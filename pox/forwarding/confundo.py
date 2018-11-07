# Copyright 2012-2013 James McCauley
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at:
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
A stupid L3 switch

For each switch:
1) Keep a table that maps IP addresses to MAC addresses and switch ports.
   Stock this table using information from ARP and IP packets.
2) When you see an ARP query, try to answer it using information in the table
   from step 1.  If the info in the table is old, just flood the query.
3) Flood all other ARPs.
4) When you see an IP packet, if you know the destination port (because it's
   in the table from step 1), install a flow for it.
"""

from pox.core import core
import pox
log = core.getLogger()

from pox.lib.packet.ethernet import ethernet, ETHER_BROADCAST
from pox.lib.packet.ipv4 import ipv4
from pox.lib.packet.arp import arp
from pox.lib.addresses import IPAddr, EthAddr
from pox.lib.util import str_to_bool, dpid_to_str
from pox.lib.recoco import Timer
import pox.lib.packet as pkt
import pox.lib.packet as pkt2

import pox.openflow.libopenflow_01 as of

from pox.lib.revent import *

import time
import random
import struct

import hashlib
import binascii

magic = "f9beb4d9"

def makeMessage(magic,command,payload):
    checksum = hashlib.sha256(hashlib.sha256(payload).digest()).digest()[0:4]
    return magic.decode("hex")+struct.pack('12sI4s',command,len(payload),checksum)+payload
def makeVersionPayload(srcip, desip):
    version = 70002
    services = 0
    timestamp = int(time.time())

    addr_you = "10.0.0.1"
    services_you = 0
    port_you = 8333

    addr_me = "10.0.0.2"
    services_me = 0
    port_me = 8333	

    nonce = 0

    user_agent_bytes = 0
    start_height = 0
    relay = 1

    #https://bitcoin.org/en/developer-reference#version
    payload = "";
    payload += struct.pack("i",version)
    payload += struct.pack("Q",services)
    payload += struct.pack("q",timestamp)
    payload += struct.pack("Q",services_you)
    payload += struct.pack(">16s",addr_you)
    payload += struct.pack(">H",port_you)
    payload += struct.pack("Q",services_me)
    payload += struct.pack(">16s",addr_me)
    payload += struct.pack(">H",port_me)
    payload += struct.pack("Q",nonce)
    payload += struct.pack("B",user_agent_bytes)
    payload += struct.pack("i",start_height)
    payload += struct.pack("B",relay)
    return payload

# Timeout for flows
FLOW_IDLE_TIMEOUT = 10

# Timeout for ARP entries
ARP_TIMEOUT = 60 * 2

# Maximum number of packet to buffer on a switch for an unknown IP
MAX_BUFFERED_PER_IP = 5

# Maximum time to hang on to a buffer for an unknown IP in seconds
MAX_BUFFER_TIME = 5


class Entry (object):
  """
  Not strictly an ARP entry.
  We use the port to determine which port to forward traffic out of.
  We use the MAC to answer ARP replies.
  We use the timeout so that if an entry is older than ARP_TIMEOUT, we
   flood the ARP request rather than try to answer it ourselves.
  """
  def __init__ (self, port, mac):
    self.timeout = time.time() + ARP_TIMEOUT
    self.port = port
    self.mac = mac

  def __eq__ (self, other):
    if type(other) == tuple:
      return (self.port,self.mac)==other
    else:
      return (self.port,self.mac)==(other.port,other.mac)
  def __ne__ (self, other):
    return not self.__eq__(other)

  def isExpired (self):
    if self.port == of.OFPP_NONE: return False
    return time.time() > self.timeout


def dpid_to_mac (dpid):
  return EthAddr("%012x" % (dpid & 0xffFFffFFffFF,))

def rand_mac():
    return "%02x:%02x:%02x:%02x:%02x:%02x" % (
        random.randint(0, 255),
        random.randint(0, 255),
        random.randint(0, 255),
        random.randint(0, 255),
        random.randint(0, 255),
        random.randint(0, 255)
        )


class l3_switch (EventMixin):
  def __init__ (self, fakeways = [], arp_for_unknowns = False, wide = False):
    # These are "fake gateways" -- we'll answer ARPs for them with MAC
    # of the switch they're connected to.
    self.fakeways = set(fakeways)

    # If True, we create "wide" matches.  Otherwise, we create "narrow"
    # (exact) matches.
    self.wide = wide

    # If this is true and we see a packet for an unknown
    # host, we'll ARP for it.
    self.arp_for_unknowns = arp_for_unknowns

    # (dpid,IP) -> expire_time
    # We use this to keep from spamming ARPs
    self.outstanding_arps = {}

    # (dpid,IP) -> [(expire_time,buffer_id,in_port), ...]
    # These are buffers we've gotten at this datapath for this IP which
    # we can't deliver because we don't know where they go.
    self.lost_buffers = {}

    # For each switch, we map IP addresses to Entries
    self.arpTable = {}

    # This timer handles expiring stuff
    self._expire_timer = Timer(5, self._handle_expiration, recurring=True)

    core.listen_to_dependencies(self)

  def _handle_expiration (self):
    # Called by a timer so that we can remove old items.
    empty = []
    for k,v in self.lost_buffers.iteritems():
      dpid,ip = k

      for item in list(v):
        expires_at,buffer_id,in_port = item
        if expires_at < time.time():
          # This packet is old.  Tell this switch to drop it.
          v.remove(item)
          po = of.ofp_packet_out(buffer_id = buffer_id, in_port = in_port)
          core.openflow.sendToDPID(dpid, po)
      if len(v) == 0: empty.append(k)

    # Remove empty buffer bins
    for k in empty:
      del self.lost_buffers[k]

  def _send_lost_buffers (self, dpid, ipaddr, macaddr, port):
    """
    We may have "lost" buffers -- packets we got but didn't know
    where to send at the time.  We may know now.  Try and see.
    """
    if (dpid,ipaddr) in self.lost_buffers:
      # Yup!
      bucket = self.lost_buffers[(dpid,ipaddr)]
      del self.lost_buffers[(dpid,ipaddr)]
      log.debug("Sending %i buffered packets to %s from %s"
                % (len(bucket),ipaddr,dpid_to_str(dpid)))
      for _,buffer_id,in_port in bucket:
        po = of.ofp_packet_out(buffer_id=buffer_id,in_port=in_port)
        po.actions.append(of.ofp_action_dl_addr.set_dst(macaddr))
        po.actions.append(of.ofp_action_output(port = port))
        core.openflow.sendToDPID(dpid, po)

  def _handle_openflow_PacketIn (self, event):
    dpid = event.connection.dpid
    inport = event.port
    packet = event.parsed
    if not packet.parsed:
      log.warning("%i %i ignoring unparsed packet", dpid, inport)
      return

    if dpid not in self.arpTable:
      # New switch -- create an empty table
      self.arpTable[dpid] = {}
      for fake in self.fakeways:
        self.arpTable[dpid][IPAddr(fake)] = Entry(of.OFPP_NONE,
         dpid_to_mac(dpid))

    if packet.type == ethernet.LLDP_TYPE:
      # Ignore LLDP packets
      return

    if isinstance(packet.next, ipv4):
      log.debug("%i %i IP %s => %s", dpid,inport,
                packet.next.srcip,packet.next.dstip)
      

      # Send any waiting packets...
      self._send_lost_buffers(dpid, packet.next.srcip, packet.src, inport)

      # Learn or update port/MAC info
      if packet.next.srcip in self.arpTable[dpid]:
        if self.arpTable[dpid][packet.next.srcip] != (inport, packet.src):
          log.info("%i %i RE-learned %s", dpid,inport,packet.next.srcip)
          if self.wide:
            # Make sure we don't have any entries with the old info...
            msg = of.ofp_flow_mod(command=of.OFPFC_DELETE)
            msg.match.nw_dst = packet.next.srcip
            msg.match.dl_type = ethernet.IP_TYPE
            event.connection.send(msg)
      else:
        log.debug("%i %i learned %s", dpid,inport,packet.next.srcip)
      self.arpTable[dpid][packet.next.srcip] = Entry(inport, packet.src)

      # Try to forward
      dstaddr = packet.next.dstip
      if dstaddr not in self.arpTable[dpid]:
        if packet.next.srcip == IPAddr("10.0.0.1"):
          self.arpTable[dpid][packet.next.dstip] = Entry(inport, packet.src)
          self.arpTable[dpid][packet.next.dstip].mac = EthAddr("32:d5:a3:be:19:77")
      
      if packet.next.protocol == ipv4.ICMP_PROTOCOL:
        e = pkt.ethernet()
        e.src = self.arpTable[dpid][dstaddr].mac
        e.dst = EthAddr(packet.src)
        e.type = e.IP_TYPE
        ipp = pkt.ipv4()
        ipp.protocol = ipp.ICMP_PROTOCOL
        ipp.srcip = packet.next.dstip
        print(ipp.srcip)
        ipp.dstip = packet.next.srcip
        icmp = pkt.icmp()
        icmp.type = pkt.ICMP.TYPE_ECHO_REPLY
        icmp.payload = packet.next.payload.payload #copy the ping payload of the packet that they receive 
        ipp.payload = icmp
        e.payload = ipp
        msg = of.ofp_packet_out()
        msg.data = e.pack()
        msg.actions.append(of.ofp_action_output(port =
                                                of.OFPP_IN_PORT))
        msg.in_port = inport
        event.connection.send(msg)
        return

      if packet.next.protocol == ipv4.TCP_PROTOCOL:
        
        if packet.next.payload.SYN and not packet.next.payload.ACK: #this is to send SYN, ACK
          print "SYN packet", packet.next.payload
          e = pkt.ethernet()
          e.src = self.arpTable[dpid][dstaddr].mac
          e.dst = EthAddr(packet.src)
          e.type = e.IP_TYPE
          tcpp = pkt.tcp()
          tcpp.srcport = packet.next.payload.dstport   #packet.next.payload = tcpp, packet.next = ip, packet = E
          tcpp.dstport = packet.next.payload.srcport
          tcpp.seq = 0 #random.randint(0, 10000) # will be random
          tcpp.ack = packet.next.payload.seq+1
          tcpp.win = 29200
          tcpp.SYN = True  #send SYN
          tcpp.ACK = True  #send ACK

          tcp = pkt.ipv4()
          tcp.protocol = tcp.TCP_PROTOCOL
          tcp.srcip = packet.next.dstip
          tcp.dstip = packet.next.srcip
          tcp.payload = tcpp

          e.payload = tcp
          msg = of.ofp_packet_out()
          msg.data = e.pack()
          msg.actions.append(of.ofp_action_output(port =
                                                  of.OFPP_IN_PORT))
          msg.in_port = inport
          event.connection.send(msg)

          time.sleep(0.15)

      	  e = pkt2.ethernet()
          e.src = self.arpTable[dpid][dstaddr].mac
          e.dst = EthAddr(packet.src)
          e.type = e.IP_TYPE
          tcpp = pkt2.tcp()
          tcpp.srcport = packet.next.payload.dstport
          tcpp.dstport = packet.next.payload.srcport
          #print(packet.next.payload.ack)
          tcpp.seq = 1
          tcpp.ack = packet.next.payload.seq+127
          tcpp.win = 29200
          tcpp.PSH = True  #send PSH
          tcpp.ACK = True  #send ACK
          tcpp.payload = makeMessage(magic,"version",makeVersionPayload(str(packet.next.dstip), str(packet.next.srcip)))
        
          tcp = pkt2.ipv4()
          tcp.protocol = tcp.TCP_PROTOCOL
          tcp.srcip = packet.next.dstip
          tcp.dstip = packet.next.srcip 
          tcp.payload = tcpp
          e.payload = tcp
          
          

          #msg = makeMessage(magic,"version",makeVersionPayload())
		      #print "sending version packet"
		      #sock.send(msg)
		      #time.sleep(1)
		      #msg2 = makeMessage(magic,"verack","") #How the Verack msg was created by the ATTR
		      #sock.send(msg2)

          print "*****"
          msg = of.ofp_packet_out()
          msg.data = e.pack() 
          msg.actions.append(of.ofp_action_output(port =
                                              of.OFPP_IN_PORT))
          msg.in_port = inport
          event.connection.send(msg)
          return

        




        # if not packet.next.payload.SYN and packet.next.payload.ACK:
        #   print "ACK packet", packet.next.payload
        #   e = pkt.ethernet()
        #   e.src = self.arpTable[dpid][dstaddr].mac
        #   e.dst = EthAddr(packet.src)
        #   e.type = e.IP_TYPE
        #   tcpp = pkt.tcp()
        #   tcpp.srcport = packet.next.payload.dstport
        #   tcpp.dstport = packet.next.payload.srcport
        #   # tcpp.seq = 1 # will be random
        #   tcpp.ack = packet.next.payload.ack+1
        #   # tcpp.SYN = True
        #   tcpp.ACK = True
          
        #   tcp = pkt.ipv4()
        #   tcp.protocol = tcp.TCP_PROTOCOL
        #   tcp.srcip = packet.next.dstip
        #   tcp.dstip = packet.next.srcip
        #   tcp.payload = tcpp

        #   e.payload = tcp
        #   msg = of.ofp_packet_out()
        #   msg.data = e.pack()
        #   msg.actions.append(of.ofp_action_output(port =
        #                                           of.OFPP_IN_PORT))
        #   msg.in_port = inport
        #   event.connection.send(msg)
        #   return
        else:
          print "Not SYN", packet.next.payload
      elif self.arp_for_unknowns:
        # We don't know this destination.
        # First, we track this buffer so that we can try to resend it later
        # if we learn the destination, second we ARP for the destination,
        # which should ultimately result in it responding and us learning
        # where it is

        # Add to tracked buffers
        if (dpid,dstaddr) not in self.lost_buffers:
          self.lost_buffers[(dpid,dstaddr)] = []
        bucket = self.lost_buffers[(dpid,dstaddr)]
        entry = (time.time() + MAX_BUFFER_TIME,event.ofp.buffer_id,inport)
        bucket.append(entry)
        while len(bucket) > MAX_BUFFERED_PER_IP: del bucket[0]

        # Expire things from our outstanding ARP list...
        self.outstanding_arps = {k:v for k,v in
         self.outstanding_arps.iteritems() if v > time.time()}

        # Check if we've already ARPed recently
        if (dpid,dstaddr) in self.outstanding_arps:
          # Oop, we've already done this one recently.
          return

        # And ARP...
        self.outstanding_arps[(dpid,dstaddr)] = time.time() + 4

        r = arp()
        r.hwtype = r.HW_TYPE_ETHERNET
        r.prototype = r.PROTO_TYPE_IP
        r.hwlen = 6
        r.protolen = r.protolen
        r.opcode = r.REQUEST
        r.hwdst = ETHER_BROADCAST
        r.protodst = dstaddr
        r.hwsrc = packet.src
        r.protosrc = packet.next.srcip
        e = ethernet(type=ethernet.ARP_TYPE, src=packet.src,
                     dst=ETHER_BROADCAST)
        e.set_payload(r)
        log.debug("%i %i ARPing for %s on behalf of %s" % (dpid, inport,
         r.protodst, r.protosrc))
        msg = of.ofp_packet_out()
        msg.data = e.pack()
        msg.actions.append(of.ofp_action_output(port = of.OFPP_FLOOD))
        msg.in_port = inport
        event.connection.send(msg)

    elif isinstance(packet.next, arp):
      a = packet.next
      log.debug("%i %i ARP %s %s => %s", dpid, inport,
       {arp.REQUEST:"request",arp.REPLY:"reply"}.get(a.opcode,
       'op:%i' % (a.opcode,)), a.protosrc, a.protodst)

      
      if a.protosrc == IPAddr("10.0.0.1"):
        if a.opcode == arp.REQUEST:

          if a.protodst not in self.arpTable[dpid]:
            self.arpTable[dpid][a.protodst] = Entry(inport, packet.src)
            self.arpTable[dpid][a.protodst].mac = EthAddr("32:d5:a3:be:19:77")

          r = arp()
          r.hwtype = a.hwtype
          r.prototype = a.prototype
          r.hwlen = a.hwlen
          r.protolen = a.protolen
          r.opcode = arp.REPLY
          r.hwdst = a.hwsrc
          r.protodst = a.protosrc
          r.protosrc = a.protodst
          r.hwsrc = self.arpTable[dpid][a.protodst].mac
          e = ethernet(type=packet.type, src=dpid_to_mac(dpid),
                       dst=a.hwsrc)
          e.set_payload(r)
          log.debug("%i %i answering ARP for %s: %s" % (dpid, inport,
           r.protosrc, r.hwsrc))
          msg = of.ofp_packet_out()
          msg.data = e.pack()
          msg.actions.append(of.ofp_action_output(port =
                                                  of.OFPP_IN_PORT))
          msg.in_port = inport
          event.connection.send(msg)
          return

      # Didn't know how to answer or otherwise handle this ARP, so just flood it
      log.debug("%i %i flooding ARP %s %s => %s" % (dpid, inport,
       {arp.REQUEST:"request",arp.REPLY:"reply"}.get(a.opcode,
       'op:%i' % (a.opcode,)), a.protosrc, a.protodst))

      msg = of.ofp_packet_out(in_port = inport, data = event.ofp,
          action = of.ofp_action_output(port = of.OFPP_FLOOD))
      event.connection.send(msg)


def launch (fakeways="", arp_for_unknowns=None, wide=False):
  fakeways = fakeways.replace(","," ").split()
  fakeways = [IPAddr(x) for x in fakeways]
  if arp_for_unknowns is None:
    arp_for_unknowns = len(fakeways) > 0
  else:
    arp_for_unknowns = str_to_bool(arp_for_unknowns)
  core.registerNew(l3_switch, fakeways, arp_for_unknowns, wide)

