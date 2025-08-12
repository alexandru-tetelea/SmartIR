from abc import ABC, abstractmethod
from base64 import b64encode
import binascii
import requests
import logging
import json
import io
import base64
import json
import sys
from bisect import bisect
from struct import pack, unpack
from math import ceil

from homeassistant.const import ATTR_ENTITY_ID
from . import Helper
_LOGGER = logging.getLogger(__name__)

BROADLINK_CONTROLLER = 'Broadlink'
XIAOMI_CONTROLLER = 'Xiaomi'
MQTT_CONTROLLER = 'MQTT'
LOOKIN_CONTROLLER = 'LOOKin'
ESPHOME_CONTROLLER = 'ESPHome'
UFOR11_CONTROLLER = 'UFOR11'

ENC_BASE64 = 'Base64'
ENC_HEX = 'Hex'
ENC_PRONTO = 'Pronto'
ENC_RAW = 'Raw'

BROADLINK_COMMANDS_ENCODING = [ENC_BASE64, ENC_HEX, ENC_PRONTO]
XIAOMI_COMMANDS_ENCODING = [ENC_PRONTO, ENC_RAW]
MQTT_COMMANDS_ENCODING = [ENC_RAW]
LOOKIN_COMMANDS_ENCODING = [ENC_PRONTO, ENC_RAW]
ESPHOME_COMMANDS_ENCODING = [ENC_RAW]
UFOR11_COMMANDS_ENCODING = [ENC_RAW]




BRDLNK_UNIT = 269 / 8192

# MAIN API
filter = lambda x: [i for i in x if i<65535]

def encode_ir(command: str) -> str:
	# command = "JgC8AXE5DioPDg0PDQ8OKw0PDg4ODw0PDSsODw0rDisNDw0sDSsOKw0rDisNDwwQDSwMEA0QDBAMEAwQDRAMLAwtDSsOKwwQDBANEAwQDBANEAwQDBAMEA0QDBAMEAwQDRAMEAwQDRAMEAwQDBANEAwQDBAMEA4PDSsODw0PDQ8ODg4PDQ8NAAPNcjgOKg8ODg4ODg8qDg4PDQ8NDw4OKg8ODioPKg4ODykPKg8pDyoPKg4ODw0PKg4ODw0PDg4ODg4PDQ8ODg4PDQ8ODg4ODg8NDw4ODg8NDw0PDg4ODw0PDg4ODg4PDQ8qDw0PDQ8ODioPKg4ODyoODg8NDw0PDg4ODw0PDg4ODg4PDQ8ODg4PDQ8ODg4OKg8ODioPDQ8ODg4PDQ8ODg4ODg8NDw4ODg8NDw0PDg4ODw0PDg4ODg4PDQ8ODg4PDQ8ODg4ODg8NDw4ODg8NDw0PDg4ODw0PDg4ODg4PDQ8ODg4PDQ8NDw4ODg8NDw4ODg4ODw0PDg4ODg4PDQ8ODg4PKg4qDw0PDg4ODg4PDg4ODg4ODg8ODg4NDw4ODg8NDw0PDg8NDw0rDisNKw4rDg4OKw0rDgANBQAAAAAAAAAAAAAAAA=="
  signal = filter(get_raw_from_broadlink(base64.b64decode(command).hex()))

  payload = b''.join(pack('<H', t) for t in signal)
  compress(out := io.BytesIO(), payload, level = 2)
  payload = out.getvalue()
  return base64.encodebytes(payload).decode('ascii').replace('\n', '')


# COMPRESSION

def emit_literal_blocks(out: io.FileIO, data: bytes):
	for i in range(0, len(data), 32):
		emit_literal_block(out, data[i:i+32])

def emit_literal_block(out: io.FileIO, data: bytes):
	length = len(data) - 1
	assert 0 <= length < (1 << 5)
	out.write(bytes([length]))
	out.write(data)

def emit_distance_block(out: io.FileIO, length: int, distance: int):
	distance -= 1
	assert 0 <= distance < (1 << 13)
	length -= 2
	assert length > 0
	block = bytearray()
	if length >= 7:
		assert length < (1 << 8)
		block.append(length - 7)
		length = 7
	block.insert(0, length << 5 | distance >> 8)
	block.append(distance & 0xFF)
	out.write(block)

def compress(out: io.FileIO, data: bytes, level=2):
	'''
	Takes a byte string and outputs a compressed "Tuya stream".
	Implemented compression levels:
	0 - copy over (no compression, 3.1% overhead)
	1 - eagerly use first length-distance pair found (linear)
	2 - eagerly use best length-distance pair found
	3 - optimal compression (n^3)
	'''
	if level == 0:
		return emit_literal_blocks(out, data)

	W = 2**13 # window size
	L = 256+9 # maximum length
	distance_candidates = lambda: range(1, min(pos, W) + 1)

	def find_length_for_distance(start: int) -> int:
		length = 0
		limit = min(L, len(data) - pos)
		while length < limit and data[pos + length] == data[start + length]:
			length += 1
		return length
	find_length_candidates = lambda: \
		( (find_length_for_distance(pos - d), d) for d in distance_candidates() )
	find_length_cheap = lambda: \
		next((c for c in find_length_candidates() if c[0] >= 3), None)
	find_length_max = lambda: \
		max(find_length_candidates(), key=lambda c: (c[0], -c[1]), default=None)

	if level >= 2:
		suffixes = []; next_pos = 0
		key = lambda n: data[n:]
		find_idx = lambda n: bisect(suffixes, key(n), key=key)
		def distance_candidates():
			nonlocal next_pos
			while next_pos <= pos:
				if len(suffixes) == W:
					suffixes.pop(find_idx(next_pos - W))
				suffixes.insert(idx := find_idx(next_pos), next_pos)
				next_pos += 1
			idxs = (idx+i for i in (+1,-1)) # try +1 first
			return (pos - suffixes[i] for i in idxs if 0 <= i < len(suffixes))

	if level <= 2:
		find_length = { 1: find_length_cheap, 2: find_length_max }[level]
		block_start = pos = 0
		while pos < len(data):
			if (c := find_length()) and c[0] >= 3:
				emit_literal_blocks(out, data[block_start:pos])
				emit_distance_block(out, c[0], c[1])
				pos += c[0]
				block_start = pos
			else:
				pos += 1
		emit_literal_blocks(out, data[block_start:pos])
		return

	# use topological sort to find shortest path
	predecessors = [(0, None, None)] + [None] * len(data)
	def put_edge(cost, length, distance):
		npos = pos + length
		cost += predecessors[pos][0]
		current = predecessors[npos]
		if not current or cost < current[0]:
			predecessors[npos] = cost, length, distance
	for pos in range(len(data)):
		if c := find_length_max():
			for l in range(3, c[0] + 1):
				put_edge(2 if l < 9 else 3, l, c[1])
		for l in range(1, min(32, len(data) - pos) + 1):
			put_edge(1 + l, l, 0)

	# reconstruct path, emit blocks
	blocks = []; pos = len(data)
	while pos > 0:
		_, length, distance = predecessors[pos]
		pos -= length
		blocks.append((pos, length, distance))
	for pos, length, distance in reversed(blocks):
		if not distance:
			emit_literal_block(out, data[pos:pos + length])
		else:
			emit_distance_block(out, length, distance)

def get_raw_from_broadlink(string):
  dec = []
  unit = BRDLNK_UNIT  # 32.84ms units, or 2^-15s
  length = int(string[6:8] + string[4:6], 16)  # Length of payload in little endian

  i = 8
  while i < length * 2 + 8:  # IR Payload
    hex_value = string[i:i+2]
    if hex_value == "00":
      hex_value = string[i+2:i+4] + string[i+4:i+6]  # Quick & dirty big-endian conversion
      i += 4
    dec.append(ceil(int(hex_value, 16) / unit))  # Will be lower than initial value due to former round()
    i += 2

  return dec

def get_controller(hass, controller, encoding, controller_data, delay):
    """Return a controller compatible with the specification provided."""
    controllers = {
        BROADLINK_CONTROLLER: BroadlinkController,
        XIAOMI_CONTROLLER: XiaomiController,
        MQTT_CONTROLLER: MQTTController,
        LOOKIN_CONTROLLER: LookinController,
        ESPHOME_CONTROLLER: ESPHomeController,
        UFOR11_CONTROLLER: UFOR11Controller
    }
    try:
        return controllers[controller](hass, controller, encoding, controller_data, delay)
    except KeyError:
        raise Exception("The controller is not supported.")


class AbstractController(ABC):
    """Representation of a controller."""
    def __init__(self, hass, controller, encoding, controller_data, delay):
        self.check_encoding(encoding)
        self.hass = hass
        self._controller = controller
        self._encoding = encoding
        self._controller_data = controller_data
        self._delay = delay

    @abstractmethod
    def check_encoding(self, encoding):
        """Check if the encoding is supported by the controller."""
        pass

    @abstractmethod
    async def send(self, command):
        """Send a command."""
        pass


class BroadlinkController(AbstractController):
    """Controls a Broadlink device."""

    def check_encoding(self, encoding):
        """Check if the encoding is supported by the controller."""
        if encoding not in BROADLINK_COMMANDS_ENCODING:
            raise Exception("The encoding is not supported "
                            "by the Broadlink controller.")

    async def send(self, command):
        """Send a command."""
        commands = []

        if not isinstance(command, list):
            command = [command]

        for _command in command:
            if self._encoding == ENC_HEX:
                try:
                    _command = binascii.unhexlify(_command)
                    _command = b64encode(_command).decode('utf-8')
                except:
                    raise Exception("Error while converting "
                                    "Hex to Base64 encoding")

            if self._encoding == ENC_PRONTO:
                try:
                    _command = _command.replace(' ', '')
                    _command = bytearray.fromhex(_command)
                    _command = Helper.pronto2lirc(_command)
                    _command = Helper.lirc2broadlink(_command)
                    _command = b64encode(_command).decode('utf-8')
                except:
                    raise Exception("Error while converting "
                                    "Pronto to Base64 encoding")

            commands.append('b64:' + _command)

        service_data = {
            ATTR_ENTITY_ID: self._controller_data,
            'command': commands,
            'delay_secs': self._delay
        }

        await self.hass.services.async_call(
            'remote', 'send_command', service_data)


class XiaomiController(AbstractController):
    """Controls a Xiaomi device."""

    def check_encoding(self, encoding):
        """Check if the encoding is supported by the controller."""
        if encoding not in XIAOMI_COMMANDS_ENCODING:
            raise Exception("The encoding is not supported "
                            "by the Xiaomi controller.")

    async def send(self, command):
        """Send a command."""
        service_data = {
            ATTR_ENTITY_ID: self._controller_data,
            'command': self._encoding.lower() + ':' + command
        }

        await self.hass.services.async_call(
            'remote', 'send_command', service_data)




class LookinController(AbstractController):
    """Controls a Lookin device."""

    def check_encoding(self, encoding):
        """Check if the encoding is supported by the controller."""
        if encoding not in LOOKIN_COMMANDS_ENCODING:
            raise Exception("The encoding is not supported "
                            "by the LOOKin controller.")

    async def send(self, command):
        """Send a command."""
        encoding = self._encoding.lower().replace('pronto', 'prontohex')
        url = f"http://{self._controller_data}/commands/ir/" \
              f"{encoding}/{command}"
        await self.hass.async_add_executor_job(requests.get, url)


class ESPHomeController(AbstractController):
    """Controls a ESPHome device."""

    def check_encoding(self, encoding):
        """Check if the encoding is supported by the controller."""
        if encoding not in ESPHOME_COMMANDS_ENCODING:
            raise Exception("The encoding is not supported "
                            "by the ESPHome controller.")

    async def send(self, command):
        """Send a command."""
        service_data = {'command': json.loads(command)}

        await self.hass.services.async_call(
            'esphome', self._controller_data, service_data)



class MQTTController(AbstractController):
    """Controls a MQTT device."""

    def check_encoding(self, encoding):
        """Check if the encoding is supported by the controller."""
        if encoding not in MQTT_COMMANDS_ENCODING:
            raise Exception("The encoding is not supported "
                            "by the mqtt controller.")

    async def send(self, command):
        """Send a command."""
        service_data = {
            'topic': self._controller_data,
            'payload': command
        }

        await self.hass.services.async_call(
            'mqtt', 'publish', service_data)

class UFOR11Controller(MQTTController):
    """Controls a UFO-R11 device."""

    def check_encoding(self, encoding):
        """Check if the encoding is supported by the controller."""
        if encoding not in UFOR11_COMMANDS_ENCODING:
            raise Exception("The encoding is not supported "
                            "by the UFO-R11 controller.")

    async def send(self, command):
        """Send a command."""
        service_data = {
            'topic': self._controller_data,
            'payload': json.dumps({"ir_code_to_send": encode_ir(command)})
        }

        await self.hass.services.async_call(
            'mqtt', 'publish', service_data)
