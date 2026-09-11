#THIS TOOL MOD BY - @TrnDravix
#TELEGRAM SEARCH - @TrnDravix
#TELEGRAM CHANNEL - TrnDravix BGMI
#OWNER / MODER -TrnDravix TrnDravix

#One_Of_The_Best_Tool_In_Whole_Telegram - 100% WORKING FINAL

import itertools as it
import math
import struct
import shutil
import os
import sys
import uuid
import hashlib
import platform
import subprocess
import requests
import base64
import zlib
from dataclasses import dataclass
from functools import lru_cache
from pathlib import PurePath, Path
from typing import List, Dict, Tuple, Optional, Any
import time
from rich.console import Console
from rich.panel import Panel
from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn, TaskProgressColumn, TimeElapsedColumn, TimeRemainingColumn
from rich.table import Table
from rich import print as rprint
from rich.markup import escape
from rich.text import Text
from rich.align import Align
from rich.console import Group
from rich.box import HEAVY_EDGE, ROUNDED, DOUBLE_EDGE
from datetime import datetime
import pytz
import re
import zipfile
import json

# ==================== COMPAT: batched polyfill ====================

def _batched(iterable, n):
    it_obj = iter(iterable)
    while True:
        batch = list(it.islice(it_obj, n))
        if not batch:
            break
        yield batch

# ==================== VENDORED ZUC CIPHER (gmalg fallback) ====================

_ZUC_S0 = bytes([
    0x3e,0x72,0x5b,0x47,0xca,0xe0,0x00,0x33,0x04,0xd1,0x54,0x98,0x09,0xb9,0x6d,0xcb,
    0x7b,0x1b,0xf9,0x32,0xaf,0x9d,0x6a,0xa5,0xb8,0x2d,0xfc,0x1d,0x08,0x53,0x03,0x90,
    0x4d,0x4e,0x84,0x99,0xe4,0xce,0xd9,0x91,0xdd,0xb6,0x85,0x48,0x8b,0x29,0x6e,0xac,
    0xcd,0xc1,0xf8,0x1e,0x73,0x43,0x69,0xc6,0xb5,0xbd,0xfd,0x39,0x63,0x20,0xd4,0x38,
    0x76,0x7d,0xb2,0xa7,0xcf,0xed,0x57,0xc5,0xf3,0x2c,0xbb,0x14,0x21,0x06,0x55,0x9b,
    0xe3,0xef,0x5e,0x31,0x4f,0x7f,0x5a,0xa4,0x0d,0x82,0x51,0x49,0x5f,0xba,0x58,0x1c,
    0x4a,0x16,0xd5,0x17,0xa8,0x92,0x24,0x1f,0x8c,0xff,0xd8,0xae,0x2e,0x01,0xd3,0xad,
    0x3b,0x4b,0xda,0x46,0xeb,0xc9,0xde,0x9a,0x8f,0x87,0xd7,0x3a,0x80,0x6f,0x2f,0xc8,
    0xb1,0xb4,0x37,0xf7,0x0a,0x22,0x13,0x28,0x7c,0xcc,0x3c,0x89,0xc7,0xc3,0x96,0x56,
    0x07,0xbf,0x7e,0xf0,0x0b,0x2b,0x97,0x52,0x35,0x41,0x79,0x61,0xa6,0x4c,0x10,0xfe,
    0xbc,0x26,0x95,0x88,0x8a,0xb0,0xa3,0xfb,0xc0,0x18,0x94,0xf2,0xe1,0xe5,0xe9,0x5d,
    0xd0,0xdc,0x11,0x66,0x64,0x5c,0xec,0x59,0x42,0x75,0x12,0xf5,0x74,0x9c,0xaa,0x23,
    0x0e,0x86,0xab,0xbe,0x2a,0x02,0xe7,0x67,0xe6,0x44,0xa2,0x6c,0xc2,0x93,0x9f,0xf1,
    0xf6,0xfa,0x36,0xd2,0x50,0x68,0x9e,0x62,0x71,0x15,0x3d,0xd6,0x40,0xc4,0xe2,0x0f,
    0x8e,0x83,0x77,0x6b,0x25,0x05,0x3f,0x0c,0x30,0xea,0x70,0xb7,0xa1,0xe8,0xa9,0x65,
    0x8d,0x27,0x1a,0xdb,0x81,0xb3,0xa0,0xf4,0x45,0x7a,0x19,0xdf,0xee,0x78,0x34,0x60
])
_ZUC_S1 = bytes([
    0x55,0xc2,0x63,0x71,0x3b,0xc8,0x47,0x86,0x9f,0x3c,0xda,0x5b,0x29,0xaa,0xfd,0x77,
    0x8c,0xc5,0x94,0x0c,0xa6,0x1a,0x13,0x00,0xe3,0xa8,0x16,0x72,0x40,0xf9,0xf8,0x42,
    0x44,0x26,0x68,0x96,0x81,0xd9,0x45,0x3e,0x10,0x76,0xc6,0xa7,0x8b,0x39,0x43,0xe1,
    0x3a,0xb5,0x56,0x2a,0xc0,0x6d,0xb3,0x05,0x22,0x66,0xbf,0xdc,0x0b,0xfa,0x62,0x48,
    0xdd,0x20,0x11,0x06,0x36,0xc9,0xc1,0xcf,0xf6,0x27,0x52,0xbb,0x69,0xf5,0xd4,0x87,
    0x7f,0x84,0x4c,0xd2,0x9c,0x57,0xa4,0xbc,0x4f,0x9a,0xdf,0xfe,0xd6,0x8d,0x7a,0xeb,
    0x2b,0x53,0xd8,0x5c,0xa1,0x14,0x17,0xfb,0x23,0xd5,0x7d,0x30,0x67,0x73,0x08,0x09,
    0xee,0xb7,0x70,0x3f,0x61,0xb2,0x19,0x8e,0x4e,0xe5,0x4b,0x93,0x8f,0x5d,0xdb,0xa9,
    0xad,0xf1,0xae,0x2e,0xcb,0x0d,0xfc,0xf4,0x2d,0x46,0x6e,0x1d,0x97,0xe8,0xd1,0xe9,
    0x4d,0x37,0xa5,0x75,0x5e,0x83,0x9e,0xab,0x82,0x9d,0xb9,0x1c,0xe0,0xcd,0x49,0x89,
    0x01,0xb6,0xbd,0x58,0x24,0xa2,0x5f,0x38,0x78,0x99,0x15,0x90,0x50,0xb8,0x95,0xe4,
    0xd0,0x91,0xc7,0xce,0xed,0x0f,0xb4,0x6f,0xa0,0xcc,0xf0,0x02,0x4a,0x79,0xc3,0xde,
    0xa3,0xef,0xea,0x51,0xe6,0x6b,0x18,0xec,0x1b,0x2c,0x80,0xf7,0x74,0xe7,0xff,0x21,
    0x5a,0x6a,0x54,0x1e,0x41,0x31,0x92,0x35,0xc4,0x33,0x07,0x0a,0xba,0x7e,0x0e,0x34,
    0x88,0xb1,0x98,0x7c,0xf3,0x3d,0x60,0x6c,0x7b,0xca,0xd3,0x1f,0x32,0x65,0x04,0x28,
    0x64,0xbe,0x85,0x9b,0x2f,0x59,0x8a,0xd7,0xb0,0x25,0xac,0xaf,0x12,0x03,0xe2,0xf2
])
_ZUC_D = [0b100010011010111,0b010011010111100,0b110001001101011,0b001001101011110,
    0b101011110001001,0b011010111100010,0b111000100110101,0b000100110101111,
    0b100110101111000,0b010111100010011,0b110101111000100,0b001101011110001,
    0b101111000100110,0b011110001001101,0b111100010011010,0b100011110101100]
_ZUC_MOD = 0x7fffffff
def _zuc_rol32(x,n): return ((x<<n)&0xffffffff)|(x>>(32-n))
def _zuc_bs(x):
    return (_ZUC_S0[(x>>24)&0xff]<<24)^(_ZUC_S1[(x>>16)&0xff]<<16)^(_ZUC_S0[(x>>8)&0xff]<<8)^(_ZUC_S1[x&0xff])
def _zuc_l1(x): return x^_zuc_rol32(x,2)^_zuc_rol32(x,10)^_zuc_rol32(x,18)^_zuc_rol32(x,24)
def _zuc_l2(x): return x^_zuc_rol32(x,8)^_zuc_rol32(x,14)^_zuc_rol32(x,22)^_zuc_rol32(x,30)
class _FallbackZUC:
    def __init__(self,key,iv):
        self._lfsr=[0]*16;self._r1=0;self._r2=0;S=self._lfsr
        for i in range(16): S[i]=(key[i]<<23)|(_ZUC_D[i]<<8)|iv[i]
        for _ in range(32):
            x0=(S[15]>>15<<16)|(S[14]&0xffff);x1=((S[11]&0xffff)<<16)|(S[9]>>15);x2=((S[7]&0xffff)<<16)|(S[5]>>15)
            self._lfsr_work(self._f(x0,x1,x2)>>1)
        self.generate()
    def _f(self,x0,x1,x2):
        r1,r2=self._r1,self._r2;w=((x0^r1)+r2)&0xffffffff;w1=(r1+x1)&0xffffffff;w2=r2^x2
        self._r1=_zuc_bs(_zuc_l1(((w1&0xffff)<<16)^(w2>>16)));self._r2=_zuc_bs(_zuc_l2(((w2&0xffff)<<16)^(w1>>16)));return w
    def _lfsr_work(self,u=0):
        S=self._lfsr;s16=((S[15]<<15)+(S[13]<<17)+(S[10]<<21)+(S[4]<<20)+(S[0]<<8)+S[0]+u)%_ZUC_MOD
        S.append(_ZUC_MOD if s16==0 else s16);S.pop(0)
    def generate(self):
        S=self._lfsr;x0=(S[15]>>15<<16)|(S[14]&0xffff);x1=((S[11]&0xffff)<<16)|(S[9]>>15)
        x2=((S[7]&0xffff)<<16)|(S[5]>>15);x3=((S[2]&0xffff)<<16)|(S[0]>>15)
        z=self._f(x0,x1,x2)^x3;self._lfsr_work();return z.to_bytes(4,'big')
_tz=_FallbackZUC(bytes.fromhex('3d4c4be96a82fdaeb58f641db17b455b'),bytes.fromhex('84319aa8de6915ca1f6bda6bfbd8c766'))
assert _tz.generate()==bytes.fromhex('14f1c272'),"ZUC fallback self-test FAILED"
try:
    import gmalg as _gmalg_mod
    _ZUC_CLASS = _gmalg_mod.ZUC
except ImportError:
    _ZUC_CLASS = _FallbackZUC
from Crypto.Cipher import AES
from Crypto.Cipher.AES import MODE_CBC
from Crypto.Hash import SHA1
from Crypto.Util.Padding import unpad
from zstandard import ZstdDecompressor, ZstdCompressionDict, DICT_TYPE_AUTO, ZstdCompressor

console = Console()

# ==================== SIMPLE BLOCK DISPLAY CLASS ====================

class SimpleBlockDisplay:
    """Simple display that shows each file and its blocks"""
    
    def __init__(self, total_files: int, pak_name: str):
        self.total_files = total_files
        self.pak_name = pak_name
        self.processed_files = 0
        self.current_file = ""
        self.current_file_idx = 0
        self.all_blocks = []  # Store all blocks for final summary
        self.total_fitted = 0
        self.total_skipped = 0
        
    def start_file(self, file_name: str, total_blocks: int):
        self.current_file_idx += 1
        self.current_file = file_name
        self.current_blocks = []
        self.current_total_blocks = total_blocks
        self.current_fitted = 0
        self.current_skipped = 0
        
        # Print file header
        console.print()
        console.print(f"[bold cyan]┌─────────────────────────────────────────────────────────────[/bold cyan]")
        console.print(f"[bold cyan]│[/] [bold yellow][{self.current_file_idx}/{self.total_files}][/] [bold green]{file_name}[/bold green] [dim]({total_blocks} blocks)[/dim]")
        console.print(f"[bold cyan]├─────────────────────────────────────────────────────────────[/bold cyan]")
        
    def add_block(self, block_idx: int, block_size: int, fitted: bool, compression_ratio: float = None):
        """Add a block result"""
        size_mb = block_size / (1024 * 1024)
        if fitted:
            self.current_fitted += 1
            self.total_fitted += 1
            ratio_str = f" [{compression_ratio:.1%}]" if compression_ratio else ""
            status = f"[green]✓ FITTED{ratio_str}[/green]"
        else:
            self.current_skipped += 1
            self.total_skipped += 1
            status = f"[red]✗ SKIPPED[/red]"
        
        console.print(f"[bold cyan]│[/]    Block {block_idx:3d}: {size_mb:>7.2f} MB  →  {status}")
        self.current_blocks.append({'fitted': fitted})
        
    def finish_file(self):
        """Finish current file"""
        total_blocks = len(self.current_blocks)
        
        if total_blocks > 0:
            if self.current_fitted == total_blocks:
                status = "[green]✓ ALL FITTED[/green]"
            elif self.current_fitted > 0:
                status = f"[yellow]✓ {self.current_fitted}/{total_blocks} FITTED[/yellow]"
            else:
                status = "[red]✗ ALL SKIPPED[/red]"
        else:
            status = "[green]✓ DONE[/green]"
        
        console.print(f"[bold cyan]└─────────────────────────────────────────────────────────────[/bold cyan]")
        console.print(f"  [dim]Result: {status}[/dim]")
        
        self.processed_files += 1
        self.all_blocks.extend(self.current_blocks)
        
    def final_summary(self):
        """Print final summary"""
        total_blocks = len(self.all_blocks)
        
        console.print()
        console.print(f"[bold green]╔═════════════════════════════════════════════════════════════════╗[/bold green]")
        console.print(f"[bold green]║[/] [bold yellow]REPACK SUMMARY[/bold yellow]")
        console.print(f"[bold green]║[/]")
        console.print(f"[bold green]║[/]   Total Files:   [bold cyan]{self.processed_files}[/bold cyan]")
        console.print(f"[bold green]║[/]   Total Blocks:  [bold cyan]{total_blocks}[/bold cyan]")
        console.print(f"[bold green]║[/]   Fitted Blocks: [bold green]{self.total_fitted}[/bold green]")
        console.print(f"[bold green]║[/]   Skipped Blocks:[bold red]{self.total_skipped}[/bold red]")
        if total_blocks > 0:
            success_rate = (self.total_fitted / total_blocks) * 100
            console.print(f"[bold green]║[/]   Success Rate:  [bold yellow]{success_rate:.1f}%[/bold yellow]")
        console.print(f"[bold green]╚═════════════════════════════════════════════════════════════════╝[/bold green]")

# ==================== ORIGINAL CLASSES (UNCHANGED) ====================

ZUC_KEY = bytes.fromhex('01010101010101010101010101010101')
ZUC_IV = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF')

RSA_MOD_1 = bytes.fromhex('CBE8B9F2504050EF9831B719E9A6249A6D238505ADE909BDE78C180DED6072A0C3347B8AF4780E1F212D952D82D4BF7F233C1ECA499E1F9D9A85B4FAD759F54BABC1666C5DE411EA9E4B2374425DD6C6F54333BBC8F2610FE6063E4D0D6C21A671A8F7C3740555E5DC06D4E1691C456DB4116C0C012BF7B206E8311AAAEC689952BF804EF638F09D5822B4117B114208F14DEB459E80CB770E5B0D7978E21F5E6CED4999D3583108221A7AB28B960277ADB5690A332784019D9C195BE4EA9EA0A09459010F236465DE0D59C3EF7324E954E1118D93EE19F299760C2CDB963CE87973EA5ECC9BBE81C27D4C7C8572AC07E9BCEAC9BD72AB7A56A3C0AD736ABCE4')
RSA_MOD_2 = bytes.fromhex('7F58E8A39A4DA4E87357DDD650EAA16D3B5CE95B213D1030A662566444796A78A84AE9AC3DBFFDE7F41094896696835DAF13B89E6EC2B84963B1B1BAF7151DA245C3FBFAE2A6AE18B2684D03F9229DE2C91440F2A3A3BCDE1E5680C16722A88039C73560D5D43F4B6562C2EEA5B1D926D86B51108A2643C70FB74D6442CE3A08339B8FD8F660AE88129B7AB8C46F2FA58124485CCCB1E987B05A6DA65A01858ED3F89905449AE42BB07290FCB9994BF22E26610BCABB9804783A3B9587917F3D97316EDDA15C5E13F79066407B55A93B291B68A4AC42A98D6E35FED84B14A792D154E62028DDAD20FC301951E5924BE9AD62FB719DD94CC30CAB871BEC4377A8')

SIMPLE1_DECRYPT_KEY = 121
SIMPLE2_DECRYPT_KEY = bytes.fromhex('E55B4ED1')
SIMPLE2_BLOCK_SIZE = 16

SM4_SECRET_4 = 'eb691efea914241317a8'
SM4_SECRET_2 = 'Q0hVTKey$as*1ZFlQCiA'
SM4_SECRET_NEW = [
    'xG2qW5lP7lV2iN5fN5pG',
    'xT1cJ6dL5wC0kK1rB4dK',
    'qC4jS5bZ6fL5xE6nD4zA',
    'gD4jQ2aL3bS3lC3xT0iW',
    'xU1yQ8wE9zY3gZ3bT5aE',
    'uQ3cO2dX7xY4xU7gH7iS',
    'gW1fR0jK6wQ4oN0oK1kZ',
    'aJ4pV7iZ7pU4wP2aC2cZ',
    'cX6jT3cM2oT3vK0kJ1qN',
    'iT2vS0cS6yT6cZ1sE1lO',
    'hM1pH9iY8wM9hT4lN5uJ',
    'kG6bC8jK0fL0dE4sH4mL',
    'dB6lB3vE0eZ8wM8rI0aC',
    'tP7sP7nI9rA2vQ4cV5yQ',
    'aT0cL1yN4pT3sZ7eM2vY',
    'uV6fU8fC9zN3mP5dH8mN'
]

EM_SIMPLE1 = 1
EM_SIMPLE2 = 16
EM_SM4_2 = 2
EM_SM4_4 = 4
EM_SM4_NEW_BASE = 31
EM_SM4_NEW_MASK = ~EM_SM4_NEW_BASE
EM_UNKNOWN_17 = 17

CM_NONE = 0
CM_ZLIB = 1
CM_ZSTD = 6
CM_ZSTD_DICT = 8
CM_MASK = 15

class SM4:
    _S_BOX = bytes([
        52, 102, 37, 116, 137, 120, 228, 169, 90, 65, 188, 122, 214, 22, 33, 35,
        77, 97, 218, 148, 155, 223, 19, 60, 105, 58, 49, 10, 95, 215, 153, 149,
        241, 174, 114, 61, 7, 96, 36, 182, 152, 238, 196, 162, 45, 136, 221, 141,
        4, 234, 187, 17, 202, 62, 93, 161, 246, 63, 176, 151, 128, 71, 43, 166,
        230, 247, 217, 177, 89, 192, 124, 190, 84, 40, 183, 126, 79, 248, 67, 110,
        160, 80, 14, 245, 144, 184, 251, 163, 123, 98, 25, 70, 3, 42, 185, 143,
        159, 119, 180, 91, 131, 135, 8, 235, 226, 30, 66, 240, 15, 232, 113, 106,
        117, 173, 85, 31, 181, 171, 51, 250, 127, 21, 189, 133, 216, 6, 104, 179,
        82, 48, 72, 11, 0, 237, 239, 178, 87, 142, 231, 108, 213, 229, 46, 83,
        130, 5, 249, 129, 244, 86, 191, 140, 75, 227, 219, 74, 145, 76, 44, 211,
        64, 41, 78, 32, 20, 54, 121, 9, 111, 209, 55, 224, 57, 12, 138, 146,
        56, 18, 53, 109, 225, 253, 147, 154, 23, 212, 201, 156, 107, 132, 38, 157,
        175, 118, 193, 158, 208, 150, 197, 203, 233, 115, 73, 210, 205, 100, 195, 199,
        1, 125, 243, 172, 252, 222, 164, 68, 50, 27, 194, 186, 28, 2, 198, 39,
        69, 139, 242, 24, 167, 16, 81, 29, 200, 207, 99, 255, 47, 13, 88, 206,
        101, 165, 220, 26, 59, 134, 254, 34, 92, 168, 94, 103, 170, 236, 112, 204
    ])
    _FK = [1184304796, 1270900830, 1493524870, 3164752158]
    _CK = [964907, 973793155, 2654690407, 2916866751, 2071233739, 1226140771, 3348805095, 2045549823, 388349611, 800627875, 612403927, 3721562911, 1195432523, 3150178931, 612053223, 2445162591, 67183755, 1174197155, 1393249511, 3331183455, 3822152747, 1332317203, 1804781383, 1990130463, 1282653851, 3376591251, 2910902311, 925872959, 332098219, 735840931, 396665415, 3588844719]
    
    @staticmethod
    def ROL32(x, n):
        return (x << n) & 0xFFFFFFFF | (x >> (32 - n))
    
    @staticmethod
    def _BS(X):
        return (SM4._S_BOX[X >> 24 & 255] << 24 | 
                SM4._S_BOX[X >> 16 & 255] << 16 | 
                SM4._S_BOX[X >> 8 & 255] << 8 | 
                SM4._S_BOX[X & 255])
    
    @staticmethod
    def _T0(X):
        X = SM4._BS(X)
        return X ^ SM4.ROL32(X, 2) ^ SM4.ROL32(X, 10) ^ SM4.ROL32(X, 18) ^ SM4.ROL32(X, 24)
    
    @staticmethod
    def _T1(X):
        X = SM4._BS(X)
        return X ^ SM4.ROL32(X, 13) ^ SM4.ROL32(X, 23)
    
    @staticmethod
    def _key_expand(key: bytes, rkey: list):
        K0 = int.from_bytes(key[0:4], 'big') ^ SM4._FK[0]
        K1 = int.from_bytes(key[4:8], 'big') ^ SM4._FK[1]
        K2 = int.from_bytes(key[8:12], 'big') ^ SM4._FK[2]
        K3 = int.from_bytes(key[12:16], 'big') ^ SM4._FK[3]
        for i in range(0, 32, 4):
            K0 = K0 ^ SM4._T1(K1 ^ K2 ^ K3 ^ SM4._CK[i])
            rkey[i] = K0
            K1 = K1 ^ SM4._T1(K2 ^ K3 ^ K0 ^ SM4._CK[i + 1])
            rkey[i + 1] = K1
            K2 = K2 ^ SM4._T1(K3 ^ K0 ^ K1 ^ SM4._CK[i + 2])
            rkey[i + 2] = K2
            K3 = K3 ^ SM4._T1(K0 ^ K1 ^ K2 ^ SM4._CK[i + 3])
            rkey[i + 3] = K3
    
    @classmethod
    def key_length(cls):
        return 16
    
    @classmethod
    def block_length(cls):
        return 16
    
    def __init__(self, key: bytes):
        if len(key) != self.key_length():
            raise ValueError(f'Key must be {self.key_length()} bytes')
        else:
            self._key = key
            self._rkey = [0] * 32
            SM4._key_expand(self._key, self._rkey)
            self._block_buffer = bytearray()
    
    def encrypt(self, block: bytes) -> bytes:
        if len(block) != self.block_length():
            raise ValueError(f'Block must be {self.block_length()} bytes')
        else:
            RK = self._rkey
            X0 = int.from_bytes(block[0:4], 'big')
            X1 = int.from_bytes(block[4:8], 'big')
            X2 = int.from_bytes(block[8:12], 'big')
            X3 = int.from_bytes(block[12:16], 'big')
            for i in range(0, 32, 4):
                X0 = X0 ^ SM4._T0(X1 ^ X2 ^ X3 ^ RK[i])
                X1 = X1 ^ SM4._T0(X2 ^ X3 ^ X0 ^ RK[i + 1])
                X2 = X2 ^ SM4._T0(X3 ^ X0 ^ X1 ^ RK[i + 2])
                X3 = X3 ^ SM4._T0(X0 ^ X1 ^ X2 ^ RK[i + 3])
            BUFFER = self._block_buffer
            BUFFER.clear()
            BUFFER.extend(X3.to_bytes(4, 'big'))
            BUFFER.extend(X2.to_bytes(4, 'big'))
            BUFFER.extend(X1.to_bytes(4, 'big'))
            BUFFER.extend(X0.to_bytes(4, 'big'))
            return bytes(BUFFER)
    
    def decrypt(self, block: bytes) -> bytes:
        if len(block) != self.block_length():
            raise ValueError(f'Block must be {self.block_length()} bytes')
        else:
            RK = self._rkey
            X0 = int.from_bytes(block[0:4], 'big')
            X1 = int.from_bytes(block[4:8], 'big')
            X2 = int.from_bytes(block[8:12], 'big')
            X3 = int.from_bytes(block[12:16], 'big')
            for i in range(0, 32, 4):
                X0 = X0 ^ SM4._T0(X1 ^ X2 ^ X3 ^ RK[31 - i])
                X1 = X1 ^ SM4._T0(X2 ^ X3 ^ X0 ^ RK[30 - i])
                X2 = X2 ^ SM4._T0(X3 ^ X0 ^ X1 ^ RK[29 - i])
                X3 = X3 ^ SM4._T0(X0 ^ X1 ^ X2 ^ RK[28 - i])
            BUFFER = self._block_buffer
            BUFFER.clear()
            BUFFER.extend(X3.to_bytes(4, 'big'))
            BUFFER.extend(X2.to_bytes(4, 'big'))
            BUFFER.extend(X1.to_bytes(4, 'big'))
            BUFFER.extend(X0.to_bytes(4, 'big'))
            return bytes(BUFFER)

class Misc:
    @staticmethod
    def pad_to_n(data: bytes, n: int) -> bytes:
        assert n > 0
        padding = n - len(data) % n
        if padding == n:
            return data
        else:
            return data + b'\x00' * padding
    @staticmethod
    def align_up(x: int, n: int) -> int:
        return (x + n - 1) // n * n

class Reader:
    def __init__(self, buffer, cursor=0):
        self._buffer = buffer
        self._cursor = cursor
    def u1(self, move_cursor=True) -> int:
        return self.unpack('B', move_cursor=move_cursor)[0]
    def u4(self, move_cursor=True) -> int:
        return self.unpack('<I', move_cursor=move_cursor)[0]
    def u8(self, move_cursor=True) -> int:
        return self.unpack('<Q', move_cursor=move_cursor)[0]
    def i1(self, move_cursor=True) -> int:
        return self.unpack('b', move_cursor=move_cursor)[0]
    def i4(self, move_cursor=True) -> int:
        return self.unpack('<i', move_cursor=move_cursor)[0]
    def i8(self, move_cursor=True) -> int:
        return self.unpack('<q', move_cursor=move_cursor)[0]
    def s(self, n: int, move_cursor=True) -> bytes:
        return self.unpack(f'{n}s', move_cursor=move_cursor)[0]
    def unpack(self, f: str, offset=0, move_cursor=True):
        x = struct.unpack_from(f, self._buffer, self._cursor + offset)
        if move_cursor:
            self._cursor += struct.calcsize(f)
        return x
    def string(self, move_cursor=True) -> str:
        length = self.i4(move_cursor=move_cursor)
        if length == 0:
            return str()
        else:
            assert length > 0
            offset = 0 if move_cursor else 4
            return self.unpack(f'{length}s', offset=offset, move_cursor=move_cursor)[0].rstrip(b'\x00').decode()

class PakInfo:
    def __init__(self, buffer, keystream: List[int]):
        def decrypt_index_encrypted(x: int) -> int:
            MASK_8 = 255
            return (x ^ keystream[3]) & MASK_8
        def decrypt_magic(x: int) -> int:
            return x ^ keystream[2]
        def decrypt_index_hash(x: bytes) -> bytes:
            key = struct.pack('<5I', *keystream[4:][:5])
            assert len(x) == len(key)
            return bytes((a ^ b for a, b in zip(x, key)))
        def decrypt_index_size(x: int) -> int:
            return x ^ (keystream[10] << 32 | keystream[11])
        def decrypt_index_offset(x: int) -> int:
            return x ^ (keystream[0] << 32 | keystream[1])
        reader = Reader(buffer[-PakInfo._mem_size((-1)):])
        self.index_encrypted = decrypt_index_encrypted(reader.u1()) == 1
        self.magic = decrypt_magic(reader.u4())
        self.version = reader.u4()
        self.index_hash = decrypt_index_hash(reader.s(20)) if self.version >= 6 else bytes()
        self.index_size = decrypt_index_size(reader.u8())
        self.index_offset = decrypt_index_offset(reader.u8())
        if self.version <= 3:
            self.index_encrypted = False
    @staticmethod
    def _mem_size(_: int) -> int:
        return 45

class TencentPakInfo(PakInfo):
    def __init__(self, buffer, keystream: List[int]):
        def decrypt_unk(x: bytes) -> bytes:
            key = struct.pack('<8I', *keystream[7:][:8])
            assert len(x) == len(key)
            return bytes((a ^ b for a, b in zip(x, key)))
        def decrypt_stem_hash(x: int) -> int:
            return x ^ keystream[8]
        def decrypt_unk_hash(x: int) -> int:
            return x ^ keystream[9]
        super().__init__(buffer, keystream)
        reader = Reader(buffer[-TencentPakInfo._mem_size(self.version):])
        self.unk1 = decrypt_unk(reader.s(32)) if self.version >= 7 else bytes()
        self.packed_key = reader.s(256) if self.version >= 8 else bytes()
        self.packed_iv = reader.s(256) if self.version >= 8 else bytes()
        self.packed_index_hash = reader.s(256) if self.version >= 8 else bytes()
        self.stem_hash = decrypt_stem_hash(reader.u4()) if self.version >= 9 else 0
        self.unk2 = decrypt_unk_hash(reader.u4()) if self.version >= 9 else 0
        self.content_org_hash = reader.s(20) if self.version >= 12 else bytes()
    @staticmethod
    def _mem_size(version: int) -> int:
        size_for_7 = 32 if version >= 7 else 0
        size_for_8 = 768 if version >= 8 else 0
        size_for_9 = 8 if version >= 9 else 0
        size_for_12 = 20 if version >= 12 else 0
        return PakInfo._mem_size(version) + size_for_7 + size_for_8 + size_for_9 + size_for_12

class PakCompressedBlock:
    def __init__(self, reader: Reader):
        self.start = reader.u8()
        self.end = reader.u8()

@dataclass
class TencentPakEntry:
    def __init__(self, reader: Reader, version: int):
        self.content_hash = reader.s(20)
        if version <= 1:
            _ = reader.u8()
        self.offset = reader.u8()
        self.uncompressed_size = reader.u8()
        self.compression_method = reader.u4() & CM_MASK
        self.size = reader.u8()
        self.unk1 = reader.u1() if version >= 5 else 0
        self.unk2 = reader.s(20) if version >= 5 else bytes()
        if self.compression_method != 0 and version >= 3:
            self.compressed_blocks = [PakCompressedBlock(reader) for _ in range(reader.u4())]
        else:
            self.compressed_blocks = []
        self.compression_block_size = reader.u4() if version >= 4 else 0
        self.encrypted = reader.u1() == 1 if version >= 4 else False
        self.encryption_method = reader.u4() if version >= 12 else 0
        self.index_new_sep = reader.u4() if version >= 12 else 0

class PakCrypto:
    class _LCG:
        def __init__(self, seed: int):
            self.state = seed
        def next(self) -> int:
            MASK_32 = 4294967295
            MSB_1 = 2147483648
            def wrap(x: int) -> int:
                x &= MASK_32
                if not x & MSB_1:
                    return x
                else:
                    return (x + MSB_1 & MASK_32) - MSB_1
            x1 = wrap(1103515245 * self.state)
            self.state = wrap(x1 + 12345)
            x2 = wrap(x1 + 77880) if self.state < 0 else self.state
            return (x2 >> 16 & MASK_32) % 32767
    @staticmethod
    def zuc_keystream() -> List[int]:
        zuc = _ZUC_CLASS(ZUC_KEY, ZUC_IV)
        return [struct.unpack('>I', zuc.generate())[0] for _ in range(16)]
    @staticmethod
    def _xorxor(buffer, x) -> bytes:
        return bytes((buffer[i] ^ x[i % len(x)] for i in range(len(buffer))))
    @staticmethod
    def _hashhash(buffer, n: int) -> bytes:
        result = bytes()
        for i in range(math.ceil(n / SHA1.digest_size)):
            result += SHA1.new(buffer).digest()
        if len(result) >= n:
            result = result[:n]
            return result
        else:
            result += b'\x00' * (n - len(result))
            return result
    @staticmethod
    def _meowmeow(buffer) -> bytes:
        def unpad(x):
            skip = 1 + next((i for i in range(len(x)) if x[i]!= 0))
            return x[skip:]
        if len(buffer) < 43:
            return bytes()
        else:
            x1 = buffer[1:][:SHA1.digest_size]
            x2 = buffer[SHA1.digest_size + 1:]
            x1 = PakCrypto._xorxor(x1, PakCrypto._hashhash(x2, len(x1)))
            x2 = PakCrypto._xorxor(x2, PakCrypto._hashhash(x1, len(x2)))
            part1, m = (x2[:SHA1.digest_size], x2[SHA1.digest_size:])
            if part1!= SHA1.new(b'\x00' * SHA1.digest_size).digest():
                return bytes()
            else:
                return unpad(m)
    @staticmethod
    def rsa_extract(signature: bytes, modulus: bytes) -> bytes:
        c = int.from_bytes(signature, 'little')
        n = int.from_bytes(modulus, 'little')
        e = 65537
        m = pow(c, e, n).to_bytes(256, 'little').rstrip(b'\x00')
        return PakCrypto._meowmeow(Misc.pad_to_n(m, 4))
    @staticmethod
    def _decrypt_simple1(ciphertext) -> bytes:
        return bytes((x ^ SIMPLE1_DECRYPT_KEY for x in ciphertext))
    @staticmethod
    def _decrypt_simple2(ciphertext) -> bytes:
        class RollingKey:
            def __init__(self, initial_value: int):
                self._value = initial_value
            def update(self, x: int) -> int:
                self._value ^= x
                return self._value
        assert len(ciphertext) % SIMPLE2_BLOCK_SIZE == 0
        initial_key, = struct.unpack('<I', SIMPLE2_DECRYPT_KEY)
        rolling_key = RollingKey(initial_key)
        plaintext = (struct.pack('<I', rolling_key.update(x)) for x in struct.unpack(f'<{len(ciphertext) // 4}I', ciphertext))
        return bytes(it.chain.from_iterable(plaintext))
    @staticmethod
    @lru_cache(maxsize=1)
    def _derive_sm4_key(file_path: PurePath, encryption_method: int) -> bytes:
        part1 = file_path.stem.lower()
        if encryption_method == EM_SM4_2:
            secret = SM4_SECRET_2
        else:
            if encryption_method == EM_SM4_4:
                secret = SM4_SECRET_4
            else:
                index = (encryption_method - EM_SM4_NEW_BASE) % len(SM4_SECRET_NEW)
                secret = f'{SM4_SECRET_NEW[index]}{encryption_method}'
        return SHA1.new(str(part1 + secret).encode()).digest()[:SM4.key_length()]
    @staticmethod
    @lru_cache(maxsize=1)
    def _sm4_context_for_key(key: bytes) -> SM4:
        return SM4(key)
    @staticmethod
    def _decrypt_sm4(ciphertext, file_path: PurePath, encryption_method: int) -> bytes:
        assert len(ciphertext) % SM4.block_length() == 0
        key = PakCrypto._derive_sm4_key(file_path, encryption_method)
        sm4 = PakCrypto._sm4_context_for_key(key)
        return bytes(it.chain.from_iterable((sm4.decrypt(x) for x in _batched(ciphertext, SM4.block_length()))))
    @staticmethod
    def decrypt_index(ciphertext, pak_info: TencentPakInfo) -> bytes:
        if pak_info.version > 7:
            key = PakCrypto.rsa_extract(pak_info.packed_key, RSA_MOD_1)
            iv = PakCrypto.rsa_extract(pak_info.packed_iv, RSA_MOD_1)
            assert len(key) == 32 and len(iv) == 32
            aes = AES.new(key, MODE_CBC, iv[:16])
            return unpad(aes.decrypt(ciphertext), AES.block_size)
        else:
            return bytes(PakCrypto._decrypt_simple1(ciphertext))
    @staticmethod
    def _is_simple1_method(encryption_method: int) -> bool:
        return encryption_method == EM_SIMPLE1
    @staticmethod
    def _is_simple2_method(encryption_method: int) -> bool:
        return encryption_method == EM_SIMPLE2 or encryption_method == 17
    @staticmethod
    def _is_sm4_method(encryption_method: int) -> bool:
        return encryption_method == EM_SM4_2 or encryption_method == EM_SM4_4 or encryption_method & EM_SM4_NEW_MASK!= 0
    @staticmethod
    def align_encrypted_content_size(n: int, encryption_method: int) -> int:
        if PakCrypto._is_simple2_method(encryption_method):
            return Misc.align_up(n, SIMPLE2_BLOCK_SIZE)
        else:
            if PakCrypto._is_sm4_method(encryption_method):
                return Misc.align_up(n, SM4.block_length())
            else:
                return n
    @staticmethod
    def decrypt_block(ciphertext, file: PurePath, encryption_method: int) -> bytes:
        if PakCrypto._is_simple1_method(encryption_method):
            return PakCrypto._decrypt_simple1(ciphertext)
        else:
            if PakCrypto._is_simple2_method(encryption_method):
                return PakCrypto._decrypt_simple2(ciphertext)
            else:
                if PakCrypto._is_sm4_method(encryption_method):
                    return PakCrypto._decrypt_sm4(ciphertext, file, encryption_method)
                else:
                    raise ValueError(f'Unknown encryption method: {encryption_method}')
    @staticmethod
    @lru_cache(maxsize=33)
    def generate_block_indices(n: int, encryption_method: int) -> List[int]:
        if not PakCrypto._is_sm4_method(encryption_method):
            return list(range(n))
        else:
            permutation = []
            lcg = PakCrypto._LCG(n)
            while len(permutation)!= n:
                x = lcg.next() % n
                if x not in permutation:
                    permutation.append(x)
            inverse = [0] * len(permutation)
            for i, x in enumerate(permutation):
                inverse[x] = i
            return inverse

class PakCompression:
    @staticmethod
    @lru_cache(maxsize=33)
    def _zstd_decompressor(dict: ZstdCompressionDict) -> ZstdDecompressor:
        return ZstdDecompressor(dict)
    @staticmethod
    def zstd_dictionary(dict_data) -> ZstdCompressionDict:
        return ZstdCompressionDict(dict_data, DICT_TYPE_AUTO)
    @staticmethod
    def decompress_block(block, dict: Optional[ZstdCompressionDict], compression_method: int) -> bytes:
        if compression_method == CM_ZLIB:
            try:
                return zlib.decompress(block)
            except zlib.error:
                return block
        else:
            if compression_method == CM_ZSTD or compression_method == CM_ZSTD_DICT:
                if compression_method!= CM_ZSTD_DICT:
                    dict = None
                return PakCompression._zstd_decompressor(dict).decompress(block)
            else:
                raise ValueError(f'Unknown compression method: {compression_method}')

class TencentPakFile:
    def __init__(self, file_path: PurePath, is_od=False):
        self._file_path = file_path
        with open(file_path, 'rb') as file:
            self._file_content = memoryview(file.read())
        self._is_od = is_od
        self._mount_point = PurePath()
        self._is_zstd_with_dict = 'zsdic' in str(self._file_path)
        self._zstd_dict = None
        self._files = []
        self._index = {}
        self._pak_info = TencentPakInfo(self._file_content, PakCrypto.zuc_keystream())
        self._verify_stem_hash()
        self._tencent_load_index()
    
    def _get_method_str(self, method_int, is_encryption):
        if is_encryption:
            if PakCrypto._is_simple1_method(method_int): return "SIMPLE1"
            if PakCrypto._is_simple2_method(method_int): return "SIMPLE2"
            if PakCrypto._is_sm4_method(method_int): return f"SM4 (Type {method_int})"
            return "NONE" if method_int == 0 else "UNKNOWN"
        else:
            if method_int == CM_NONE: return "NONE"
            if method_int == CM_ZLIB: return "ZLIB"
            if method_int == CM_ZSTD: return "ZSTD"
            if method_int == CM_ZSTD_DICT: return "ZSTD_DICT"
            return "UNKNOWN"
    
    def _verify_stem_hash(self) -> None:
        if not self._is_od and self._pak_info.version >= 9:
                assert self._pak_info.stem_hash == zlib.crc32(self._file_path.stem.encode('utf-32le'))
    def _tencent_load_index(self) -> None:
        index_data = self._file_content[self._pak_info.index_offset:][:self._pak_info.index_size]
        if self._pak_info.index_encrypted:
            index_data = PakCrypto.decrypt_index(index_data, self._pak_info)
        else:
            index_data = index_data
        self._verify_index_hash(index_data)
        self._load_index(index_data)
    def _verify_index_hash(self, index_data) -> None:
        expected_hash = self._pak_info.index_hash
        if not self._is_od and self._pak_info.version >= 8:
                assert expected_hash == PakCrypto.rsa_extract(self._pak_info.packed_index_hash, RSA_MOD_2)
        assert expected_hash == SHA1.new(index_data).digest()
    @staticmethod
    def _construct_mount_point(mount_point: str) -> PurePath:
        result = PurePath()
        for part in PurePath(mount_point).parts:
            if part!= '..':
                result /= part
        return result
    def _peek_content(self, offset: int, size: int, encryption_method: int) -> memoryview:
        size = PakCrypto.align_encrypted_content_size(size, encryption_method)
        return self._file_content[offset:][:size]
    def _peek_block_content(self, block: PakCompressedBlock, encryption_method: int) -> memoryview:
        size = PakCrypto.align_encrypted_content_size(block.end - block.start, encryption_method)
        return self._file_content[block.start:][:size]
    def _construct_zstd_dict(self, dict_entry: TencentPakEntry) -> None:
        assert not self._zstd_dict
        assert not dict_entry.encrypted
        assert dict_entry.compression_method == CM_NONE
        reader = Reader(self._peek_content(dict_entry.offset, dict_entry.size, 0))
        dict_size = reader.u8()
        _ = reader.u4()
        assert dict_size == reader.u4()
        dict_data = reader.s(dict_size)
        self._zstd_dict = PakCompression.zstd_dictionary(dict_data)
    def _load_index(self, index_data) -> None:
        if self._pak_info.version <= 10:
            raise ValueError(f'Unsupported version: {self._pak_info.version}')
        else:
            reader = Reader(index_data)
            self._mount_point = self._construct_mount_point(reader.string())
            self._files = [TencentPakEntry(reader, self._pak_info.version) for _ in range(reader.u4())]
            for _ in range(reader.u8()):
                dir_path = PurePath(reader.string())
                e = {reader.string(): self._files[~reader.i4()] for _ in range(reader.u8())}
                if self._is_zstd_with_dict and dir_path.name == 'zstddic':
                    assert len(e) == 1
                    self._construct_zstd_dict(e[[*e.keys()][0]])
                else:
                    self._index.update({PurePath(dir_path): e})
    
    def _write_to_disk(self, file_path: Path, entry: TencentPakEntry) -> None:
        encryption_method = entry.encryption_method
        compression_method = entry.compression_method

        enc_str = self._get_method_str(encryption_method, True)
        comp_str = self._get_method_str(compression_method, False)
        console.print(f"[bold cyan]->[/] Unpack: [bold green]{file_path.name}[/] [[bold yellow]{comp_str}[/]/[bold magenta]{enc_str}[/]]")

        with open(file_path, 'wb') as file:
            if compression_method == CM_NONE:
                data = self._peek_content(entry.offset, entry.size, encryption_method)
                if entry.encrypted:
                    data = PakCrypto.decrypt_block(data, file_path, encryption_method)
                file.write(data)
                return
            else:
                for x in PakCrypto.generate_block_indices(len(entry.compressed_blocks), encryption_method):
                    data = self._peek_block_content(entry.compressed_blocks[x], encryption_method)
                    if entry.encrypted:
                        data = PakCrypto.decrypt_block(data, file_path, encryption_method)
                    data = PakCompression.decompress_block(data, self._zstd_dict, compression_method)
                    file.write(data)
    
    def dump(self, out_path: Path) -> None:
        out_path = out_path / self._mount_point
        out_path.mkdir(parents=True, exist_ok=True)
        total_files = sum(len(d) for d in self._index.values())
        with Progress(
            SpinnerColumn(),
            TextColumn("[bold cyan][UNPACK][/] {task.description}"),
            BarColumn(),
            TaskProgressColumn(),
            TimeElapsedColumn(),
            console=console
        ) as progress:
            task = progress.add_task("Extracting files...", total=total_files)
            for dir_path, dir_content in self._index.items():
                current_out_path = out_path / dir_path
                current_out_path.mkdir(parents=True, exist_ok=True)
                for file_name, entry in dir_content.items():
                    self._write_to_disk(current_out_path / file_name, entry)
                    progress.update(task, advance=1)

def dump_unpacking_log(pak_file, output_log_path: Path):
    with open(output_log_path, 'w', encoding='utf-8') as log_file:
        log_file.write('================================================================================\n')
        log_file.write('PAK UNPACKING DEBUG LOG\n')
        log_file.write('================================================================================\n\n')
        log_file.write(f'PAK File: {pak_file._file_path}\n')
        log_file.write(f'PAK Info Version: {pak_file._pak_info.version}\n')
        log_file.write(f'Mount Point: {pak_file._mount_point}\n')
        log_file.write('--------------------------------------------------------------------------------\n\n')
        file_count = 0
        for dir_path, files in pak_file._index.items():
            for file_name, entry in files.items():
                file_count += 1
                full_path = str(PurePath(dir_path) / file_name).replace('\\', '/')
                log_file.write(f'\n[{file_count}] {full_path}\n')
                log_file.write(f'  Uncompressed Size: {entry.uncompressed_size:,} bytes\n')
                log_file.write(f'  Compressed Size: {entry.size:,} bytes\n')
                log_file.write(f'  Compression Method: {entry.compression_method}\n')
                log_file.write(f'  Encryption Method: {entry.encryption_method}\n')
                log_file.write(f'  Compressed Blocks: {len(entry.compressed_blocks)}\n')
                if entry.compressed_blocks:
                    for i, blk in enumerate(entry.compressed_blocks):
                        block_size = blk.end - blk.start
                        log_file.write(f'    Block {i}: Offset={blk.start:,} Size={block_size:,} bytes\n')
        log_file.write('\n================================================================================\n')
        log_file.write('END OF LOG\n')
        log_file.write('================================================================================\n')
    console.print(f'[bold #00FF88]✅ Debug log saved to: {output_log_path}[/bold #00FF88]')

def _zstd_add_skippable_padding(data: bytes, pad_len: int) -> bytes:
    if pad_len <= 0:
        return data
    else:
        out = bytearray(data)
        while pad_len > 0:
            frame_len = min(max(pad_len - 8, 0), 1048576)
            out += b'P*M\x18'
            out += struct.pack('<I', frame_len)
            out += b'\x00' * frame_len
            pad_len -= 8 + frame_len
        return bytes(out)

def _encrypt_plaintext(plaintext: bytes, pak_relative_path: PurePath, encryption_method: int) -> bytes:
    if PakCrypto._is_simple1_method(encryption_method):
        return bytes((b ^ SIMPLE1_DECRYPT_KEY for b in plaintext))
    else:
        if PakCrypto._is_simple2_method(encryption_method):
            pad = -len(plaintext) % SIMPLE2_BLOCK_SIZE
            plaintext += b'\x00' * pad
            key, = struct.unpack('<I', SIMPLE2_DECRYPT_KEY)
            rolling = key
            out = []
            for x, in struct.iter_unpack('<I', plaintext):
                c = rolling ^ x
                out.append(c)
                rolling ^= c
            return struct.pack(f'<{len(out)}I', *out)
        else:
            if PakCrypto._is_sm4_method(encryption_method):
                key = PakCrypto._derive_sm4_key(pak_relative_path, encryption_method)
                sm4 = PakCrypto._sm4_context_for_key(key)
                pad_len = -len(plaintext) % 16
                if pad_len > 0:
                    plaintext = plaintext + b'\x00' * pad_len
                out = bytearray()
                for i in range(0, len(plaintext), 16):
                    block = plaintext[i:i + 16]
                    if len(block) < 16:
                        block = block.ljust(16, b'\x00')
                    out.extend(sm4.encrypt(block))
                return bytes(out)
            else:
                return plaintext

# ==================== WORKING REPACK FUNCTIONS ====================

def _repack_uncompressed(outfh, pak_file, entry, pak_relative_path: PurePath, new_data: bytes):
    enc_method = entry.encryption_method
    target_size = entry.size
    enc_region = PakCrypto.align_encrypted_content_size(target_size, enc_method) if entry.encrypted else target_size
    plaintext = new_data[:enc_region]
    if entry.encrypted:
        a = PakCrypto.align_encrypted_content_size(len(plaintext), enc_method)
        plaintext += b'\x00' * (a - len(plaintext))
        cipher = _encrypt_plaintext(plaintext, pak_relative_path, enc_method)
        outfh.seek(entry.offset)
        outfh.write(cipher)
        with open(pak_file._file_path, 'rb') as src:
            src.seek(entry.offset + len(cipher))
            outfh.write(src.read(enc_region - len(cipher)))
    else:
        outfh.seek(entry.offset)
        outfh.write(plaintext)
        with open(pak_file._file_path, 'rb') as src:
            src.seek(entry.offset + len(plaintext))
            outfh.write(src.read(target_size - len(plaintext)))

def _best_compress(chunk, cm, zstd_dict=None):
    """Compress one chunk at the best achievable level (fast levels to avoid in-game lag)."""
    if cm == CM_ZLIB:
        return zlib.compress(chunk, 6)
    if cm in (CM_ZSTD, CM_ZSTD_DICT):
        zd = zstd_dict if cm == CM_ZSTD_DICT else None
        for lvl in _ZSTD_FAST_LEVELS:
            try:
                return ZstdCompressor(level=lvl, dict_data=zd, threads=1).compress(chunk)
            except Exception:
                continue
    return chunk  # fallback: store raw

def _pw_string(s):
    """PAK string serialiser: i4(len_with_null) + bytes + null."""
    if not s: return struct.pack('<i', 0)
    b = s.encode('utf-8') + b'\x00'
    return struct.pack('<i', len(b)) + b

def _pw_entry(e, v):
    """Serialise one TencentPakEntry back to bytes."""
    w = bytearray(e.content_hash)
    w += struct.pack('<Q', e.offset)
    w += struct.pack('<Q', e.uncompressed_size)
    w += struct.pack('<I', e.compression_method)
    w += struct.pack('<Q', e.size)
    if v >= 5:
        w += bytes([e.unk1])
        w += e.unk2  # 20 bytes
    if e.compression_method != CM_NONE and v >= 3:
        w += struct.pack('<I', len(e.compressed_blocks))
        for b in e.compressed_blocks:
            w += struct.pack('<QQ', b.start, b.end)
    if v >= 4:
        w += struct.pack('<I', e.compression_block_size)
        w += bytes([1 if e.encrypted else 0])
    if v >= 12:
        w += struct.pack('<II', e.encryption_method, e.index_new_sep)
    return bytes(w)

def _get_all_dirs_and_mp(pak_file):
    """Re-parse raw (possibly encrypted) index → (mount_point_str, ordered dirs dict)."""
    raw = bytes(pak_file._file_content[
        pak_file._pak_info.index_offset:][:pak_file._pak_info.index_size])
    if pak_file._pak_info.index_encrypted:
        raw = PakCrypto.decrypt_index(raw, pak_file._pak_info)
    r = Reader(raw)
    mp = r.string()
    num_files = r.u4()
    for _ in range(num_files):
        TencentPakEntry(r, pak_file._pak_info.version)
    dirs = {}
    for _ in range(r.u8()):
        dp = r.string()
        cnt = r.u8()
        dirs[dp] = {r.string(): pak_file._files[~r.i4()] for _ in range(cnt)}
    return mp, dirs

def repack_pak_file_full(pak_file, edited_root, output_path, target_path=None, force_add=False):
    """
    FULL REBUILD REPACK - FIXED FOR NEW FILES (OPTION 4)
    """
    import copy as _cp

    console.print(f'[bold cyan]📦 Full PAK Rebuild mode (Option 3 & 4 logic)[/bold cyan]')
    if target_path:
        console.print(f'[bold cyan]🎯 Target path: {target_path}[/bold cyan]')
    
    # Get all files from edit folder
    edit_files = []
    for p in Path(edited_root).rglob('*'):
        if p.is_file():
            edit_files.append(p)
    
    if not edit_files:
        console.print('[bold red]❌ No files found in EDIT folder![/bold red]')
        return 0
    
    console.print(f'[bold cyan]📁 Found {len(edit_files)} files in EDIT folder[/bold cyan]')

    version = pak_file._pak_info.version
    keystream = PakCrypto.zuc_keystream()
    orig_fc = pak_file._file_content

    # Get existing directory structure
    mp_str, all_dirs = _get_all_dirs_and_mp(pak_file)

    # FIX 1: Normalize target_path to match exact case and slashes of existing dirs
    if target_path and force_add:
        target_path = target_path.replace('\\', '/')
        matched_dir = None
        for existing_dir in all_dirs.keys():
            if existing_dir.strip('/').lower() == target_path.strip('/').lower():
                matched_dir = existing_dir
                break
        if matched_dir:
            target_path = matched_dir # Use the exact string from the PAK
        else:
            target_path = target_path.strip('/') + '/' # Ensure standard trailing slash
    
    # Build name→entry map
    pak_name_map = {}
    for dir_path, files in pak_file._index.items():
        for name, entry in files.items():
            full_path = str(PurePath(dir_path)/name).replace('\\', '/')
            pak_name_map.setdefault(name.lower(), []).append((full_path, entry))

    # Find matching files
    edited = {}
    
    for p in edit_files:
        fl = p.name.lower()
        found_match = False
        
        if fl in pak_name_map:
            cands = pak_name_map[fl]
            if target_path:
                target_candidates = [(fp, e) for fp, e in cands if target_path.strip('/') in fp]
                if target_candidates:
                    sz = p.stat().st_size
                    sm = [(fp, e) for fp, e in target_candidates if e.uncompressed_size == sz]
                    fp, ent = sm[0] if sm else target_candidates[0]
                    edited[fp] = (p, ent)
                    found_match = True
            
            if not found_match:
                sz = p.stat().st_size
                sm = [(fp, e) for fp, e in cands if e.uncompressed_size == sz]
                fp, ent = sm[0] if sm else cands[0]
                if target_path:
                    new_fp = f"{target_path.rstrip('/')}/{p.name}"
                    edited[new_fp] = (p, ent)
                else:
                    edited[fp] = (p, ent)
                found_match = True
        
        if not found_match:
            stem = p.stem.lower()
            ext = p.suffix.lower()
            for dir_path, files in pak_file._index.items():
                for name, entry in files.items():
                    if Path(name).stem.lower() == stem and Path(name).suffix.lower() == ext:
                        full_path = str(PurePath(dir_path)/name).replace('\\', '/')
                        if target_path:
                            new_fp = f"{target_path.rstrip('/')}/{p.name}"
                            edited[new_fp] = (p, entry)
                        else:
                            edited[full_path] = (p, entry)
                        found_match = True
                        break
                if found_match:
                    break
        
        if not found_match and force_add and target_path:
            template_entry = None
            for dir_path, files in pak_file._index.items():
                for name, entry in files.items():
                    if Path(name).suffix.lower() == p.suffix.lower():
                        template_entry = entry
                        break
                if template_entry: break
            
            if not template_entry:
                for dir_path, files in pak_file._index.items():
                    for name, entry in files.items():
                        template_entry = entry
                        break
                    if template_entry: break
            
            if template_entry:
                new_fp = f"{target_path.rstrip('/')}/{p.name}"
                edited[new_fp] = (p, template_entry)

    if not edited:
        console.print('[bold red]❌ No files to repack![/bold red]')
        return 0

    console.print(f'  [bold bright_cyan]📁 Files to repack: {len(edited)}[/bold bright_cyan]')

    new_files = []
    for e in pak_file._files:
        ne = _cp.copy(e)
        ne.compressed_blocks = [_cp.copy(b) for b in e.compressed_blocks]
        new_files.append(ne)

    old_to_new = {id(pak_file._files[i]): new_files[i] for i in range(len(pak_file._files))}
    edited_paths = {fp: p for fp, (p, _) in edited.items()}

    out_buf = bytearray()

    for dp_str, dir_files in list(all_dirs.items()):
        for name, old_entry in list(dir_files.items()):
            full_path = str(PurePath(dp_str)/name).replace('\\', '/')
            ne = old_to_new.get(id(old_entry), None)
            
            if ne is None:
                ne = _cp.copy(old_entry)
                ne.compressed_blocks = [_cp.copy(b) for b in old_entry.compressed_blocks]
                new_files.append(ne)
                old_to_new[id(old_entry)] = ne

            em = old_entry.encryption_method
            cm = old_entry.compression_method

            if full_path in edited_paths:
                p, template = edited[full_path]
                new_raw = _harden_asset_for_repack(str(full_path), p.read_bytes())
                pak_rel = PurePath(full_path)

                ne.content_hash = SHA1.new(new_raw).digest()
                ne.uncompressed_size = len(new_raw)
                ne.compression_method = template.compression_method if template else cm
                ne.encryption_method = template.encryption_method if template else em
                ne.encrypted = template.encrypted if template else old_entry.encrypted
                ne.unk1 = template.unk1 if template else old_entry.unk1
                
                # FIX 2: If we changed the path of an existing file via target_path, recalculate unk2
                if template and target_path:
                    full_path_str = mp_str + full_path
                    ne.unk2 = SHA1.new(full_path_str.lower().encode('utf-8')).digest()
                else:
                    ne.unk2 = template.unk2 if template else old_entry.unk2
                    
                ne.index_new_sep = template.index_new_sep if template else old_entry.index_new_sep

                if ne.compression_method == CM_NONE:
                    store = bytearray(new_raw)
                    cipher = (_encrypt_plaintext(bytes(store), pak_rel, ne.encryption_method)
                              if ne.encrypted else bytes(store))
                    ne.offset = len(out_buf)
                    ne.size = len(cipher)
                    ne.uncompressed_size = len(new_raw)
                    out_buf += cipher
                else:
                    cs = (template.compression_block_size if template and template.compression_block_size > 0 
                          else old_entry.compression_block_size if old_entry.compression_block_size > 0 
                          else 65536)
                    chunks = [new_raw[i:i+cs] for i in range(0, len(new_raw), cs)]
                    new_blks = []
                    for chunk in chunks:
                        compressed = _best_compress(chunk, ne.compression_method, pak_file._zstd_dict)
                        cipher = (_encrypt_plaintext(compressed, pak_rel, ne.encryption_method)
                                  if ne.encrypted else compressed)
                        blk_buf = bytearray(cipher)
                        blk = PakCompressedBlock.__new__(PakCompressedBlock)
                        blk.start = len(out_buf)
                        blk.end = blk.start + len(blk_buf)
                        out_buf += blk_buf
                        new_blks.append(blk)

                    ne.compressed_blocks = new_blks
                    ne.offset = new_blks[0].start if new_blks else len(out_buf)
                    ne.size = sum(b.end - b.start for b in new_blks)
                    ne.uncompressed_size = len(new_raw)

                console.print(f'[green]✓ Processed: {full_path}[/green]')

            else:
                if cm == CM_NONE:
                    read_sz = (PakCrypto.align_encrypted_content_size(old_entry.size, em)
                               if old_entry.encrypted else old_entry.size)
                    ne.offset = len(out_buf)
                    out_buf += bytes(orig_fc[old_entry.offset: old_entry.offset + read_sz])

                elif old_entry.compressed_blocks:
                    new_blks = []
                    for ob in old_entry.compressed_blocks:
                        unc = ob.end - ob.start
                        enc = (PakCrypto.align_encrypted_content_size(unc, em)
                               if old_entry.encrypted else unc)
                        nb = PakCompressedBlock.__new__(PakCompressedBlock)
                        nb.start = len(out_buf)
                        nb.end = nb.start + enc
                        out_buf += bytes(orig_fc[ob.start: ob.start + enc])
                        new_blks.append(nb)
                    ne.compressed_blocks = new_blks
                    ne.offset = new_blks[0].start

    if target_path and force_add:
        for fp, (p, template) in edited.items():
            already_processed = False
            for dp_str, dir_files in all_dirs.items():
                for name, entry in dir_files.items():
                    if str(PurePath(dp_str)/name).replace('\\', '/') == fp:
                        already_processed = True
                        break
                if already_processed:
                    break
            
            if not already_processed:
                ne = _cp.copy(template)
                new_raw = _harden_asset_for_repack(str(fp), p.read_bytes())
                pak_rel = PurePath(fp)
                
                ne.content_hash = SHA1.new(new_raw).digest()
                ne.uncompressed_size = len(new_raw)
                ne.compression_method = template.compression_method
                ne.encryption_method = template.encryption_method
                ne.encrypted = template.encrypted
                ne.unk1 = template.unk1
                
                # FIX 3: Accurately generate the path hash (unk2) for the NEW file
                # The game engine uses this specific SHA1 hash to find the file!
                full_path_str = mp_str + fp
                ne.unk2 = SHA1.new(full_path_str.lower().encode('utf-8')).digest()
                
                ne.index_new_sep = template.index_new_sep

                if ne.compression_method == CM_NONE:
                    store = bytearray(new_raw)
                    cipher = (_encrypt_plaintext(bytes(store), pak_rel, ne.encryption_method)
                              if ne.encrypted else bytes(store))
                    ne.offset = len(out_buf)
                    ne.size = len(cipher)
                    ne.uncompressed_size = len(new_raw)
                    out_buf += cipher
                else:
                    cs = template.compression_block_size if template.compression_block_size > 0 else 65536
                    chunks = [new_raw[i:i+cs] for i in range(0, len(new_raw), cs)]
                    new_blks = []
                    for chunk in chunks:
                        compressed = _best_compress(chunk, ne.compression_method, pak_file._zstd_dict)
                        cipher = (_encrypt_plaintext(compressed, pak_rel, ne.encryption_method)
                                  if ne.encrypted else compressed)
                        blk_buf = bytearray(cipher)
                        blk = PakCompressedBlock.__new__(PakCompressedBlock)
                        blk.start = len(out_buf)
                        blk.end = blk.start + len(blk_buf)
                        out_buf += blk_buf
                        new_blks.append(blk)

                    ne.compressed_blocks = new_blks
                    ne.offset = new_blks[0].start if new_blks else len(out_buf)
                    ne.size = sum(b.end - b.start for b in new_blks)
                    ne.uncompressed_size = len(new_raw)

                new_files.append(ne)
                
                # FIX 4: Add to all_dirs mapping using the exact validated target_path
                if target_path not in all_dirs:
                    all_dirs[target_path] = {}
                all_dirs[target_path][p.name] = ne
                console.print(f'[green]✓ Added new: {fp}[/green]')

    eidx = {id(new_files[i]): i for i in range(len(new_files))}

    idx = bytearray(_pw_string(mp_str))
    idx += struct.pack('<I', len(new_files))
    for ne in new_files:
        idx += _pw_entry(ne, version)
    idx += struct.pack('<Q', len(all_dirs))
    for dp_str, dir_files in all_dirs.items():
        idx += _pw_string(dp_str)
        idx += struct.pack('<Q', len(dir_files))
        for name, old_e in dir_files.items():
            idx += _pw_string(name)
            found_idx = None
            for i, e in enumerate(new_files):
                if id(e) == id(old_e):
                    found_idx = i
                    break
            if found_idx is None:
                for i, e in enumerate(new_files):
                    if e.offset == old_e.offset and e.size == old_e.size:
                        found_idx = i
                        break
            if found_idx is not None:
                idx += struct.pack('<i', ~found_idx)
            else:
                idx += struct.pack('<i', -1)

    index_plain = bytes(idx)
    new_sha1 = SHA1.new(index_plain).digest()

    if pak_file._pak_info.index_encrypted:
        key = PakCrypto.rsa_extract(pak_file._pak_info.packed_key, RSA_MOD_1)
        iv = PakCrypto.rsa_extract(pak_file._pak_info.packed_iv, RSA_MOD_1)
        aes = AES.new(key, MODE_CBC, iv[:16])
        pad = (-len(index_plain)) % AES.block_size or AES.block_size
        index_bytes = aes.encrypt(index_plain + bytes([pad] * pad))
    else:
        index_bytes = index_plain

    new_idx_offset = len(out_buf)
    new_idx_size = len(index_bytes)
    out_buf += index_bytes

    footer_sz = TencentPakInfo._mem_size(version)
    new_footer = bytearray(orig_fc[-footer_sz:])

    h_key = struct.pack('<5I', *keystream[4:9])
    new_footer[-36:-16] = bytes(a ^ b for a, b in zip(new_sha1, h_key))
    new_footer[-16:-8] = ((new_idx_size ^ (keystream[10] << 32 | keystream[11])).to_bytes(8, 'little'))
    new_footer[-8:] = ((new_idx_offset ^ (keystream[0] << 32 | keystream[1])).to_bytes(8, 'little'))

    out_buf += new_footer

    with open(output_path, 'wb') as f:
        f.write(out_buf)

    return len(edited)


# ==================== ORIGINAL REPACK (For Option 2) ====================

def _repack_compressed_with_display(outfh, pak_file, entry, pak_relative_path, new_data, repack_dir, display):
    """Original compressed repack with display - Working fine"""
    blocks = entry.compressed_blocks
    enc_method = entry.encryption_method
    comp_method = entry.compression_method
    order = PakCrypto.generate_block_indices(len(blocks), enc_method)
    
    if len(new_data) != entry.uncompressed_size:
        if len(new_data) < entry.uncompressed_size:
            new_data = new_data.ljust(entry.uncompressed_size, b'\x00')
        else:
            new_data = new_data[:entry.uncompressed_size]

    if len(blocks) > 1:
        if entry.compression_block_size > 0:
            chunk_size = entry.compression_block_size
        else:
            block_sizes = [blk.end - blk.start for blk in blocks]
            total_block_size = sum(block_sizes)
            avg_block_size = total_block_size / len(blocks)
            avg_compression_ratio = total_block_size / entry.uncompressed_size if entry.uncompressed_size > 0 else 1
            chunk_size = int(avg_block_size / avg_compression_ratio) if avg_compression_ratio > 0 else 65536
        
        ptr = 0
        for logical_i, phys_i in enumerate(order):
            blk = blocks[phys_i]
            target_size = blk.end - blk.start
            chunk_len = min(chunk_size, len(new_data) - ptr)
            if chunk_len <= 0: break
            chunk = new_data[ptr:ptr + chunk_len]
            ptr += chunk_len
            
            with open(pak_file._file_path, 'rb') as src:
                src.seek(blk.start)
                original_compressed = src.read(target_size)
            
            compressed_ok = False
            new_compressed = None
            zstd_dict = pak_file._zstd_dict if comp_method == CM_ZSTD_DICT else None
            
            if comp_method in (CM_ZSTD, CM_ZSTD_DICT):
                for level in _ZSTD_FAST_LEVELS:
                    c = ZstdCompressor(level=level, dict_data=zstd_dict, threads=1)
                    new_compressed = c.compress(chunk)
                    if len(new_compressed) <= target_size:
                        compressed_ok = True
                        break
            elif comp_method == CM_ZLIB:
                new_compressed = zlib.compress(chunk, 6)
                if len(new_compressed) <= target_size:
                    compressed_ok = True
            
            if not compressed_ok:
                outfh.seek(blk.start)
                outfh.write(original_compressed)
                display.add_block(logical_i, target_size, False)
                continue
            
            if entry.encrypted:
                if PakCrypto._is_sm4_method(enc_method):
                    pad_len = -len(new_compressed) % 16
                    if pad_len > 0: new_compressed += b'\x00' * pad_len
                new_compressed = _encrypt_plaintext(new_compressed, pak_relative_path, enc_method)
            
            if len(new_compressed) > target_size:
                outfh.seek(blk.start)
                outfh.write(original_compressed)
                display.add_block(logical_i, target_size, False)
            else:
                outfh.seek(blk.start)
                outfh.write(new_compressed)
                if len(new_compressed) < target_size:
                    outfh.write(b'\x00' * (target_size - len(new_compressed)))
                ratio = len(new_compressed) / len(chunk) if len(chunk) > 0 else 1
                display.add_block(logical_i, target_size, True, ratio)
    else:
        if not blocks: return
        blk = blocks[0]
        target_size = blk.end - blk.start
        
        with open(pak_file._file_path, 'rb') as src:
            src.seek(blk.start)
            original_compressed = src.read(target_size)
        
        compressed_ok = False
        new_compressed = None
        zstd_dict = pak_file._zstd_dict if comp_method == CM_ZSTD_DICT else None
        
        if comp_method in (CM_ZSTD, CM_ZSTD_DICT):
            for level in _ZSTD_FAST_LEVELS:
                c = ZstdCompressor(level=level, dict_data=zstd_dict, threads=1)
                new_compressed = c.compress(new_data)
                if len(new_compressed) <= target_size:
                    compressed_ok = True
                    break
        elif comp_method == CM_ZLIB:
            new_compressed = zlib.compress(new_data, 6)
            if len(new_compressed) <= target_size:
                compressed_ok = True
        
        if not compressed_ok:
            outfh.seek(blk.start)
            outfh.write(original_compressed)
            display.add_block(0, target_size, False)
            return
        
        if entry.encrypted:
            if PakCrypto._is_sm4_method(enc_method):
                pad_len = -len(new_compressed) % 16
                if pad_len > 0: new_compressed += b'\x00' * pad_len
            new_compressed = _encrypt_plaintext(new_compressed, pak_relative_path, enc_method)
        
        if len(new_compressed) > target_size:
            outfh.seek(blk.start)
            outfh.write(original_compressed)
            display.add_block(0, target_size, False)
        else:
            outfh.seek(blk.start)
            outfh.write(new_compressed)
            if len(new_compressed) < target_size:
                outfh.write(b'\x00' * (target_size - len(new_compressed)))
            ratio = len(new_compressed) / len(new_data) if len(new_data) > 0 else 1
            display.add_block(0, target_size, True, ratio)

def smart_resolve_by_fingerprint(filename: str, repack_file: Path, candidates: list):
    repack_size = repack_file.stat().st_size
    size_matches = [(path, entry) for path, entry in candidates if entry.uncompressed_size == repack_size]
    if len(size_matches) == 1:
        return size_matches[0]
    if not size_matches:
        return None
    def fingerprint(e):
        return (e.uncompressed_size, e.size, e.compression_method, len(e.compressed_blocks), e.compression_block_size)
    base_fp = fingerprint(size_matches[0][1])
    final_matches = [(path, entry) for path, entry in size_matches if fingerprint(entry) == base_fp]
    if len(final_matches) == 1:
        return final_matches[0]
    return None

def repack_pak_file_with_block_display(pak_file, edited_root: Path, output_path: Path):
    """Original repack with simple block display - WORKING"""
    shutil.copy2(pak_file._file_path, output_path)
    
    pak_name_map = {}
    for dir_path, files in pak_file._index.items():
        for name, entry in files.items():
            full_path = str(PurePath(dir_path) / name).replace('\\', '/')
            key = name.lower()
            pak_name_map.setdefault(key, []).append((full_path, entry))
    
    edited = {}
    for p in edited_root.rglob('*'):
        if not p.is_file():
            continue
        fname_lower = p.name.lower()
        if fname_lower in pak_name_map:
            candidates = pak_name_map[fname_lower]
            if len(candidates) == 1:
                full_path, entry = candidates[0]
                edited[full_path] = (p, entry)
            else:
                resolved = smart_resolve_by_fingerprint(filename=p.name, repack_file=p, candidates=candidates)
                if resolved:
                    full_path, entry = resolved
                    edited[full_path] = (p, entry)
        else:
            stem = p.stem.lower()
            ext = p.suffix.lower()
            for dir_path, files in pak_file._index.items():
                for name, entry in files.items():
                    if Path(name).stem.lower() == stem and Path(name).suffix.lower() == ext:
                        full_path = str(PurePath(dir_path) / name).replace('\\', '/')
                        edited[full_path] = (p, entry)
                        break
    
    if not edited:
        console.print('[bold #FF0055]❌ No files to repack![/bold #FF0055]')
        return
    
    total_files = len(edited)
    display = SimpleBlockDisplay(total_files, pak_file._file_path.name)
    
    with open(output_path, 'r+b') as outfh:
        for full_path, (p, entry) in edited.items():
            file_name = p.name
            total_blocks = len(entry.compressed_blocks) if entry.compressed_blocks else 1
            
            display.start_file(file_name, total_blocks)
            new_data = p.read_bytes()
            pak_rel = PurePath(full_path)
            
            if entry.compression_method == CM_NONE:
                _repack_uncompressed(outfh, pak_file, entry, pak_rel, new_data)
                display.add_block(0, len(new_data), True)
            else:
                _repack_compressed_with_display(outfh, pak_file, entry, pak_rel, new_data, edited_root, display)
            
            display.finish_file()
    
    display.final_summary()

def detect_repack_mode(pak_path: Path) -> str:
    name = pak_path.name.lower()
    if name == 'mini_obb.pak':
        return 'MINI_OBB'
    if 'zsdic' in name:
        return 'OBBZSDIC'
    if 'game' in name or 'patch' in name:
        return 'GAMEPATCH'
    return 'OBBZSDIC'

def repack_mini_obb(pak, repack_dir, output_pak):
    console.print('[bold #00FFFF]🧩 Repack Mode: MINI_OBB[/bold #00FFFF]')
    pak._is_zstd_with_dict = False
    pak._zstd_dict = None
    repack_pak_file_with_block_display(pak_file=pak, edited_root=repack_dir, output_path=output_pak)

def repack_obbzsdic(pak, repack_dir, output_pak):
    console.print('[bold #00FFFF]🧩 Repack Mode: OBBZSDIC[/bold #00FFFF]')
    repack_pak_file_with_block_display(pak_file=pak, edited_root=repack_dir, output_path=output_pak)

def repack_gamepatch(pak, repack_dir, output_pak):
    console.print('[bold #00FFFF]🧩 Repack Mode: GAMEPATCH[/bold #00FFFF]')
    pak._is_zstd_with_dict = False
    pak._zstd_dict = None
    repack_pak_file_with_block_display(pak_file=pak, edited_root=repack_dir, output_path=output_pak)

def ensure_directories(base_dir: Path):
    (base_dir / "INPUT").mkdir(parents=True, exist_ok=True)
    (base_dir / "DUMP").mkdir(parents=True, exist_ok=True)
    (base_dir / "PAK").mkdir(parents=True, exist_ok=True)
    (base_dir / "UNPACK").mkdir(parents=True, exist_ok=True)
    (base_dir / "REPACK").mkdir(parents=True, exist_ok=True)
    (base_dir / "RESULT").mkdir(parents=True, exist_ok=True)
    pak_tool_dir = base_dir / "PAK TOOL"
    (pak_tool_dir / "EDIT").mkdir(parents=True, exist_ok=True)
    (pak_tool_dir / "UNPACK").mkdir(parents=True, exist_ok=True)
    (pak_tool_dir / "RESULT").mkdir(parents=True, exist_ok=True)
    (pak_tool_dir / "PAK").mkdir(parents=True, exist_ok=True)

def clear_screen():
    if os.name == 'nt':
        os.system('cls')
    else:
        sys.stdout.write('\033[2J\033[H\033[3J')
        sys.stdout.flush()

def print_banner():
    clear_screen()
    console.print("[bold cyan]========================================[/bold cyan]")
    console.print("[bold yellow]    PAK TOOL - UNPACK & REPACK[/bold yellow]")
    console.print("[bold cyan]========================================[/bold cyan]")
    console.print()
    console.print("[bold yellow]TG - @TrnDravix[/bold yellow]")
    console.print("[bold green]🔰 JAI SHREE SHYAM 🔰[/bold green]")
    console.print()

def get_indian_time():
    tz = pytz.timezone("Asia/Kolkata")
    return datetime.now(tz).strftime("%Y-%m-%d %H:%M:%S")

def safe_input(prompt: str='') -> str:
    try:
        return input(prompt)
    except (EOFError, RuntimeError):
        try:
            if sys.platform != 'win32':
                with open('/dev/tty', 'r') as tty:
                    sys.stderr.write(prompt)
                    sys.stderr.flush()
                    return tty.readline().rstrip('\n')
            else:
                with open('CON', 'r') as con:
                    sys.stderr.write(prompt)
                    sys.stderr.flush()
                    return con.readline().rstrip('\r\n')
        except Exception:
            return ''
    except Exception:
        return ''

def human_size(size: int) -> str:
    for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
        if size < 1024.0:
            return f'{size:.2f} {unit}'
        size /= 1024.0
    return f'{size:.2f} PB'

def delete_folder(data_path: Path) -> None:
    folders = []
    for item in data_path.iterdir():
        if item.is_dir() and item.name not in ['PAK', 'UNPACK', 'REPACK', 'RESULT', 'PAK TOOL']:
            folders.append(item)
    if not folders:
        console.print('[bold #FFAA00]⚠ No folders found to delete![/bold #FFAA00]')
        return
    folder_table = Table(title="[bold #FF00FF]📁 AVAILABLE FOLDERS[/bold #FF00FF]", border_style="#00FFFF", box=DOUBLE_EDGE)
    folder_table.add_column("#", justify="center", style="bold #FFFF00", width=4)
    folder_table.add_column("Folder Name", justify="left", style="bold #00FF88")
    folder_table.add_column("Size", justify="right", style="bold #00CCFF")
    for i, folder in enumerate(folders, 1):
        folder_size = 0
        for root, dirs, files in os.walk(folder):
            for file in files:
                file_path = os.path.join(root, file)
                if os.path.isfile(file_path):
                    folder_size += os.path.getsize(file_path)
        folder_table.add_row(str(i), folder.name, human_size(folder_size))
    console.print(folder_table)
    try:
        choice = int(console.input(f"\n[bold #FFFF00]Select folder number (1-{len(folders)}): [/bold #FFFF00]"))
        if 1 <= choice <= len(folders):
            selected_folder = folders[choice - 1]
            confirm = safe_input(f"[bold #FFFF00]Delete {selected_folder.name}? (yes/no): [/bold #FFFF00]").strip().lower()
            if confirm == 'yes':
                shutil.rmtree(selected_folder)
                console.print(f'[bold #00FF88]✅ Deleted: {selected_folder.name}[/bold #00FF88]')
            else:
                console.print('[bold #FFAA00]⚠ Cancelled[/bold #FFAA00]')
        else:
            console.print('[bold #FF0055]❌ Invalid selection[/bold #FF0055]')
    except ValueError:
        console.print('[bold #FF0055]❌ Invalid input[/bold #FF0055]')

def display_file_selector(title, folder_path, file_pattern="*.pak"):
    files = list(folder_path.glob(file_pattern))
    if not files:
        console.print(f"[bold red][ERROR] No {file_pattern} files in {folder_path}[/]")
        return None, None
    selection_table = Table(title=f"[bold cyan]{title}[/]", expand=True, box=ROUNDED, border_style="yellow")
    selection_table.add_column("[bold yellow]#[/]", justify="center", style="bold yellow", width=4)
    selection_table.add_column("[bold green]File Name[/]", justify="left", style="bold bright_green")
    selection_table.add_column("[bold magenta]Size[/]", justify="right", style="bold bright_magenta")
    for i, f in enumerate(files, 1):
        size_mb = f.stat().st_size / (1024 * 1024)
        selection_table.add_row(str(i), f.name, f"{size_mb:.2f} MB")
    console.print(selection_table)
    try:
        idx = int(console.input(f"\n[bold yellow]Select file number (1-{len(files)}): [/]")) - 1
        if idx < 0 or idx >= len(files):
            console.print("[bold red][ERROR] Invalid selection[/]")
            return None, None
        return files[idx], files
    except ValueError:
        console.print("[bold red][ERROR] Please enter a valid number[/]")
        return None, None

# ==================== UNIVERSAL DUMP / OBB / PROTECTION ====================

_DUMP_SKIP_NAMES = {'dump_info.json', '.dravix_guard'}
_OBB_ALIGN = 4096
_GUARD_BANNER = b'\n[PAK TOOL] Protected by @TrnDravix\n'

def _write_dump_info(dest: Path, source: Path):
    info = {
        'source': source.name,
        'size': source.stat().st_size,
        'format': 'unknown',
        'dumped_at': datetime.now().isoformat(timespec='seconds'),
    }
    (dest / 'dump_info.json').write_text(json.dumps(info, indent=2), encoding='utf-8')

def _update_dump_info(dest: Path, fmt: str):
    info_path = dest / 'dump_info.json'
    if info_path.exists():
        info = json.loads(info_path.read_text(encoding='utf-8'))
    else:
        info = {}
    info['format'] = fmt
    file_count = 0
    for _, _, files in os.walk(dest):
        file_count += len(files)
    info['files'] = max(file_count - 1, 0)
    info_path.write_text(json.dumps(info, indent=2, ensure_ascii=False), encoding='utf-8')

def _extract_strings(data: bytes, min_len=4):
    out, buf = [], []
    for b in data:
        if 32 <= b < 127:
            buf.append(chr(b))
        else:
            if len(buf) >= min_len:
                out.append(''.join(buf))
            buf = []
    if len(buf) >= min_len:
        out.append(''.join(buf))
    return out

def _dump_strings_to_file(data: bytes, dest: Path, name='strings.txt'):
    strs = _extract_strings(data)
    if strs:
        (dest / name).write_text('\n'.join(strs), encoding='utf-8')

def _dump_elf(data: bytes, dest: Path) -> bool:
    if len(data) < 16 or data[:4] != b'\x7fELF':
        return False
    (dest / 'format.txt').write_text('ELF', encoding='utf-8')
    ei_class = data[4]
    endian = 'little' if data[5] == 1 else 'big'
    bits = 64 if ei_class == 2 else 32
    hdr_len = 64 if ei_class == 2 else 52
    if len(data) >= hdr_len:
        e_type = int.from_bytes(data[16:18], endian)
        e_machine = int.from_bytes(data[18:20], endian)
    else:
        e_type = e_machine = 0
    (dest / 'elf_info.txt').write_text(
        f'class=ELF{bits}\nendian={endian}\ntype=0x{e_type:04x}\nmachine=0x{e_machine:04x}',
        encoding='utf-8')
    return True

def _dump_lua_chunk(data: bytes, dest: Path) -> bool:
    sig = data[:4]
    if sig not in (b'\x1bLua', b'\x1bLJ'):
        return False
    is_lj = sig == b'\x1bLJ'
    version = data[4]
    (dest / 'format.txt').write_text('LUAJIT' if is_lj else 'LUA', encoding='utf-8')
    (dest / 'lua_version.txt').write_text(
        'LuaJIT' if is_lj else f'Lua 5.{version}', encoding='utf-8')
    return True

def _dump_pak(src: Path, dest: Path) -> bool:
    try:
        pak = TencentPakFile(src)
    except Exception:
        return False
    (dest / 'format.txt').write_text('TENCENT_PAK', encoding='utf-8')
    pak.dump(dest)
    try:
        dump_unpacking_log(pak, dest / f'dump_{src.stem}.log')
    except Exception:
        pass
    return True

def _dump_zip_container(path: Path, dest: Path) -> bool:
    try:
        zin = zipfile.ZipFile(path)
    except Exception:
        return False
    for zi in zin.infolist():
        if zi.is_dir():
            continue
        target = dest / zi.filename
        try:
            target.resolve().relative_to(dest.resolve())
        except ValueError:
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        try:
            target.write_bytes(zin.read(zi))
        except Exception:
            continue
    zin.close()
    return True

def _detect_format_from_head(head: bytes) -> str:
    if head[:2] == b'PK':
        return 'ZIP'
    if head[:4] == b'\x7fELF':
        return 'ELF'
    if head[:4] in (b'\x1bLua', b'\x1bLJ'):
        return 'LUA'
    return 'UNKNOWN'

def _is_protected_file(dump_dir: Path) -> bool:
    guard = dump_dir / '.dravix_guard'
    return guard.exists() and guard.stat().st_size > 0

def dump_universal(source: Path, dump_root: Path) -> Tuple[Path, str]:
    dest = dump_root / source.stem
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    _write_dump_info(dest, source)
    with open(source, 'rb') as f:
        head = f.read(16)
    fmt = _detect_format_from_head(head)
    handled = False
    if fmt == 'ZIP':
        handled = _dump_zip_container(source, dest)
        if handled:
            fmt = 'ZIP_CONTAINER'
    if not handled:
        handled = _dump_pak(source, dest)
        if handled:
            fmt = 'TENCENT_PAK'
    if not handled and fmt == 'ELF':
        data = open(source, 'rb').read()
        handled = _dump_elf(data, dest)
        if handled:
            _dump_strings_to_file(data, dest, 'strings.txt')
            fmt = 'ELF'
    if not handled and fmt == 'LUA':
        data = open(source, 'rb').read()
        handled = _dump_lua_chunk(data, dest)
        if handled:
            _dump_strings_to_file(data, dest, 'strings.txt')
            fmt = 'LUA'
    if not handled:
        shutil.copy2(source, dest / source.name)
        data = open(source, 'rb').read()
        _dump_strings_to_file(data, dest, 'strings.txt')
        fmt = 'RAW_BINARY'
    _update_dump_info(dest, fmt)
    return dest, fmt

def unpack_obb(path: Path, unpack_root: Path) -> Optional[Path]:
    dest = unpack_root / path.stem
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    if _dump_zip_container(path, dest):
        return dest
    try:
        pak = TencentPakFile(path, is_od=True)
        pak.dump(dest)
        dump_unpacking_log(pak, dest / f'dump_{path.stem}.log')
        return dest
    except Exception:
        return None

def _apply_protection_zip(built_zip: Path) -> None:
    tmp_path = built_zip.parent / (built_zip.name + '.tmp')
    try:
        zin = zipfile.ZipFile(built_zip, 'r')
        entries = [(zi, zin.read(zi.filename)) for zi in zin.infolist()]
        zin.close()
    except Exception:
        return
    try:
        with zipfile.ZipFile(tmp_path, 'w', zipfile.ZIP_DEFLATED, compresslevel=6) as zout:
            for zi, data in entries:
                nz = zipfile.ZipInfo(zi.filename)
                nz.compress_type = zi.compress_type
                nz.extra = _zip_align_extra(zout.fp.tell(), zi.filename)
                zout.writestr(nz, data)
            g = zipfile.ZipInfo('.dravix_guard')
            g.compress_type = zipfile.ZIP_STORED
            g.extra = _zip_align_extra(zout.fp.tell(), '.dravix_guard')
            zout.writestr(g, _GUARD_BANNER)
        shutil.move(str(tmp_path), str(built_zip))
    except Exception:
        try:
            tmp_path.unlink()
        except Exception:
            pass

def _apply_protection(out_path: Path) -> None:
    if out_path.suffix.lower() in ('.obb', '.apk', '.zip'):
        _apply_protection_zip(out_path)
    else:
        try:
            with open(out_path, 'ab') as f:
                f.write(_GUARD_BANNER)
        except Exception:
            pass

def _zip_align_extra(cur_pos: int, arcname: str, align: int = _OBB_ALIGN) -> bytes:
    """Local-header padding so a zip entry's data begins on a 4K page:

    Android/zipalign-compatible: the local file header is written with an
    enlarged Extra Field (zerofilled) so the file DATA starts at a 4096-byte
    boundary inside the container. Page-aligned data lets the OS memory-map
    asset regions directly (no stutter for audio/texture/blob files).
    """
    name_b = arcname.encode('utf-8')
    pad = (-(cur_pos + 30 + len(name_b))) % align
    return b'\x00' * pad

def _repack_obb_aligned(unpack_dir: Path, out: Path) -> bool:
    """Build a .obb as a DEFLATED (level 6) zip with every file's data
    4096-aligned. Original ZIP_STORED behaviour ballooned the container;
    DEFLATED keeps huge audio/texture assets small while page alignment keeps
    loads instant on Android."""
    with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED, compresslevel=6) as zout:
        for root, _, files in os.walk(unpack_dir):
            for fn in files:
                full = Path(root) / fn
                rel = full.relative_to(unpack_dir)
                zinfo = zipfile.ZipInfo(rel.as_posix())
                zinfo.compress_type = zipfile.ZIP_DEFLATED
                zinfo.extra = _zip_align_extra(zout.fp.tell(), rel.as_posix())
                with open(full, 'rb') as f:
                    with zout.open(zinfo, 'w') as dst:
                        shutil.copyfileobj(f, dst)
        g = zipfile.ZipInfo('.dravix_guard')
        g.compress_type = zipfile.ZIP_STORED
        g.extra = _zip_align_extra(zout.fp.tell(), '.dravix_guard')
        zout.writestr(g, _GUARD_BANNER)
    return True

def repack_obb(unpack_dir: Path, out_root: Path) -> Optional[Path]:
    out = out_root / (unpack_dir.name + '.obb')
    try:
        _repack_obb_aligned(unpack_dir, out)
        return out
    except Exception:
        return None

def _clean_for_repack(dump_dir: Path, clean_root: Path) -> Path:
    clean = clean_root / dump_dir.name
    if clean.exists():
        shutil.rmtree(clean)
    shutil.copytree(dump_dir, clean)
    for pattern in [('.dravix_guard',), ('dump_info.json',), ('*.log',)]:
        for item in clean.rglob(pattern[0]):
            if item.exists() and item.is_file():
                item.unlink()
    return clean

def repack_from_dump(dump_dir: Path, result_root: Path,
                     original_search_dirs: List[Path]) -> Tuple[bool, str]:
    if _is_protected_file(dump_dir):
        return False, 'Dump is protected by anti-dump marker — cannot repack.'
    info_path = dump_dir / 'dump_info.json'
    fmt = 'UNKNOWN'
    if info_path.exists():
        info = json.loads(info_path.read_text(encoding='utf-8'))
        fmt = info.get('format', 'UNKNOWN').upper()
    clean = _clean_for_repack(dump_dir, result_root / '_repack_tmp')
    try:
        if fmt == 'TENCENT_PAK':
            orig = None
            for p in original_search_dirs:
                cand = p / (dump_dir.name + '.pak')
                if cand.exists():
                    orig = cand
                    break
            if orig is None:
                return False, f'No original .pak found for {dump_dir.name}'
            pak = TencentPakFile(orig)
            out = result_root / (dump_dir.name + '.pak')
            repack_pak_file_full(pak, clean, out)
            return True, str(out)
        elif fmt in ('ZIP_CONTAINER', 'RAW_BINARY'):
            out = result_root / (dump_dir.name + '.zip')
            with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED, compresslevel=6) as zout:
                for root, _, files in os.walk(clean):
                    for fn in files:
                        full = Path(root) / fn
                        rel = full.relative_to(clean)
                        zinfo = zipfile.ZipInfo(rel.as_posix())
                        zinfo.compress_type = zipfile.ZIP_DEFLATED
                        zinfo.extra = _zip_align_extra(zout.fp.tell(), rel.as_posix())
                        with open(full, 'rb') as f:
                            with zout.open(zinfo, 'w') as dst:
                                shutil.copyfileobj(f, dst)
                g = zipfile.ZipInfo('.dravix_guard')
                g.compress_type = zipfile.ZIP_STORED
                g.extra = _zip_align_extra(zout.fp.tell(), '.dravix_guard')
                zout.writestr(g, _GUARD_BANNER)
            return True, str(out)
        else:
            return False, f'Unknown dump format "{fmt}" — cannot determine repack strategy.'
    finally:
        shutil.rmtree(result_root / '_repack_tmp', ignore_errors=True)

# ==================== COMPRESSION / ALIGNMENT OPTIMISATION ====================

_ZSTD_FAST_LEVELS = (6, 3)

# ==================== LUA / ASSET ANTI-DUMP PROTECTION ====================
#
# Strip debug information (line numbers, local-variable tables, upvalue names)
# from Lua 5.3 / 5.4 compiled chunks before writing them back into the PAK --
# the same effect as `luac -s` -- so memory dumpers can't harvest symbols, while
# the chunk stays 100% engine-compatible (valid TencentPak headers/checksums and
# a byte-exact header + code + constants + upvalues + nested prototypes).

def _minify_lua_source(data: bytes) -> bytes:
    """Safely minify plain-text Lua source (strip comments / blank lines).

    Only strips comments and leading whitespace; string & long-string contents
    are preserved verbatim so semantics never change.
    """
    try:
        src = data.decode('utf-8', errors='surrogateescape')
    except Exception:
        return data
    out = []
    i, n = 0, len(src)
    state = 'code'      # code | squote | dquote | longstr | linecom | blockcom
    depth = 0
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ''
        if state == 'code':
            if c == '-' and nxt == '-':
                peep = src[i + 2] if i + 2 < n else ''
                if peep == '[':
                    eq = 0
                    j = i + 3
                    while j < n and src[j] == '=':
                        eq += 1
                        j += 1
                    if j < n and src[j] == '[':
                        state = 'blockcom'
                        depth = eq
                        i = j + 1
                        continue
                state = 'linecom'
                i += 2
                continue
            if c == "'":
                state = 'squote'
            elif c == '"':
                state = 'dquote'
            elif c == '[':
                eq = 0
                j = i + 1
                while j < n and src[j] == '=':
                    eq += 1
                    j += 1
                if j < n and src[j] == '[':
                    state = 'longstr'
                    depth = eq
                    out.append(c)
                    out.append('=' * eq)
                    out.append('[')
                    i = j + 1
                    continue
            out.append(c)
            i += 1
        elif state in ('squote', 'dquote'):
            out.append(c)
            if c == '\\':
                if i + 1 < n:
                    out.append(src[i + 1])
                    i += 2
                    continue
            elif c == state[0]:
                state = 'code'
            i += 1
        elif state == 'longstr':
            out.append(c)
            if c == ']':
                neq = 0
                j = i + 1
                while j < n and src[j] == '=':
                    neq += 1
                    j += 1
                if neq == depth and j < n and src[j] == ']':
                    out.append('=' * depth)
                    out.append(']')
                    state = 'code'
                    i = j + 1
                    continue
            i += 1
        elif state == 'linecom':
            if c == '\n':
                state = 'code'
            i += 1
        elif state == 'blockcom':
            if i + 1 < n and c == ']' and src[i + 1] == ']':
                state = 'code'
                i += 2
                continue
            if i + 1 < n and c == ']' and src[i + 1] == '=':
                neq = 0
                j = i + 1
                while j < n and src[j] == '=':
                    neq += 1
                    j += 1
                if neq == depth and j < n and src[j] == ']':
                    state = 'code'
                    i = j + 1
                    continue
            i += 1
    try:
        return ''.join(out).encode('utf-8')
    except Exception:
        return data


class _LuaChunk:
    """Minimal Lua 5.3 / 5.4 chunk reader + stripped re-serialiser (luac -s)."""

    def __init__(self, data: bytes):
        self._src = data
        self._ver = None
        self._header = b''
        self._endian = '<'
        self._main = None
        self._linfo_n = None
        self._li_size = 8
        self._num_size = 8

    # ---------- low-level readers ----------
    def _ra(self, n):
        p, self._pos = self._pos, self._pos + n
        blob = self._src[p:p + n]
        if len(blob) != n:
            raise ValueError('truncated chunk')
        return blob

    def _u8(self):
        return self._ra(1)[0]

    def _i(self):
        b = self._ra(4)
        return int.from_bytes(b, 'little' if self._endian == '<' else 'big', signed=True)

    def _ivec(self):
        x = 0
        while True:
            b = self._u8()
            x = (x << 7) | (b & 0x7f)
            if b & 0x80:
                break
        return x

    def _int64(self):
        b = self._ra(8)
        return int.from_bytes(b, 'little' if self._endian == '<' else 'big', signed=True)

    def _num(self):
        b = self._ra(8)
        return struct.unpack('<d' if self._endian == '<' else '>d', b)[0]

    # ---------- strings ----------
    def _gstr(self):
        if self._ver == 0x54:
            size = self._ivec()
        elif self._ver == 0x53:
            size = self._u8()
            if size == 0xFF:
                size = int.from_bytes(self._ra(8), self._endian)
        else:
            raise ValueError(f'unsupported lua version 0x{self._ver:02x}')
        if size == 0:
            return None
        return self._ra(size - 1)

    # ---------- constants ----------
    def _gconstant(self):
        t = self._u8()
        if self._ver == 0x54:
            if t == 0: return ('nil',)
            if t == 1: return ('bool', False)
            if t == 0x11: return ('bool', True)
            if t == 3: return ('num', self._num())
            if t == 0x13: return ('int', self._int64())
            if t in (4, 0x14): return ('str', self._gstr())
            raise ValueError(f'bad constant tag 0x{t:02x}')
        else:
            if t == 0: return ('nil',)
            if t == 1: return ('bool', self._u8() != 0)
            if t == 3: return ('num', self._num())
            if t == 0x13: return ('int', int.from_bytes(
                self._ra(self._li_size), 'little' if self._endian == '<' else 'big', signed=True))
            if t in (4, 0x14): return ('str', self._gstr())
            raise ValueError(f'bad constant tag 0x{t:02x}')

    # ---------- function ----------
    def _gfunc(self):
        src = self._gstr()
        if self._ver == 0x54:
            line_def = self._ivec()
            line_last = self._ivec()
        else:
            line_def = self._i()
            line_last = self._i()
        numparams = self._u8()
        is_vararg = self._u8()
        maxstack = self._u8()
        ncode = self._iv_or_i()
        code = [self._u32le() for _ in range(ncode)]
        nk = self._iv_or_i()
        k = [self._gconstant() for _ in range(nk)]
        nup = self._iv_or_i()
        if self._ver == 0x54:
            up = [((self._u8(), self._u8(), self._u8())) for _ in range(nup)]
        else:
            up = [((self._u8(), self._u8())) for _ in range(nup)]
        np = self._iv_or_i()
        protos = [self._gfunc() for _ in range(np)]
        # ---- debug (read & discard) ----
        if self._ver == 0x54:
            nli = self._ivec(); self._ra(nli)
            nabs = self._ivec()
            for _ in range(nabs):
                self._ivec(); self._ivec()
        else:
            nli = self._i(); self._ra(nli * 4)
        nlv = self._iv_or_i()
        for _ in range(nlv):
            self._gstr(); self._iv_or_i(); self._iv_or_i()
        nuv = self._iv_or_i()
        if self._ver == 0x54:
            if nuv != 0:
                nuv = nup
            for _ in range(nuv):
                self._gstr()
        else:
            for _ in range(nuv):
                self._gstr()
        self._linfo_n = nli
        return {
            'source': src, 'linedefined': line_def, 'lastlinedefined': line_last,
            'numparams': numparams, 'is_vararg': is_vararg, 'maxstacksize': maxstack,
            'code': code, 'k': k, 'upvalues': up, 'protos': protos,
        }

    def _iv_or_i(self):
        return self._ivec() if self._ver == 0x54 else self._i()

    def _u32le(self):
        return int.from_bytes(self._ra(4), 'little')

    # ---------- top-level ----------
    def parse(self):
        d = self._src
        if d[:4] != b'\x1bLua':
            raise ValueError('not a lua chunk')
        self._ver = d[4]
        if self._ver not in (0x53, 0x54):
            raise ValueError(f'unsupported lua version 0x{self._ver:02x}')
        if self._ver == 0x54:
            self._pos = 12                      # magic4 + ver + fmt + LUAC_DATA(6)
            self._endian = '<'
            self._ra(1); self._ra(1); self._ra(1)   # instr/int/number sizes
            self._ra(8)                          # LUAC_INT (lua_Integer)
            self._ra(8)                          # LUAC_NUM (double)
            self._header = d[:self._pos]
            self._pos = len(self._header)
            self._ra(1)                          # main nupvalues byte
        else:                                    # 5.3
            self._pos = 12
            self._endian = '<'
            self._ra(1)                          # sizeof(int)
            self._ra(1)                          # sizeof(size_t)
            self._ra(1)                          # sizeof(Instruction)
            self._li_size = self._u8()           # sizeof(lua_Integer)
            self._num_size = self._u8()          # sizeof(lua_Number)
            self._ra(self._li_size)              # LUAC_INT
            self._ra(self._num_size)             # LUAC_NUM
            self._header = d[:self._pos]
            self._pos = len(self._header)
            self._ra(1)                          # nupvalues byte
        self._main = self._gfunc()
        if self._pos != len(d):
            raise ValueError(f'trailing bytes: {len(d) - self._pos}')
        return self._main

    # ---------- low-level writers ----------
    @staticmethod
    def _w_u8(buf, v):
        buf.append(v & 0xFF)

    @staticmethod
    def _w_i(buf, v, endian='<'):
        bo = 'little' if endian == '<' else 'big'
        buf += int(v).to_bytes(4, bo, signed=True)

    @staticmethod
    def _w_ivec(buf, v):
        if v < 0:
            raise ValueError('negative varint')
        groups = []
        while True:
            groups.append(v & 0x7F)
            v >>= 7
            if not v:
                break
        for idx in range(len(groups) - 1, -1, -1):
            buf.append(groups[idx] | (0x80 if idx == 0 else 0))

    @staticmethod
    def _w_int64(buf, v, endian='<'):
        bo = 'little' if endian == '<' else 'big'
        buf += int(v).to_bytes(8, bo, signed=True)

    @staticmethod
    def _w_num(buf, v, endian='<'):
        buf += struct.pack('<d' if endian == '<' else '>d', float(v))

    def _wstr(self, buf, s):
        if self._ver == 0x54:
            self._w_ivec(buf, 0 if s is None else len(s) + 1)
        else:
            if s is None:
                self._w_u8(buf, 0)
            else:
                size = len(s) + 1
                if size < 0xFF:
                    self._w_u8(buf, size)
                else:
                    self._w_u8(buf, 0xFF)
                    buf += size.to_bytes(8, self._endian)
        if s:
            buf += s

    def _wconst(self, buf, c):
        tag = c[0]
        if self._ver == 0x54:
            if tag == 'nil':
                self._w_u8(buf, 0)
            elif tag == 'bool':
                self._w_u8(buf, 0x11 if c[1] else 1)
            elif tag == 'num':
                self._w_u8(buf, 3); self._w_num(buf, c[1])
            elif tag == 'int':
                self._w_u8(buf, 0x13); self._w_int64(buf, c[1])
            elif tag == 'str':
                self._w_u8(buf, 4); self._wstr(buf, c[1])
        else:
            if tag == 'nil':
                self._w_u8(buf, 0)
            elif tag == 'bool':
                self._w_u8(buf, 1); self._w_u8(buf, 1 if c[1] else 0)
            elif tag == 'num':
                self._w_u8(buf, 3); self._w_num(buf, c[1])
            elif tag == 'int':
                self._w_u8(buf, 0x13)
                buf += int(c[1]).to_bytes(self._li_size, 'little' if self._endian == '<' else 'big', signed=True)
            elif tag == 'str':
                self._w_u8(buf, 4); self._wstr(buf, c[1])
        return buf

    def _wfunc(self, buf, f):
        self._wstr(buf, f['source'])
        if self._ver == 0x54:
            self._w_ivec(buf, f['linedefined'])
            self._w_ivec(buf, f['lastlinedefined'])
        else:
            self._w_i(buf, f['linedefined'])
            self._w_i(buf, f['lastlinedefined'])
        self._w_u8(buf, f['numparams'])
        self._w_u8(buf, f['is_vararg'])
        self._w_u8(buf, f['maxstacksize'])
        self._wrap_count(buf, len(f['code']))
        for ins in f['code']:
            buf += ins.to_bytes(4, 'little')
        self._wrap_count(buf, len(f['k']))
        for c in f['k']:
            self._wconst(buf, c)
        self._wrap_count(buf, len(f['upvalues']))
        for u in f['upvalues']:
            for b in u:
                self._w_u8(buf, b)
        self._wrap_count(buf, len(f['protos']))
        for p in f['protos']:
            self._wfunc(buf, p)
        # ---- debug section stripped (zero counts) ----
        if self._ver == 0x54:
            self._w_ivec(buf, 0)   # lineinfo
            self._w_ivec(buf, 0)   # abslineinfo
        else:
            self._w_i(buf, 0)      # lineinfo
        self._wrap_count(buf, 0)   # locvars
        self._wrap_count(buf, 0)   # upvalue names

    def _wrap_count(self, buf, v):
        if self._ver == 0x54:
            self._w_ivec(buf, v)
        else:
            self._w_i(buf, v)

    def rebuild(self):
        buf = bytearray(self._header)
        nup = len(self._main['upvalues'])
        if self._ver == 0x54:
            self._w_ivec(buf, nup)
        else:
            self._w_u8(buf, nup)
        self._wfunc(buf, self._main)
        return bytes(buf)


def _tree_sig(p):
    return (
        p['numparams'], p['is_vararg'], p['maxstacksize'], tuple(p['code']),
        tuple(p['k']), tuple(tuple(x) for x in p['upvalues']),
        tuple(_tree_sig(x) for x in p['protos']),
    )


def _strip_lua_debug(data: bytes):
    """Return a debug-stripped Lua 5.3/5.4 chunk, or None if it can't be
    safely stripped (unrecognised version / parse failure / round-trip mismatch).
    """
    if data[:4] != b'\x1bLua':
        return None
    try:
        c1 = _LuaChunk(data)
        c1.parse()
    except Exception:
        return None
    if c1._ver not in (0x53, 0x54):
        return None
    sig1 = _tree_sig(c1._main)
    out = c1.rebuild()
    if out == data or len(out) >= len(data):
        return None
    try:
        c2 = _LuaChunk(out)
        c2.parse()
    except Exception:
        return None
    if _tree_sig(c2._main) != sig1:
        return None
    return out


def _harden_asset_for_repack(rel_name, data: bytes) -> bytes:
    """Apply anti-dump hardening to Lua assets before repack.

    Compiled Lua chunks -> luac -s style debug strip (safe, engine-compatible).
    Plain-text Lua     -> comment/whitespace stripping.
    Everything else untouched.
    """
    low = (rel_name or '').lower()
    if data[:4] == b'\x1bLua':
        stripped = _strip_lua_debug(data)
        return stripped if stripped is not None else data
    is_lua_source = data[:4] not in (b'\x1bLua', b'\x1bLJ') and (
        low.endswith('.lua') or low.endswith('.luac') or low.endswith('.luac.bytes')
    )
    if is_lua_source:
        try:
            minified = _minify_lua_source(data)
            return minified if len(minified) < len(data) else data
        except Exception:
            return data
    return data


def generate_hardened_so(base_dir):
    """Generate a script-hardening kit: dravix.py -> Cython C-extension -> stripped .so
    -> AES-256 encrypted artifact (anti-decompile).

    Builds locally when cython + a compiler are available; otherwise hands off to
    the cloud workflow (.github/workflows/harden.yml) so devices with no toolchain
    can still produce the hardened build.
    """
    import subprocess as _sp
    hdir = base_dir / 'HARDEN'
    hdir.mkdir(parents=True, exist_ok=True)
    (hdir / 'setup_dravix.py').write_text(
        'from setuptools import setup, Extension\n'
        'from Cython.Build import cythonize\n'
        'setup(\n'
        '    ext_modules=cythonize(\n'
        '        "dravix_hardening.py",\n'
        "        compiler_directives={'language_level': 3},\n"
        '        nthreads=2, quiet=True,\n'
        '    ),\n'
        "    script_args=['build_ext', '--inplace'],\n"
        ')\n',
        encoding='utf-8')
    script_path = hdir / 'build_hardened.sh'
    script_path.write_text(
        '''#!/usr/bin/env bash
# ============================================================
#  PAK TOOL - SCRIPT HARDENING GENERATOR  (@TrnDravix)
#  dravix.py -> Cython .so -> stripped -> AES-256 encrypted
#  Launch the hardened build with:
#    python -c "import dravix_hardening as __tool; __tool.main_menu()"
# ============================================================
set -e
cd "$(dirname "$0")"
cp -f ../dravix.py ./dravix_hardening.py
python -m pip install --quiet --upgrade pip setuptools wheel cython
python -m pip install --quiet rich pycryptodome zstandard requests pytz gmalg
python setup_dravix.py build_ext --inplace
SO=$(ls dravix_hardening*.so 2>/dev/null | head -n1)
if [ -z "$SO" ]; then echo "ERROR: no .so produced"; exit 1; fi
strip --strip-unneeded "$SO" 2>/dev/null || true
python -c "import dravix_hardening; print('HARDENED MODULE OK')"
KEY=$(python - <<'PY'
import secrets, base64
print(base64.b64encode(secrets.token_bytes(32)).decode())
PY
)
python - "$SO" "$KEY" <<'PY'
import sys
from Crypto.Cipher import AES
from Crypto.Protocol.KDF import PBKDF2
so, key = sys.argv[1], sys.argv[2]
data = open(so, 'rb').read()
derived = PBKDF2(key.encode(), b'TrnDravixPAKTool', 32, count=10000)
cipher = AES.new(derived, AES.MODE_EAX)
ct, tag = cipher.encrypt_and_digest(data)
with open('dravix_hardened.so.enc', 'wb') as f:
    f.write(cipher.nonce + tag + ct)
print('AES-256-EAX encrypted -> dravix_hardened.so.enc')
PY
printf '%s\\n' "$KEY" > dravix_hardened.key
echo "HARDENED BUILD COMPLETE - KEY: $KEY"
ls -la dravix_hardening*.so dravix_hardened.so.enc dravix_hardened.key
''',
        encoding='utf-8')
    script_path.chmod(0o755)
    console.print(f'[bold #00FF88]✅ Hardening kit created in HARDEN/[/bold #00FF88]')
    console.print('[dim](build_hardened.sh + setup_dravix.py → dravix_hardened.so.enc)[/dim]')
    try:
        import importlib as _implib
        has_cython = _implib.util.find_spec('cython') is not None
    except Exception:
        has_cython = False
    if has_cython:
        console.print('[bold cyan]⚙ Cython detected — attempting local build...[/bold cyan]')
        try:
            r = _sp.run(['bash', str(script_path)], cwd=str(hdir),
                        capture_output=True, text=True, timeout=900)
        except Exception as e:
            console.print(f'[bold #FF0055]❌ Local build error: {escape(str(e))}[/bold #FF0055]')
            return
        if r.returncode == 0:
            console.print('[bold #00FF88]✅ Hardened .so built locally (see HARDEN/).[/bold #00FF88]')
            for line in r.stdout.splitlines():
                console.print('[dim]' + (escape(line) if len(line) < 130 else escape(line[:127]) + '...') + '[/dim]')
        else:
            console.print('[bold #FF0055]❌ Local build failed — use the cloud workflow instead.[/bold #FF0055]')
            for line in r.stderr.splitlines()[-20:]:
                console.print(f'[dim #FF8888]{escape(line)}[/dim #FF8888]')
    else:
        console.print('[bold #FFFF00]⚠ Cython not installed — push repo & run the "harden" workflow.[/bold #FFFF00]')
        console.print('[dim]Actions tab → "Script Hardening" → Run workflow → download hardened-dravix artifact.[/dim]')


def main_menu():
    if getattr(sys, 'frozen', False):
        data_path = Path(sys.executable).parent
    else:
        data_path = Path(__file__).parent
    ensure_directories(data_path)
    input_dir = data_path / 'INPUT'
    dump_root = data_path / 'DUMP'
    unpack_root = data_path / 'UNPACK'
    result_root = data_path / 'RESULT'
    pak_dir = data_path / 'PAK'
    pak_tool_dir = data_path / 'PAK TOOL'
    while True:
        print_banner()
        console.print("[bold cyan]╔══════════════════════════════════════╗[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold yellow]          MAIN MENU[/bold yellow]                [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]╠══════════════════════════════════════╣[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 1. UNIVERSAL DUMP[/bold white]  [dim](INPUT/)[/dim]        [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 2. REPACK FROM DUMP[/bold white] [dim](DUMP/)[/dim]       [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 3. OBB UNPACK[/bold white]  [dim](INPUT/)[/dim]           [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 4. OBB REPACK[/bold white] [dim](UNPACK/)[/dim]          [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 5. UNPACK ALL TYPES PAKS[/bold white]  [dim](PAK/)[/dim]  [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 6. REPACK ALL TYPES PAKS[/bold white] [dim](PAK/)[/dim] [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 7. REPACK ANY SIZE[/bold white] [dim](PAK TOOL/)[/dim]     [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 8. REPACK TO PATH[/bold white] [dim](PAK TOOL/)[/dim]     [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 9. DELETE FOLDER[/bold white]                 [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] H. HARDEN SCRIPT[/bold white] [dim](→ .so)[/dim]         [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]║[/bold cyan] [bold white] 0. EXIT[/bold white]                         [bold cyan]║[/bold cyan]")
        console.print("[bold cyan]╚══════════════════════════════════════╝[/bold cyan]")
        console.print()
        choice = safe_input('[bold yellow]ENTER CHOICE: [/bold yellow]').strip()

        if choice == '1':
            inputs = [f for f in input_dir.iterdir() if f.is_file()]
            if not inputs:
                console.print('[bold #FFAA00]⚠ No files in INPUT/ — place files there first.[/bold #FFAA00]')
                safe_input('\nPress Enter to continue...')
                continue
            table = Table(title=f"[bold cyan]📁 FILES IN INPUT/ ({len(inputs)} found)[/bold cyan]",
                          border_style="#00FFFF", box=DOUBLE_EDGE)
            table.add_column("#", justify="center", style="bold #FFFF00", width=4)
            table.add_column("File Name", justify="left", style="bold #00FF88")
            table.add_column("Size", justify="right", style="bold #00CCFF")
            for i, f in enumerate(inputs, 1):
                table.add_row(str(i), f.name, human_size(f.stat().st_size))
            table.add_row("0", "[bold #FFFF00]DUMP ALL FILES[/bold #FFFF00]", f"[bold #FFFF00]{len(inputs)} files[/bold #FFFF00]")
            console.print(table)
            try:
                sel = int(console.input('\n[bold #FFFF00]Select file number to dump: [/bold #FFFF00]'))
            except ValueError:
                sel = -1
            if sel == 0:
                chosen = inputs
                console.print(f'[bold cyan]🚀 Dumping ALL {len(inputs)} file(s)...[/bold cyan]')
            elif 1 <= sel <= len(inputs):
                chosen = [inputs[sel - 1]]
            else:
                console.print('[bold #FF0055]❌ Invalid selection![/bold #FF0055]')
                safe_input('\nPress Enter to continue...')
                continue
            success, fail = 0, 0
            for src in chosen:
                try:
                    dest, fmt = dump_universal(src, dump_root)
                    console.print(f'[bold green]✅ {src.name} → {fmt} → {dest.name}/[/bold green]')
                    success += 1
                except Exception as e:
                    console.print(f'[bold red]❌ {src.name}: {escape(str(e))}[/bold red]')
                    fail += 1
            console.print(f'\n[bold cyan]📊 Dumped: {success}  Failed: {fail}[/bold cyan]')
            safe_input('\nPress Enter to continue...')

        elif choice == '2':
            dumps = [d for d in dump_root.iterdir() if d.is_dir()]
            if not dumps:
                console.print('[bold #FFAA00]⚠ No dump folders in DUMP/ — run Universal Dump first.[/bold #FFAA00]')
                safe_input('\nPress Enter to continue...')
                continue
            console.print('[bold cyan]📁 Dump folders:[/bold cyan]')
            for i, d in enumerate(dumps, 1):
                info = ''
                info_path = d / 'dump_info.json'
                if info_path.exists():
                    try:
                        info = json.loads(info_path.read_text(encoding='utf-8')).get('format', '')
                    except Exception:
                        pass
                console.print(f'  {i}. {d.name} [dim]({info})[/dim]')
            try:
                idx = int(console.input('[bold yellow]Select dump number: [/bold yellow]')) - 1
                if not (0 <= idx < len(dumps)):
                    console.print('[bold red]❌ Invalid[/bold red]')
                    safe_input('\nPress Enter to continue...')
                    continue
            except ValueError:
                console.print('[bold red]❌ Invalid[/bold red]')
                safe_input('\nPress Enter to continue...')
                continue
            selected = dumps[idx]
            ok, msg = repack_from_dump(selected, result_root,
                                       [input_dir, pak_dir])
            if ok:
                console.print(f'[bold green]✅ Repacked → {msg}[/bold green]')
            else:
                console.print(f'[bold red]❌ Repack failed: {msg}[/bold red]')
            safe_input('\nPress Enter to continue...')

        elif choice == '3':
            obb_files = [f for f in input_dir.iterdir()
                         if f.is_file() and f.suffix.lower() == '.obb']
            if not obb_files:
                console.print('[bold #FFAA00]⚠ No .obb files in INPUT/[/bold #FFAA00]')
                safe_input('\nPress Enter to continue...')
                continue
            console.print(f'[bold cyan]Found {len(obb_files)} .obb file(s)[/bold cyan]')
            for src in obb_files:
                try:
                    dest = unpack_obb(src, unpack_root)
                    if dest:
                        console.print(f'[bold green]✅ {src.name} → {dest.name}/[/bold green]')
                    else:
                        console.print(f'[bold yellow]⚠ {src.name}: Could not extract[/bold yellow]')
                except Exception as e:
                    console.print(f'[bold red]❌ {src.name}: {escape(str(e))}[/bold red]')
            safe_input('\nPress Enter to continue...')

        elif choice == '4':
            unpacks = [d for d in unpack_root.iterdir() if d.is_dir()]
            if not unpacks:
                console.print('[bold #FFAA00]⚠ No folders in UNPACK/ — run OBB Unpack first.[/bold #FFAA00]')
                safe_input('\nPress Enter to continue...')
                continue
            console.print('[bold cyan]📁 Unpacked folders:[/bold cyan]')
            for i, d in enumerate(unpacks, 1):
                console.print(f'  {i}. {d.name}')
            try:
                idx = int(console.input('[bold yellow]Select folder number: [/bold yellow]')) - 1
                if not (0 <= idx < len(unpacks)):
                    console.print('[bold red]❌ Invalid[/bold red]')
                    safe_input('\nPress Enter to continue...')
                    continue
            except ValueError:
                console.print('[bold red]❌ Invalid[/bold red]')
                safe_input('\nPress Enter to continue...')
                continue
            try:
                out = repack_obb(unpacks[idx], result_root)
                if out:
                    console.print(f'[bold green]✅ Repacked → {out}[/bold green]')
                else:
                    console.print('[bold red]❌ Repack failed[/bold red]')
            except Exception as e:
                console.print(f'[bold red]❌ {escape(str(e))}[/bold red]')
            safe_input('\nPress Enter to continue...')

        elif choice == '5':
            if not pak_dir.exists():
                console.print(f"[bold red]ERROR: PAK folder not found at {pak_dir}[/bold red]")
                safe_input('\nPress Enter to continue...')
                continue
            pak_file, _ = display_file_selector("📁 Available .pak files to UNPACK:", pak_dir)
            if not pak_file:
                safe_input('\nPress Enter to continue...')
                continue
            try:
                console.print(f'[bold #00FFFF]🚀 Unpacking {pak_file.name}...[/bold #00FFFF]')
                pak = TencentPakFile(pak_file)
                unpack_path = data_path / "UNPACK" / pak_file.stem
                repack_path = data_path / "REPACK" / pak_file.stem
                pak.dump(unpack_path)
                log_path = unpack_path / f'Debug_{pak_file.stem}.log'
                dump_unpacking_log(pak, log_path)
                for dir_path, _ in pak._index.items():
                    (repack_path / pak._mount_point / dir_path).mkdir(parents=True, exist_ok=True)
                console.print(f'[bold #00FF88]✅ SUCCESS: Extracted to {unpack_path}[/bold #00FF88]')
            except Exception as e:
                console.print(f'[bold #FF0055]❌ Error: {escape(str(e))}[/bold #FF0055]')
            safe_input('\nPress Enter to continue...')

        elif choice == '6':
            if not pak_dir.exists():
                console.print(f"[bold red]ERROR: PAK folder not found at {pak_dir}[/bold red]")
                safe_input('\nPress Enter to continue...')
                continue
            pak_file, _ = display_file_selector("📁 Available .pak files to REPACK:", pak_dir)
            if not pak_file:
                safe_input('\nPress Enter to continue...')
                continue
            repack_dir = data_path / "REPACK" / pak_file.stem
            if not repack_dir.exists():
                console.print(f'[bold #FF0055]❌ ERROR: {repack_dir} not found.[/bold #FF0055]')
                console.print('[#FFAA00]⚠ Please unpack first using option 5.[/#FFAA00]')
                safe_input('\nPress Enter to continue...')
                continue
            try:
                console.print(f'[bold #00FFFF]🚀 Repacking {pak_file.name}...[/bold #00FFFF]')
                pak = TencentPakFile(pak_file)
                output_pak = result_root / pak_file.name
                mode = detect_repack_mode(pak_file)
                if mode == 'MINI_OBB':
                    repack_mini_obb(pak, repack_dir, output_pak)
                elif mode == 'GAMEPATCH':
                    repack_gamepatch(pak, repack_dir, output_pak)
                else:
                    repack_obbzsdic(pak, repack_dir, output_pak)
                console.print('[bold #00FF88]✅ REPACK COMPLETED SUCCESSFULLY![/bold #00FF88]')
            except Exception as e:
                console.print(f'[bold #FF0055]❌ Repack failed:[/bold #FF0055] {e}')
                import traceback
                traceback.print_exc()
            safe_input('\nPress Enter to continue...')

        elif choice == '7':
            edit_dir = pak_tool_dir / 'EDIT'
            result_dir = pak_tool_dir / 'RESULT'
            if not pak_dir.exists():
                console.print(f"[bold red]ERROR: PAK folder not found at {pak_dir}[/bold red]")
                safe_input('\nPress Enter to continue...')
                continue
            pak_file, _ = display_file_selector("📁 Available .pak files to REPACK (EXISTING):", pak_dir)
            if not pak_file:
                safe_input('\nPress Enter to continue...')
                continue
            if not edit_dir.exists() or not any(edit_dir.iterdir()):
                console.print(f'[bold #FF0055]❌ ERROR: No files in EDIT folder.[/bold #FF0055]')
                console.print('[#FFAA00]⚠ Place edited files in PAK TOOL/EDIT/.[/#FFAA00]')
                safe_input('\nPress Enter to continue...')
                continue
            try:
                console.print(f'[bold #00FFFF]🚀 Repacking {pak_file.name} (ANY SIZE)...[/bold #00FFFF]')
                pak = TencentPakFile(pak_file)
                output_pak = result_dir / pak_file.name
                count = repack_pak_file_full(pak, edit_dir, output_pak)
                if count > 0:
                    console.print(f'[bold #00FF88]✅ Repacked {count} files → {output_pak}[/bold #00FF88]')
                else:
                    console.print('[bold #FF0055]❌ No files repacked![/bold #FF0055]')
            except Exception as e:
                console.print(f'[bold #FF0055]❌ Repack failed:[/bold #FF0055] {e}')
                import traceback
                traceback.print_exc()
            safe_input('\nPress Enter to continue...')

        elif choice == '8':
            edit_dir = pak_tool_dir / 'EDIT'
            result_dir = pak_tool_dir / 'RESULT'
            if not pak_dir.exists():
                console.print(f"[bold red]ERROR: PAK folder not found at {pak_dir}[/bold red]")
                safe_input('\nPress Enter to continue...')
                continue
            pak_file, _ = display_file_selector("📁 Available .pak files to REPACK TO PATH:", pak_dir)
            if not pak_file:
                safe_input('\nPress Enter to continue...')
                continue
            if not edit_dir.exists() or not any(edit_dir.iterdir()):
                console.print(f'[bold #FF0055]❌ ERROR: No files in EDIT folder.[/bold #FF0055]')
                console.print('[#FFAA00]⚠ Place files to add in PAK TOOL/EDIT/.[/#FFAA00]')
                safe_input('\nPress Enter to continue...')
                continue
            console.print('[bold #FFFF00]📁 Enter target path inside the PAK:[/bold #FFFF00]')
            console.print('[dim]Example: Content/Lua/GameLua/Mod/BRMod/Gameplay/Core[/dim]')
            target_path = safe_input('[bold #00FFFF]Path: [/bold #00FFFF]').strip()
            if not target_path:
                console.print('[bold #FF0055]❌ No path provided![/bold #FF0055]')
                safe_input('\nPress Enter to continue...')
                continue
            target_path = target_path.replace('\\', '/').strip('/')
            try:
                console.print(f'[bold #00FFFF]🚀 Adding to {target_path} in {pak_file.name}...[/bold #00FFFF]')
                pak = TencentPakFile(pak_file)
                output_pak = result_dir / pak_file.name
                count = repack_pak_file_full(pak, edit_dir, output_pak, target_path, force_add=True)
                if count > 0:
                    console.print(f'[bold #00FF88]✅ {count} files → {target_path} → {output_pak}[/bold #00FF88]')
                else:
                    console.print('[bold #FF0055]❌ No files processed![/bold #FF0055]')
            except Exception as e:
                console.print(f'[bold #FF0055]❌ Repack failed:[/bold #FF0055] {e}')
                import traceback
                traceback.print_exc()
            safe_input('\nPress Enter to continue...')

        elif choice == '9':
            delete_folder(data_path)
            safe_input('\nPress Enter to continue...')

        elif choice.lower() == 'h':
            generate_hardened_so(data_path)
            safe_input('\nPress Enter to continue...')

        elif choice == '0':
            console.print("[bold magenta]Goodbye![/bold magenta]")
            time.sleep(2)
            break
        else:
            console.print('[bold #FF0055]❌ Invalid choice![/bold #FF0055]')
            time.sleep(2)

if __name__ == '__main__':
    try:
        main_menu()
    except KeyboardInterrupt:
        console.print('\n[bold #FFFF00]⚠ Interrupted. Exiting...[/bold #FFFF00]')
        sys.exit(0)
    except Exception as e:
        console.print(f'[bold #FF0055]💥 ERROR:[/bold #FF0055] {escape(str(e))}')
        import traceback
        traceback.print_exc()
        safe_input('\nPress Enter to exit...')
        sys.exit(1)
        
#🔰THIS TOOL MOD BY - @TrnDravix 🔰
#🔰TELEGRAM SEARCH - @TrnDravix 🔰
#🔰TELEGRAM CHANNEL - TrnDravix BGMI    🔰
#🔰OWNER / MODER -TrnDravix TrnDravix           🔰