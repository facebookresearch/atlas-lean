/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortNumbering
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFoldedScalar
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressMaskEight

/-! Original sparse masks and full signed phases certify a bounded part of actual short support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Candidate sparse outputs are checked against the original full binary and phase action. -/
def generatedSixthXiShortBlock065Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (450, 8)),
    Sum.inr (Sum.inr (323, 2)),
    Sum.inr (Sum.inr (265, 12)),
    Sum.inr (Sum.inr (387, 22)),
    Sum.inr (Sum.inr (265, 10)),
    Sum.inr (Sum.inr (450, 13)),
    Sum.inr (Sum.inr (323, 21)),
    Sum.inr (Sum.inr (387, 1)),
    Sum.inr (Sum.inr (215, 16)),
    Sum.inr (Sum.inr (215, 17)),
    Sum.inr (Sum.inr (220, 6)),
    Sum.inr (Sum.inr (215, 19)),
    Sum.inr (Sum.inr (265, 3)),
    Sum.inr (Sum.inr (323, 14)),
    Sum.inr (Sum.inr (387, 11)),
    Sum.inr (Sum.inr (450, 23)),
    Sum.inr (Sum.inr (322, 8)),
    Sum.inr (Sum.inr (259, 22)),
    Sum.inr (Sum.inr (451, 2)),
    Sum.inr (Sum.inr (393, 12)),
    Sum.inr (Sum.inr (92, 7)),
    Sum.inr (Sum.inr (87, 5)),
    Sum.inr (Sum.inr (92, 18)),
    Sum.inr (Sum.inr (92, 4)),
    Sum.inr (Sum.inr (322, 0)),
    Sum.inr (Sum.inr (451, 9)),
    Sum.inr (Sum.inr (393, 20)),
    Sum.inr (Sum.inr (259, 15)),
    Sum.inr (Sum.inr (393, 3)),
    Sum.inr (Sum.inr (322, 23)),
    Sum.inr (Sum.inr (451, 14)),
    Sum.inr (Sum.inr (259, 11)),
    Sum.inr (Sum.inr (87, 16)),
    Sum.inr (Sum.inr (87, 17)),
    Sum.inr (Sum.inr (92, 6)),
    Sum.inr (Sum.inr (87, 19)),
    Sum.inr (Sum.inr (393, 10)),
    Sum.inr (Sum.inr (451, 21)),
    Sum.inr (Sum.inr (259, 1)),
    Sum.inr (Sum.inr (322, 13)),
    Sum.inr (Sum.inl (213, 53)),
    Sum.inr (Sum.inl (207, 21)),
    Sum.inr (Sum.inl (150, 29)),
    Sum.inr (Sum.inl (173, 20)),
    Sum.inr (Sum.inl (38, 52)),
    Sum.inr (Sum.inl (18, 12)),
    Sum.inr (Sum.inl (38, 60)),
    Sum.inr (Sum.inl (38, 62)),
    Sum.inr (Sum.inl (213, 42)),
    Sum.inr (Sum.inl (150, 61)),
    Sum.inr (Sum.inl (173, 54)),
    Sum.inr (Sum.inl (207, 52)),
    Sum.inr (Sum.inl (173, 52)),
    Sum.inr (Sum.inl (213, 20)),
    Sum.inr (Sum.inl (150, 21)),
    Sum.inr (Sum.inl (207, 43)),
    Sum.inr (Sum.inl (18, 44)),
    Sum.inr (Sum.inl (18, 28)),
    Sum.inr (Sum.inl (38, 54)),
    Sum.inr (Sum.inl (18, 60)),
    Sum.inr (Sum.inl (173, 22)),
    Sum.inr (Sum.inl (150, 53)),
    Sum.inr (Sum.inl (207, 10)),
    Sum.inr (Sum.inl (213, 11)),
    Sum.inr (Sum.inl (158, 50)),
    Sum.inr (Sum.inl (157, 53)),
    Sum.inr (Sum.inl (140, 42)),
    Sum.inr (Sum.inl (153, 55)),
    Sum.inr (Sum.inl (28, 21)),
    Sum.inr (Sum.inl (8, 5)),
    Sum.inr (Sum.inl (28, 29)),
    Sum.inr (Sum.inl (28, 31)),
    Sum.inr (Sum.inl (158, 29)),
    Sum.inr (Sum.inl (140, 5)),
    Sum.inr (Sum.inl (153, 21)),
    Sum.inr (Sum.inl (157, 23)),
    Sum.inr (Sum.inl (153, 53)),
    Sum.inr (Sum.inl (158, 9)),
    Sum.inr (Sum.inl (140, 56)),
    Sum.inr (Sum.inl (157, 42)),
    Sum.inr (Sum.inl (8, 37)),
    Sum.inr (Sum.inl (8, 21)),
    Sum.inr (Sum.inl (28, 23)),
    Sum.inr (Sum.inl (8, 53)),
    Sum.inr (Sum.inl (153, 23)),
    Sum.inr (Sum.inl (140, 23)),
    Sum.inr (Sum.inl (157, 8)),
    Sum.inr (Sum.inl (158, 38)),
    Sum.inr (Sum.inl (53, 20)),
    Sum.inr (Sum.inl (52, 36)),
    Sum.inr (Sum.inl (46, 4)),
    Sum.inr (Sum.inl (48, 21)),
    Sum.inr (Sum.inl (21, 4)),
    Sum.inr (Sum.inl (1, 0)),
    Sum.inr (Sum.inl (21, 12)),
    Sum.inr (Sum.inl (21, 14)),
    Sum.inr (Sum.inl (53, 5)),
    Sum.inr (Sum.inl (46, 21)),
    Sum.inr (Sum.inl (48, 5)),
    Sum.inr (Sum.inl (52, 4)),
    Sum.inr (Sum.inl (48, 17)),
    Sum.inr (Sum.inl (53, 21)),
    Sum.inr (Sum.inl (46, 20)),
    Sum.inr (Sum.inl (52, 5)),
    Sum.inr (Sum.inl (1, 32)),
    Sum.inr (Sum.inl (1, 16)),
    Sum.inr (Sum.inl (21, 6)),
    Sum.inr (Sum.inl (1, 48)),
    Sum.inr (Sum.inl (48, 1)),
    Sum.inr (Sum.inl (46, 5)),
    Sum.inr (Sum.inl (52, 37)),
    Sum.inr (Sum.inl (53, 4)),
    Sum.inr (Sum.inl (119, 37)),
    Sum.inr (Sum.inl (118, 58)),
    Sum.inr (Sum.inl (112, 54)),
    Sum.inr (Sum.inl (114, 59)),
    Sum.inr (Sum.inl (25, 43)),
    Sum.inr (Sum.inl (5, 59)),
    Sum.inr (Sum.inl (25, 35)),
    Sum.inr (Sum.inl (25, 33)),
    Sum.inr (Sum.inl (119, 52)),
    Sum.inr (Sum.inl (112, 36)),
    Sum.inr (Sum.inl (114, 43)),
    Sum.inr (Sum.inl (118, 37)),
    Sum.inr (Sum.inl (114, 41)),
    Sum.inr (Sum.inl (119, 10)),
    Sum.inr (Sum.inl (112, 11)),
    Sum.inr (Sum.inl (118, 13)),
    Sum.inr (Sum.inl (5, 27)),
    Sum.inr (Sum.inl (5, 43)),
    Sum.inr (Sum.inl (25, 41)),
    Sum.inr (Sum.inl (5, 11)),
    Sum.inr (Sum.inl (114, 57)),
    Sum.inr (Sum.inl (112, 25)),
    Sum.inr (Sum.inl (118, 18)),
    Sum.inr (Sum.inl (119, 27)),
    Sum.inr (Sum.inr (329, 8)),
    Sum.inr (Sum.inr (264, 22)),
    Sum.inr (Sum.inr (456, 2)),
    Sum.inr (Sum.inr (386, 12)),
    Sum.inr (Sum.inr (87, 7)),
    Sum.inr (Sum.inr (92, 5)),
    Sum.inr (Sum.inr (87, 18)),
    Sum.inr (Sum.inr (87, 4)),
    Sum.inr (Sum.inr (329, 0)),
    Sum.inr (Sum.inr (456, 9)),
    Sum.inr (Sum.inr (386, 20)),
    Sum.inr (Sum.inr (264, 15)),
    Sum.inr (Sum.inr (386, 3)),
    Sum.inr (Sum.inr (329, 23)),
    Sum.inr (Sum.inr (456, 14)),
    Sum.inr (Sum.inr (264, 11)),
    Sum.inr (Sum.inr (92, 16)),
    Sum.inr (Sum.inr (92, 17)),
    Sum.inr (Sum.inr (87, 6)),
    Sum.inr (Sum.inr (92, 19)),
    Sum.inr (Sum.inr (386, 10)),
    Sum.inr (Sum.inr (456, 21)),
    Sum.inr (Sum.inr (264, 1)),
    Sum.inr (Sum.inr (329, 13)),
    Sum.inr (Sum.inr (457, 0)),
    Sum.inr (Sum.inr (392, 15)),
    Sum.inr (Sum.inr (328, 9)),
    Sum.inr (Sum.inr (258, 20)),
    Sum.inr (Sum.inr (215, 7)),
    Sum.inr (Sum.inr (220, 5)),
    Sum.inr (Sum.inr (215, 18)),
    Sum.inr (Sum.inr (215, 4)),
    Sum.inr (Sum.inr (457, 8)),
    Sum.inr (Sum.inr (328, 2)),
    Sum.inr (Sum.inr (258, 12)),
    Sum.inr (Sum.inr (392, 22)),
    Sum.inr (Sum.inr (258, 10)),
    Sum.inr (Sum.inr (457, 13)),
    Sum.inr (Sum.inr (328, 21)),
    Sum.inr (Sum.inr (392, 1)),
    Sum.inr (Sum.inr (220, 16)),
    Sum.inr (Sum.inr (220, 17)),
    Sum.inr (Sum.inr (215, 6)),
    Sum.inr (Sum.inr (220, 19)),
    Sum.inr (Sum.inr (258, 3)),
    Sum.inr (Sum.inr (328, 14)),
    Sum.inr (Sum.inr (392, 11)),
    Sum.inr (Sum.inr (457, 23)),
    Sum.inr (Sum.inr (257, 23)),
    Sum.inr (Sum.inr (320, 11)),
    Sum.inr (Sum.inr (384, 14)),
    Sum.inr (Sum.inr (458, 3)),
    Sum.inr (Sum.inr (31, 7)),
    Sum.inr (Sum.inr (20, 5)),
    Sum.inr (Sum.inr (31, 18)),
    Sum.inr (Sum.inr (31, 4)),
    Sum.inr (Sum.inr (257, 13)),
    Sum.inr (Sum.inr (384, 21)),
    Sum.inr (Sum.inr (458, 10)),
    Sum.inr (Sum.inr (320, 1)),
    Sum.inr (Sum.inr (458, 12)),
    Sum.inr (Sum.inr (257, 8)),
    Sum.inr (Sum.inr (384, 2)),
    Sum.inr (Sum.inr (320, 22)),
    Sum.inr (Sum.inr (20, 16)),
    Sum.inr (Sum.inr (20, 17)),
    Sum.inr (Sum.inr (31, 6)),
    Sum.inr (Sum.inr (20, 19)),
    Sum.inr (Sum.inr (458, 20)),
    Sum.inr (Sum.inr (384, 9)),
    Sum.inr (Sum.inr (320, 15)),
    Sum.inr (Sum.inr (257, 0)),
    Sum.inr (Sum.inr (394, 13)),
    Sum.inr (Sum.inr (459, 1)),
    Sum.inr (Sum.inr (267, 21)),
    Sum.inr (Sum.inr (321, 10)),
    Sum.inr (Sum.inr (148, 7)),
    Sum.inr (Sum.inr (159, 5)),
    Sum.inr (Sum.inr (148, 18)),
    Sum.inr (Sum.inr (148, 4)),
    Sum.inr (Sum.inr (394, 23)),
    Sum.inr (Sum.inr (267, 14)),
    Sum.inr (Sum.inr (321, 3)),
    Sum.inr (Sum.inr (459, 11)),
    Sum.inr (Sum.inr (321, 20)),
    Sum.inr (Sum.inr (394, 0)),
    Sum.inr (Sum.inr (267, 9)),
    Sum.inr (Sum.inr (459, 15)),
    Sum.inr (Sum.inr (159, 16)),
    Sum.inr (Sum.inr (159, 17)),
    Sum.inr (Sum.inr (148, 6)),
    Sum.inr (Sum.inr (159, 19)),
    Sum.inr (Sum.inr (321, 12)),
    Sum.inr (Sum.inr (267, 2)),
    Sum.inr (Sum.inr (459, 22)),
    Sum.inr (Sum.inr (394, 8)),
    Sum.inr (Sum.inr (170, 8)),
    Sum.inr (Sum.inr (235, 11)),
    Sum.inr (Sum.inr (43, 9)),
    Sum.inr (Sum.inr (97, 10)),
    Sum.inr (Sum.inr (436, 4)),
    Sum.inr (Sum.inr (447, 5)),
    Sum.inr (Sum.inr (436, 6)),
    Sum.inr (Sum.inr (436, 7)),
    Sum.inr (Sum.inr (170, 0)),
    Sum.inr (Sum.inr (43, 2)),
    Sum.inr (Sum.inr (97, 3)),
    Sum.inr (Sum.inr (235, 1)),
    Sum.inr (Sum.inr (97, 20)),
    Sum.inr (Sum.inr (170, 23)),
    Sum.inr (Sum.inr (43, 21)),
    Sum.inr (Sum.inr (235, 22)),
    Sum.inr (Sum.inr (447, 16)),
    Sum.inr (Sum.inr (447, 17)),
    Sum.inr (Sum.inr (436, 18)),
    Sum.inr (Sum.inr (447, 19)),
    Sum.inr (Sum.inr (97, 12)),
    Sum.inr (Sum.inr (43, 14)),
    Sum.inr (Sum.inr (235, 15)),
    Sum.inr (Sum.inr (170, 13))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock065Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨16640 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock065InputMaskData : ℕ :=
  sixthHex% [
    "df3930e93930f23130843130e3f130fdf130daf13084f130fb9930d19130",
    "ee9930849130c7a130c5a930c6a93084a130c8b130c0b130ccb13084b130",
    "b44930944930a44130c441308730dfb138dfaa38dfdc30dfbbf0dfa5f0df",
    "82f0dfdcf0dfa398df8990dfb698dfdc90df9fa8df9da8df9ea0dfdca0df",
    "90b8df98b0df94b0dfdcb8dfec48dfcc48dffc48df9c48dfc5d0def3d8de",
    "e8d8de9ed0def910dee710dec010de9e10dee178decb70def478de9e70de",
    "dd40dedf40dedc48de9e48ded258deda50ded650de9e58deaea0de8ea0de",
    "bea0dedea0ded2e0dde4e8ddffe8dd89e0ddee20ddf020ddd720dd8920dd",
    "f640dddc48dde340dd8948ddca78ddc878ddcb70dd8970ddc568ddcd60dd",
    "c160dd8968ddb990dd9990dda990ddc990ddd000dce608dcfd08dc8b00dc",
    "ecc0dcf2c0dcd5c0dc8bc0dcf4a0dcdea8dce1a0dc8ba8dcc890dcca90dc",
    "c998dc8b98dcc788dccf80dcc380dc8b88dcbb78dc9b78dcab78dccb78dc",
    "c788dbf180dbea80db9c88dbfb40dbe540dbc240db9c40dbe320dbc928db",
    "f620db9c28dbdf10dbdd10dbde18db9c18dbd000dbd808dbd408db9c00db",
    "acf8db8cf8dbbcf8dbdcf8dbc568daf360dae860da9e68daf9a0dae7a0da",
    "c0a0da9ea0dae1c0dacbc8daf4c0da9ec8daddf8dadff8dadcf0da9ef0da",
    "d2e0dadae8dad6e8da9ee0daae10da8e10dabe10dade10dad258d9e450d9",
    "ff50d98958d9ee90d9f090d9d790d98990d9f6f8d9dcf0d9e3f8d989f0d9",
    "cac0d9c8c0d9cbc8d989c8d9c5d0d9cdd8d9c1d8d989d0d9b920d99920d9",
    "a920d9c920d990b8d8a6b0d8bdb0d8cbb8d8ac70d8b270d89570d8cb70d8",
    "b418d89e10d8a118d8cb10d88828d88a28d88920d8cb20d88730d88f38d8",
    "8338d8cb30d8fbc8d8dbc8d8ebc8d88bc8d8dc48d7ea40d7f140d78748d7",
    "e080d7fe80d7d980d78780d7f8e8d7d2e0d7ede8d787e0d7c4d8d7c6d8d7",
    "c5d0d787d0d7cbc8d7c3c0d7cfc0d787c8d7b730d79730d7a730d7c730d7",
    "dea8d6e8a0d6f3a0d685a8d6e260d6fc60d6db60d68560d6fa08d6d000d6",
    "ef08d68500d6c630d6c430d6c738d68538d6"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock065InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock065InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock065OutputMaskData : ℕ :=
  sixthHex% [
    "aabaaa8dfb9bf120bba36181cdb6efe6b6e4f4b6efaab6ef9f539bd280bb",
    "9b12aaa3c181d2239b93b181b4f8bb806aaad3fee4dbf6e4e2feef9ff6e4",
    "e25981e610bbb1c39bc08aaaf2663aa4670ba9fc2b8afd11e42a7fcf2a74",
    "dd2a7f832a7fb6cf0bfb1c2bb28e3a8a5d118aff0bba2d11ec242ba9f63a",
    "8b2274f26a74cb627fc72a74cbc511cf8c2be91f0b98563a81fc21d7fd10",
    "da6630f9670a97b064bcb06faeb064f0b064c55510888630c11421f9c70a",
    "882510b8f70aeefe30ab2c21f8b86f81f06fb8f864b4b06fc91f0acd5630",
    "ebc5109a8c219d6f09cb6e38c6f518e5f4228b234ca02347b2234cec234c",
    "a88638e55518acc709941422e5f638d52422832d18c6ff09e42b479d6347",
    "a46b4ca82347d58c22d1c518f75638861f099bf519cdf428c06f08e36e32",
    "8db95ca6b957b4b95ceab95cae1c28e3cf08aa5d19928e32922c28a2fe32",
    "f4f708b12519e2b1579bf957a2f15caeb957a25632a61f08808c28f1c519",
    "6899e13e98d03303f01002ca0f95a42495af3695a46895a42c30d061e3f0",
    "2871e110a2ca1000d020d2ca76dbf03309e111ddaf6895af519da45dd5af",
    "207aca2433f002a0d073e9e16e03f13802c03599e01698da090fb4220fbf",
    "300fb46e0fb42aaac06779e02eebf11638da67dac05708da0101e044d3f1",
    "1747bf6e0fbf5707b45b4fbf57a0da53e9e0757ac00433f17290d92491e8",
    "290ac80a0bf2159c9c3e9c972c9c9c729c9c4779e80aaac84338d97bebf2",
    "0a09e83adbf26cd2c82900d90bd497729c974b949c47dc974b33f24f7ac8",
    "69e9e818a0d9010ac2570bf35a90d37991e96606874d068c5f0687010687",
    "34e3f37930d330a2c20871e908d3f33801e96e08d32bdac2784e8c01068c",
    "380e8734468c49e9e94da0d36b33f31a7ac2e2f512b4f423b96f039a6e39",
    "85f957aef95cbcf957e2f957d71c239acf03d35d12eb8e39eb2c23dbfe39",
    "8df703c82512eaf15c93b95caab157a6f95cdb5639df1f03f98c2388c512",
    "e46f02b26e33bff5139cf429836347a8634cba6347e46347d186339c5513",
    "d5c702ed14299cf633ac2429fa2d13bfff02"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock065OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock065OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock065InputNumeratorData : ℕ :=
  sixthHex% [
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock065InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock065InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock065OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df8616df8e38617df8618617e185f85f85f7e17e16df8e37e185f8617df",
    "86186185f85f7e185f6df8e37df8617e17e186186185f7e185f85f96175d",
    "7e185f7df8617df7df85f85f85f7e196175d7df86185f85f7df7df85f7e1",
    "7df7e16e18e37e17df86185f7e18618617e18617e195f75d86185f85f7df",
    "85f7df7df7e186185f95f75d7e17df7df7e185f7df8617e18617e195f75d",
    "7df7e185f7df85f7df86185f7e185f6df8e38617df7e17e18618617e185f",
    "7e17e16df8e385f7e18617df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock065OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock065OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block065_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock065Input a) =
      generatedSixthXiShortBlock065InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock065Output a) =
      generatedSixthXiShortBlock065OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock065Input a) =
      generatedSixthXiShortBlock065InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock065Output a) =
      generatedSixthXiShortBlock065OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block065_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock065InputMask a) =
      generatedSixthXiShortBlock065OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock065InputMask a)) *
      generatedSixthXiShortBlock065InputNumerator a =
        generatedSixthXiShortBlock065OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block065_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock065Input a
    let y := generatedSixthXiShortBlock065Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block065_cache a
  have hs := generatedSixth_xi_short_block065_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block065_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock065Input a
    let y := generatedSixthXiShortBlock065Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block065_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block065_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock065Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block065_certificate a).1
    (generatedSixth_xi_short_block065_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
