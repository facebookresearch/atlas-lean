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
def generatedSixthXiShortBlock073Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (372, 16)),
    Sum.inr (Sum.inr (372, 17)),
    Sum.inr (Sum.inr (383, 18)),
    Sum.inr (Sum.inr (372, 19)),
    Sum.inr (Sum.inr (170, 12)),
    Sum.inr (Sum.inr (224, 14)),
    Sum.inr (Sum.inr (32, 15)),
    Sum.inr (Sum.inr (97, 13)),
    Sum.inr (Sum.inl (188, 19)),
    Sum.inr (Sum.inl (187, 38)),
    Sum.inr (Sum.inl (143, 7)),
    Sum.inr (Sum.inl (166, 40)),
    Sum.inr (Sum.inl (31, 11)),
    Sum.inr (Sum.inl (11, 4)),
    Sum.inr (Sum.inl (31, 14)),
    Sum.inr (Sum.inl (31, 2)),
    Sum.inr (Sum.inl (188, 22)),
    Sum.inr (Sum.inl (143, 2)),
    Sum.inr (Sum.inl (166, 45)),
    Sum.inr (Sum.inl (187, 35)),
    Sum.inr (Sum.inl (166, 19)),
    Sum.inr (Sum.inl (188, 40)),
    Sum.inr (Sum.inl (143, 60)),
    Sum.inr (Sum.inl (187, 29)),
    Sum.inr (Sum.inl (11, 27)),
    Sum.inr (Sum.inl (11, 43)),
    Sum.inr (Sum.inl (31, 7)),
    Sum.inr (Sum.inl (11, 52)),
    Sum.inr (Sum.inl (166, 22)),
    Sum.inr (Sum.inl (143, 57)),
    Sum.inr (Sum.inl (187, 24)),
    Sum.inr (Sum.inl (188, 45)),
    Sum.inr (Sum.inl (212, 54)),
    Sum.inr (Sum.inl (206, 51)),
    Sum.inr (Sum.inl (149, 58)),
    Sum.inr (Sum.inl (172, 18)),
    Sum.inr (Sum.inl (37, 27)),
    Sum.inr (Sum.inl (17, 20)),
    Sum.inr (Sum.inl (37, 30)),
    Sum.inr (Sum.inl (37, 18)),
    Sum.inr (Sum.inl (212, 51)),
    Sum.inr (Sum.inl (149, 63)),
    Sum.inr (Sum.inl (172, 23)),
    Sum.inr (Sum.inl (206, 54)),
    Sum.inr (Sum.inl (172, 27)),
    Sum.inr (Sum.inl (212, 63)),
    Sum.inr (Sum.inl (149, 51)),
    Sum.inr (Sum.inl (206, 58)),
    Sum.inr (Sum.inl (17, 30)),
    Sum.inr (Sum.inl (17, 29)),
    Sum.inr (Sum.inl (37, 23)),
    Sum.inr (Sum.inl (17, 23)),
    Sum.inr (Sum.inl (172, 30)),
    Sum.inr (Sum.inl (149, 54)),
    Sum.inr (Sum.inl (206, 63)),
    Sum.inr (Sum.inl (212, 58)),
    Sum.inr (Sum.inl (214, 33)),
    Sum.inr (Sum.inl (208, 48)),
    Sum.inr (Sum.inl (151, 18)),
    Sum.inr (Sum.inl (174, 13)),
    Sum.inr (Sum.inl (39, 2)),
    Sum.inr (Sum.inl (19, 13)),
    Sum.inr (Sum.inl (39, 18)),
    Sum.inr (Sum.inl (39, 45)),
    Sum.inr (Sum.inl (214, 62)),
    Sum.inr (Sum.inl (151, 13)),
    Sum.inr (Sum.inl (174, 18)),
    Sum.inr (Sum.inl (208, 47)),
    Sum.inr (Sum.inl (174, 34)),
    Sum.inr (Sum.inl (214, 14)),
    Sum.inr (Sum.inl (151, 61)),
    Sum.inr (Sum.inl (208, 31)),
    Sum.inr (Sum.inl (19, 18)),
    Sum.inr (Sum.inl (19, 34)),
    Sum.inr (Sum.inl (39, 61)),
    Sum.inr (Sum.inl (19, 61)),
    Sum.inr (Sum.inl (174, 61)),
    Sum.inr (Sum.inl (151, 34)),
    Sum.inr (Sum.inl (208, 0)),
    Sum.inr (Sum.inl (214, 17)),
    Sum.inr (Sum.inl (211, 35)),
    Sum.inr (Sum.inl (205, 38)),
    Sum.inr (Sum.inl (148, 7)),
    Sum.inr (Sum.inl (171, 24)),
    Sum.inr (Sum.inl (36, 27)),
    Sum.inr (Sum.inl (16, 1)),
    Sum.inr (Sum.inl (36, 30)),
    Sum.inr (Sum.inl (36, 18)),
    Sum.inr (Sum.inl (211, 60)),
    Sum.inr (Sum.inl (148, 24)),
    Sum.inr (Sum.inl (171, 7)),
    Sum.inr (Sum.inl (205, 57)),
    Sum.inr (Sum.inl (171, 57)),
    Sum.inr (Sum.inl (211, 2)),
    Sum.inr (Sum.inl (148, 38)),
    Sum.inr (Sum.inl (205, 7)),
    Sum.inr (Sum.inl (16, 30)),
    Sum.inr (Sum.inl (16, 46)),
    Sum.inr (Sum.inl (36, 23)),
    Sum.inr (Sum.inl (16, 49)),
    Sum.inr (Sum.inl (171, 38)),
    Sum.inr (Sum.inl (148, 57)),
    Sum.inr (Sum.inl (205, 24)),
    Sum.inr (Sum.inl (211, 29)),
    Sum.inr (Sum.inr (356, 0)),
    Sum.inr (Sum.inr (293, 22)),
    Sum.inr (Sum.inr (485, 14)),
    Sum.inr (Sum.inr (431, 10)),
    Sum.inr (Sum.inr (122, 18)),
    Sum.inr (Sum.inr (113, 5)),
    Sum.inr (Sum.inr (122, 7)),
    Sum.inr (Sum.inr (122, 6)),
    Sum.inr (Sum.inr (356, 8)),
    Sum.inr (Sum.inr (485, 21)),
    Sum.inr (Sum.inr (431, 3)),
    Sum.inr (Sum.inr (293, 15)),
    Sum.inr (Sum.inr (431, 20)),
    Sum.inr (Sum.inr (356, 13)),
    Sum.inr (Sum.inr (485, 2)),
    Sum.inr (Sum.inr (293, 11)),
    Sum.inr (Sum.inr (113, 16)),
    Sum.inr (Sum.inr (113, 17)),
    Sum.inr (Sum.inr (122, 4)),
    Sum.inr (Sum.inr (113, 19)),
    Sum.inr (Sum.inr (431, 12)),
    Sum.inr (Sum.inr (485, 9)),
    Sum.inr (Sum.inr (293, 1)),
    Sum.inr (Sum.inr (356, 23)),
    Sum.inr (Sum.inr (430, 8)),
    Sum.inr (Sum.inr (495, 15)),
    Sum.inr (Sum.inr (303, 21)),
    Sum.inr (Sum.inr (357, 3)),
    Sum.inr (Sum.inr (176, 18)),
    Sum.inr (Sum.inr (187, 5)),
    Sum.inr (Sum.inr (176, 7)),
    Sum.inr (Sum.inr (176, 6)),
    Sum.inr (Sum.inr (430, 0)),
    Sum.inr (Sum.inr (303, 14)),
    Sum.inr (Sum.inr (357, 10)),
    Sum.inr (Sum.inr (495, 22)),
    Sum.inr (Sum.inr (357, 12)),
    Sum.inr (Sum.inr (430, 23)),
    Sum.inr (Sum.inr (303, 9)),
    Sum.inr (Sum.inr (495, 1)),
    Sum.inr (Sum.inr (187, 16)),
    Sum.inr (Sum.inr (187, 17)),
    Sum.inr (Sum.inr (176, 4)),
    Sum.inr (Sum.inr (187, 19)),
    Sum.inr (Sum.inr (357, 20)),
    Sum.inr (Sum.inr (303, 2)),
    Sum.inr (Sum.inr (495, 11)),
    Sum.inr (Sum.inr (430, 13)),
    Sum.inr (Sum.inr (487, 13)),
    Sum.inr (Sum.inr (422, 11)),
    Sum.inr (Sum.inr (358, 2)),
    Sum.inr (Sum.inr (300, 20)),
    Sum.inr (Sum.inr (249, 18)),
    Sum.inr (Sum.inr (242, 5)),
    Sum.inr (Sum.inr (249, 7)),
    Sum.inr (Sum.inr (249, 6)),
    Sum.inr (Sum.inr (487, 23)),
    Sum.inr (Sum.inr (358, 9)),
    Sum.inr (Sum.inr (300, 12)),
    Sum.inr (Sum.inr (422, 1)),
    Sum.inr (Sum.inr (300, 10)),
    Sum.inr (Sum.inr (487, 0)),
    Sum.inr (Sum.inr (358, 14)),
    Sum.inr (Sum.inr (422, 22)),
    Sum.inr (Sum.inr (242, 16)),
    Sum.inr (Sum.inr (242, 17)),
    Sum.inr (Sum.inr (249, 4)),
    Sum.inr (Sum.inr (242, 19)),
    Sum.inr (Sum.inr (300, 3)),
    Sum.inr (Sum.inr (358, 21)),
    Sum.inr (Sum.inr (422, 15)),
    Sum.inr (Sum.inr (487, 8)),
    Sum.inr (Sum.inr (294, 23)),
    Sum.inr (Sum.inr (359, 1)),
    Sum.inr (Sum.inr (423, 9)),
    Sum.inr (Sum.inr (493, 12)),
    Sum.inr (Sum.inr (56, 18)),
    Sum.inr (Sum.inr (51, 5)),
    Sum.inr (Sum.inr (56, 7)),
    Sum.inr (Sum.inr (56, 6)),
    Sum.inr (Sum.inr (294, 13)),
    Sum.inr (Sum.inr (423, 2)),
    Sum.inr (Sum.inr (493, 20)),
    Sum.inr (Sum.inr (359, 11)),
    Sum.inr (Sum.inr (493, 3)),
    Sum.inr (Sum.inr (294, 8)),
    Sum.inr (Sum.inr (423, 21)),
    Sum.inr (Sum.inr (359, 15)),
    Sum.inr (Sum.inr (51, 16)),
    Sum.inr (Sum.inr (51, 17)),
    Sum.inr (Sum.inr (56, 4)),
    Sum.inr (Sum.inr (51, 19)),
    Sum.inr (Sum.inr (493, 10)),
    Sum.inr (Sum.inr (423, 14)),
    Sum.inr (Sum.inr (359, 22)),
    Sum.inr (Sum.inr (294, 0)),
    Sum.inr (Sum.inl (210, 49)),
    Sum.inr (Sum.inl (204, 27)),
    Sum.inr (Sum.inl (147, 41)),
    Sum.inr (Sum.inl (170, 9)),
    Sum.inr (Sum.inl (35, 27)),
    Sum.inr (Sum.inl (15, 5)),
    Sum.inr (Sum.inl (35, 19)),
    Sum.inr (Sum.inl (35, 31)),
    Sum.inr (Sum.inl (210, 30)),
    Sum.inr (Sum.inl (147, 59)),
    Sum.inr (Sum.inl (170, 25)),
    Sum.inr (Sum.inl (204, 57)),
    Sum.inr (Sum.inl (170, 27)),
    Sum.inr (Sum.inl (210, 10)),
    Sum.inr (Sum.inl (147, 57)),
    Sum.inr (Sum.inl (204, 38)),
    Sum.inr (Sum.inl (15, 37)),
    Sum.inr (Sum.inl (15, 21)),
    Sum.inr (Sum.inl (35, 23)),
    Sum.inr (Sum.inl (15, 53)),
    Sum.inr (Sum.inl (170, 11)),
    Sum.inr (Sum.inl (147, 43)),
    Sum.inr (Sum.inl (204, 4)),
    Sum.inr (Sum.inl (210, 37)),
    Sum.inr (Sum.inl (133, 25)),
    Sum.inr (Sum.inl (132, 56)),
    Sum.inr (Sum.inl (126, 57)),
    Sum.inr (Sum.inl (128, 33)),
    Sum.inr (Sum.inl (26, 37)),
    Sum.inr (Sum.inl (6, 59)),
    Sum.inr (Sum.inl (26, 45)),
    Sum.inr (Sum.inl (26, 33)),
    Sum.inr (Sum.inl (133, 54)),
    Sum.inr (Sum.inl (126, 24)),
    Sum.inr (Sum.inl (128, 49)),
    Sum.inr (Sum.inl (132, 25)),
    Sum.inr (Sum.inl (128, 41)),
    Sum.inr (Sum.inl (133, 8)),
    Sum.inr (Sum.inl (126, 56)),
    Sum.inr (Sum.inl (132, 39)),
    Sum.inr (Sum.inl (6, 27)),
    Sum.inr (Sum.inl (6, 43)),
    Sum.inr (Sum.inl (26, 41)),
    Sum.inr (Sum.inl (6, 11)),
    Sum.inr (Sum.inl (128, 57)),
    Sum.inr (Sum.inl (126, 25)),
    Sum.inr (Sum.inl (132, 6)),
    Sum.inr (Sum.inl (133, 39)),
    Sum.inr (Sum.inl (88, 9)),
    Sum.inr (Sum.inl (87, 40)),
    Sum.inr (Sum.inl (81, 6)),
    Sum.inr (Sum.inl (83, 26)),
    Sum.inr (Sum.inl (23, 10)),
    Sum.inr (Sum.inl (3, 0)),
    Sum.inr (Sum.inl (23, 2)),
    Sum.inr (Sum.inl (23, 14))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock073Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨18688 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock073InputMaskData : ℕ :=
  sixthHex% [
    "97fa769ffa7693f276dbf276eb0a76cb0276fb0a769b0276834a75b54275",
    "ae4275d84a75bf8275a18275868275d88275a7ea758dea75b2ea75d8ea75",
    "9bd27599da759ada75d8d27594c2759cc27590ca75d8ca75e83275c83a75",
    "f83275983a75d0a274e6aa74fdaa748ba274ec6a74f26a74d56a748b6a74",
    "f40274de0274e102748b0274c83274ca3a74c93a748b3274c72a74cf2a74",
    "c322748b2274bbd2749bda74abd274cbda74832a73b52273ae2273d82a73",
    "bfea73a1ea7386ea73d8ea73a782738d8273b28273d882739bb27399ba73",
    "9aba73d8b27394a2739ca27390aa73d8aa73e85273c85a73f85273985a73",
    "d0c272e6ca72fdca728bc272ec0272f20272d502728b0272f46a72de6a72",
    "e16a728b6a72c85272ca5a72c95a728b5272c74a72cf4a72c342728b4272",
    "bbb2729bba72abb272cbba72d3fa71e5f271fef27188fa71ef3a71f13a71",
    "d63a71883a71f75a71dd5a71e25a71885a71cb6271c96a71ca6a71886271",
    "c47271cc7271c07a71887a71b88a71988271a88a71c88271c01270f61a70",
    "ed1a709b1270fcd270e2d270c5d2709bd270e4b270ceb270f1b2709bb270",
    "d88270da8a70d98a709b8270d79a70df9a70d392709b9270ab6a708b6270",
    "bb6a70db6270c7ca1ff1c21feaca1f9cc21ffb021fe5021fc2021f9c021f",
    "e3621fc96a1ff66a1f9c621fdf5a1fdd5a1fde521f9c521fd04a1fd84a1f",
    "d44a1f9c4a1facb21f8cba1fbcb21fdcba1f95221ea32a1eb8221ece2a1e",
    "a9ea1eb7ea1e90ea1eceea1eb18a1e9b821ea4821ece8a1e8dba1e8fba1e",
    "8cb21eceb21e82a21e8aa21e86a21ecea21efe521ede5a1eee521e8e5a1e",
    "a8121d9e1a1d85121df31a1d94da1d8ada1dadda1df3da1d8cb21da6ba1d",
    "99ba1df3b21db0821db2821db18a1df38a1dbf921db7921dbb921df3921d",
    "c3621de36a1dd3621db36a1dbafa1c8cf21c97fa1ce1f21c86321c98321c",
    "bf321ce1321c9e5a1cb4521c8b521ce15a1ca2621ca0621ca36a1ce16a1c",
    "ad7a1ca57a1ca97a1ce17a1cd1821cf18a1cc1821ca18a1c977a1ba1721b",
    "ba7a1bcc721babba1bb5ba1b92ba1bccba1b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock073InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock073InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock073OutputMaskData : ℕ :=
  sixthHex% [
    "71c63879ce383186334c8e3831215d44286713fb4713f276768b4f208a7e",
    "2d115e0e106411870a3a870128870a76870a43627e7ff15e47234f0eb064",
    "0e127e4f806468c95e5c5b4f0fcf0107c7014f8f0a3287014f28643a215e",
    "6df27e6dfb4f41106e17115f1a8a7f398b45261c2b0d1c201f1c2b411c2b",
    "74f95f486a7f70b86e392b4548c95f095b452e127f1a806e385420305c20",
    "78142b051c2009f3457cfa7f2b295f2b206ef67c96a07da7ade6878ee7bd",
    "e030d3cb30d8d930d38730d3b2d5a78e4687b69496ff07bd8ee5a7cf77bd",
    "e83e87dcac968f38d88730d8cf78d3b270d8cfdfbdbad687ed05a7ed0c96",
    "c1e7b797e6869a7da6b97c9cd7abf2fcabf9eeabf2b0abf2854e86b9dda6",
    "810fb7c89c9cc83e8689ac9caee5a69a77b7b8a3f9b0abf9f8e3f285ebf9",
    "89049cfc0da6abde86abd7b7bfee8ee9efbfe4749fc775a5a9a2cb82a2c0",
    "90a2cbcea2cb8a07bfb6949f8e468ec7d5a5c777bf86e5a5a1ac9f953e8e",
    "c6aac0cea2c086eacbfbe2c0f70da582049fd5d7bfd5de8efd75a4ab7495",
    "a6efb585ee8feb39e1c039ead239e18c39e1c89c95f40fb5ccdda4854e8f",
    "f4ac95b53e8f9277b5a6e5a48431ea8c39eac471e1b979eac4d68fb1dfb5",
    "e60c95e605a4000c40560d712ad65109d76b6700054c000e5e0005000005",
    "44a57109765131a44009776b09d57139076b6f0e512adc4008080e00000e",
    "39080544000e39af6b4ca6511b75711b7c40200c41760d700ad65029d76a",
    "4700046c000f7e000420000464a57029765011a44129776a58957068476a",
    "3e4e507b9c4128080f20000f19080464000f68ef6a1de6504a35704a3c41",
    "000c49560d782ad65809d76267000c4c00075e000c00000c35e578783658",
    "40e44978376209d5783907626f0e582adc4908080700000739080c440007",
    "48ef623de6586a35786a3c49550c43030d727fd6525cd76832000619000d",
    "0b000655000660e5722d365215e4432d37682d95721d47684b4e520e9c43",
    "5d080d55000d6c080611000d6caf6819a6524e75724e7c43c969819f68b0",
    "e3b390c0b2aadf25c4f425cfe625c4b825c4"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock073OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock073OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock073InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock073InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock073InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock073OutputNumeratorData : ℕ :=
  sixthHex% [
    "8618617e17e17e185f6df8e37df8617e17e186186185f7e17e17e16df8e3",
    "7e185f8617df86186185f85f8617e195f75d7df7e185f7df85f7df86185f",
    "86185f95f75d7e17df7df7e185f7df8617e18617e195f75d86185f85f7df",
    "85f7df7df7e186185f95f75d85f8617df7e185f7df7df85f7e18616e18e3",
    "86185f8617e186185f8617e17e17df6e18e385f8617e17df86185f86185f",
    "7e18616e18e37df7e18617e186185f7df85f85f86195f75d85f86185f861",
    "7df7e186185f7df8616df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock073OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock073OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block073_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock073Input a) =
      generatedSixthXiShortBlock073InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock073Output a) =
      generatedSixthXiShortBlock073OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock073Input a) =
      generatedSixthXiShortBlock073InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock073Output a) =
      generatedSixthXiShortBlock073OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block073_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock073InputMask a) =
      generatedSixthXiShortBlock073OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock073InputMask a)) *
      generatedSixthXiShortBlock073InputNumerator a =
        generatedSixthXiShortBlock073OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block073_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock073Input a
    let y := generatedSixthXiShortBlock073Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block073_cache a
  have hs := generatedSixth_xi_short_block073_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block073_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock073Input a
    let y := generatedSixthXiShortBlock073Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block073_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block073_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock073Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block073_certificate a).1
    (generatedSixth_xi_short_block073_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
