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
def generatedSixthXiShortBlock078Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (43, 8)),
    Sum.inr (Sum.inr (106, 11)),
    Sum.inr (Sum.inr (170, 9)),
    Sum.inr (Sum.inr (224, 10)),
    Sum.inr (Sum.inr (309, 4)),
    Sum.inr (Sum.inr (318, 5)),
    Sum.inr (Sum.inr (309, 6)),
    Sum.inr (Sum.inr (309, 7)),
    Sum.inr (Sum.inr (43, 0)),
    Sum.inr (Sum.inr (170, 2)),
    Sum.inr (Sum.inr (224, 3)),
    Sum.inr (Sum.inr (106, 1)),
    Sum.inr (Sum.inr (224, 20)),
    Sum.inr (Sum.inr (43, 23)),
    Sum.inr (Sum.inr (170, 21)),
    Sum.inr (Sum.inr (106, 22)),
    Sum.inr (Sum.inr (318, 16)),
    Sum.inr (Sum.inr (318, 17)),
    Sum.inr (Sum.inr (309, 18)),
    Sum.inr (Sum.inr (318, 19)),
    Sum.inr (Sum.inr (224, 12)),
    Sum.inr (Sum.inr (170, 14)),
    Sum.inr (Sum.inr (106, 15)),
    Sum.inr (Sum.inr (43, 13)),
    Sum.inr (Sum.inr (40, 13)),
    Sum.inr (Sum.inr (105, 15)),
    Sum.inr (Sum.inr (169, 14)),
    Sum.inr (Sum.inr (227, 12)),
    Sum.inr (Sum.inr (310, 4)),
    Sum.inr (Sum.inr (317, 5)),
    Sum.inr (Sum.inr (310, 6)),
    Sum.inr (Sum.inr (310, 7)),
    Sum.inr (Sum.inr (40, 23)),
    Sum.inr (Sum.inr (169, 21)),
    Sum.inr (Sum.inr (227, 20)),
    Sum.inr (Sum.inr (105, 22)),
    Sum.inr (Sum.inr (227, 3)),
    Sum.inr (Sum.inr (40, 0)),
    Sum.inr (Sum.inr (169, 2)),
    Sum.inr (Sum.inr (105, 1)),
    Sum.inr (Sum.inr (317, 16)),
    Sum.inr (Sum.inr (317, 17)),
    Sum.inr (Sum.inr (310, 18)),
    Sum.inr (Sum.inr (317, 19)),
    Sum.inr (Sum.inr (227, 10)),
    Sum.inr (Sum.inr (169, 9)),
    Sum.inr (Sum.inr (105, 11)),
    Sum.inr (Sum.inr (40, 8)),
    Sum.inr (Sum.inr (41, 23)),
    Sum.inr (Sum.inr (104, 22)),
    Sum.inr (Sum.inr (168, 21)),
    Sum.inr (Sum.inr (226, 20)),
    Sum.inr (Sum.inr (311, 4)),
    Sum.inr (Sum.inr (316, 5)),
    Sum.inr (Sum.inr (311, 6)),
    Sum.inr (Sum.inr (311, 7)),
    Sum.inr (Sum.inr (41, 13)),
    Sum.inr (Sum.inr (168, 14)),
    Sum.inr (Sum.inr (226, 12)),
    Sum.inr (Sum.inr (104, 15)),
    Sum.inr (Sum.inr (226, 10)),
    Sum.inr (Sum.inr (41, 8)),
    Sum.inr (Sum.inr (168, 9)),
    Sum.inr (Sum.inr (104, 11)),
    Sum.inr (Sum.inr (316, 16)),
    Sum.inr (Sum.inr (316, 17)),
    Sum.inr (Sum.inr (311, 18)),
    Sum.inr (Sum.inr (316, 19)),
    Sum.inr (Sum.inr (226, 3)),
    Sum.inr (Sum.inr (168, 2)),
    Sum.inr (Sum.inr (104, 1)),
    Sum.inr (Sum.inr (41, 0)),
    Sum.inr (Sum.inl (214, 39)),
    Sum.inr (Sum.inl (208, 54)),
    Sum.inr (Sum.inl (151, 25)),
    Sum.inr (Sum.inl (174, 6)),
    Sum.inr (Sum.inl (39, 14)),
    Sum.inr (Sum.inl (19, 1)),
    Sum.inr (Sum.inl (39, 30)),
    Sum.inr (Sum.inl (39, 33)),
    Sum.inr (Sum.inl (214, 56)),
    Sum.inr (Sum.inl (151, 6)),
    Sum.inr (Sum.inl (174, 25)),
    Sum.inr (Sum.inl (208, 41)),
    Sum.inr (Sum.inl (174, 41)),
    Sum.inr (Sum.inl (214, 8)),
    Sum.inr (Sum.inl (151, 54)),
    Sum.inr (Sum.inl (208, 25)),
    Sum.inr (Sum.inl (19, 30)),
    Sum.inr (Sum.inl (19, 46)),
    Sum.inr (Sum.inl (39, 49)),
    Sum.inr (Sum.inl (19, 49)),
    Sum.inr (Sum.inl (174, 54)),
    Sum.inr (Sum.inl (151, 41)),
    Sum.inr (Sum.inl (208, 6)),
    Sum.inr (Sum.inl (214, 23)),
    Sum.inr (Sum.inl (211, 47)),
    Sum.inr (Sum.inl (205, 62)),
    Sum.inr (Sum.inl (148, 17)),
    Sum.inr (Sum.inl (171, 14)),
    Sum.inr (Sum.inl (36, 59)),
    Sum.inr (Sum.inl (16, 7)),
    Sum.inr (Sum.inl (36, 62)),
    Sum.inr (Sum.inl (36, 50)),
    Sum.inr (Sum.inl (211, 48)),
    Sum.inr (Sum.inl (148, 14)),
    Sum.inr (Sum.inl (171, 17)),
    Sum.inr (Sum.inl (205, 33)),
    Sum.inr (Sum.inl (171, 47)),
    Sum.inr (Sum.inl (211, 14)),
    Sum.inr (Sum.inl (148, 48)),
    Sum.inr (Sum.inl (205, 31)),
    Sum.inr (Sum.inl (16, 24)),
    Sum.inr (Sum.inl (16, 40)),
    Sum.inr (Sum.inl (36, 55)),
    Sum.inr (Sum.inl (16, 55)),
    Sum.inr (Sum.inl (171, 48)),
    Sum.inr (Sum.inl (148, 47)),
    Sum.inr (Sum.inl (205, 0)),
    Sum.inr (Sum.inl (211, 17)),
    Sum.inr (Sum.inl (188, 11)),
    Sum.inr (Sum.inl (187, 14)),
    Sum.inr (Sum.inl (143, 53)),
    Sum.inr (Sum.inl (166, 2)),
    Sum.inr (Sum.inl (31, 27)),
    Sum.inr (Sum.inl (11, 1)),
    Sum.inr (Sum.inl (31, 30)),
    Sum.inr (Sum.inl (31, 18)),
    Sum.inr (Sum.inl (188, 14)),
    Sum.inr (Sum.inl (143, 48)),
    Sum.inr (Sum.inl (166, 7)),
    Sum.inr (Sum.inl (187, 11)),
    Sum.inr (Sum.inl (166, 57)),
    Sum.inr (Sum.inl (188, 48)),
    Sum.inr (Sum.inl (143, 14)),
    Sum.inr (Sum.inl (187, 53)),
    Sum.inr (Sum.inl (11, 30)),
    Sum.inr (Sum.inl (11, 46)),
    Sum.inr (Sum.inl (31, 23)),
    Sum.inr (Sum.inl (11, 49)),
    Sum.inr (Sum.inl (166, 60)),
    Sum.inr (Sum.inl (143, 11)),
    Sum.inr (Sum.inl (187, 48)),
    Sum.inr (Sum.inl (188, 53)),
    Sum.inr (Sum.inl (212, 22)),
    Sum.inr (Sum.inl (206, 19)),
    Sum.inr (Sum.inl (149, 23)),
    Sum.inr (Sum.inl (172, 63)),
    Sum.inr (Sum.inl (37, 43)),
    Sum.inr (Sum.inl (17, 36)),
    Sum.inr (Sum.inl (37, 46)),
    Sum.inr (Sum.inl (37, 34)),
    Sum.inr (Sum.inl (212, 19)),
    Sum.inr (Sum.inl (149, 18)),
    Sum.inr (Sum.inl (172, 58)),
    Sum.inr (Sum.inl (206, 22)),
    Sum.inr (Sum.inl (172, 54)),
    Sum.inr (Sum.inl (212, 31)),
    Sum.inr (Sum.inl (149, 30)),
    Sum.inr (Sum.inl (206, 26)),
    Sum.inr (Sum.inl (17, 46)),
    Sum.inr (Sum.inl (17, 45)),
    Sum.inr (Sum.inl (37, 39)),
    Sum.inr (Sum.inl (17, 39)),
    Sum.inr (Sum.inl (172, 51)),
    Sum.inr (Sum.inl (149, 27)),
    Sum.inr (Sum.inl (206, 31)),
    Sum.inr (Sum.inl (212, 26)),
    Sum.inr (Sum.inr (34, 23)),
    Sum.inr (Sum.inr (99, 22)),
    Sum.inr (Sum.inr (163, 21)),
    Sum.inr (Sum.inr (233, 20)),
    Sum.inr (Sum.inr (316, 4)),
    Sum.inr (Sum.inr (311, 5)),
    Sum.inr (Sum.inr (316, 6)),
    Sum.inr (Sum.inr (316, 7)),
    Sum.inr (Sum.inr (34, 13)),
    Sum.inr (Sum.inr (163, 14)),
    Sum.inr (Sum.inr (233, 12)),
    Sum.inr (Sum.inr (99, 15)),
    Sum.inr (Sum.inr (233, 10)),
    Sum.inr (Sum.inr (34, 8)),
    Sum.inr (Sum.inr (163, 9)),
    Sum.inr (Sum.inr (99, 11)),
    Sum.inr (Sum.inr (311, 16)),
    Sum.inr (Sum.inr (311, 17)),
    Sum.inr (Sum.inr (316, 18)),
    Sum.inr (Sum.inr (311, 19)),
    Sum.inr (Sum.inr (233, 3)),
    Sum.inr (Sum.inr (163, 2)),
    Sum.inr (Sum.inr (99, 1)),
    Sum.inr (Sum.inr (34, 0)),
    Sum.inr (Sum.inr (35, 13)),
    Sum.inr (Sum.inr (98, 15)),
    Sum.inr (Sum.inr (162, 14)),
    Sum.inr (Sum.inr (232, 12)),
    Sum.inr (Sum.inr (317, 4)),
    Sum.inr (Sum.inr (310, 5)),
    Sum.inr (Sum.inr (317, 6)),
    Sum.inr (Sum.inr (317, 7)),
    Sum.inr (Sum.inr (35, 23)),
    Sum.inr (Sum.inr (162, 21)),
    Sum.inr (Sum.inr (232, 20)),
    Sum.inr (Sum.inr (98, 22)),
    Sum.inr (Sum.inr (232, 3)),
    Sum.inr (Sum.inr (35, 0)),
    Sum.inr (Sum.inr (162, 2)),
    Sum.inr (Sum.inr (98, 1)),
    Sum.inr (Sum.inr (310, 16)),
    Sum.inr (Sum.inr (310, 17)),
    Sum.inr (Sum.inr (317, 18)),
    Sum.inr (Sum.inr (310, 19)),
    Sum.inr (Sum.inr (232, 10)),
    Sum.inr (Sum.inr (162, 9)),
    Sum.inr (Sum.inr (98, 11)),
    Sum.inr (Sum.inr (35, 8)),
    Sum.inr (Sum.inr (32, 8)),
    Sum.inr (Sum.inr (97, 11)),
    Sum.inr (Sum.inr (161, 9)),
    Sum.inr (Sum.inr (235, 10)),
    Sum.inr (Sum.inr (318, 4)),
    Sum.inr (Sum.inr (309, 5)),
    Sum.inr (Sum.inr (318, 6)),
    Sum.inr (Sum.inr (318, 7)),
    Sum.inr (Sum.inr (32, 0)),
    Sum.inr (Sum.inr (161, 2)),
    Sum.inr (Sum.inr (235, 3)),
    Sum.inr (Sum.inr (97, 1)),
    Sum.inr (Sum.inr (235, 20)),
    Sum.inr (Sum.inr (32, 23)),
    Sum.inr (Sum.inr (161, 21)),
    Sum.inr (Sum.inr (97, 22)),
    Sum.inr (Sum.inr (309, 16)),
    Sum.inr (Sum.inr (309, 17)),
    Sum.inr (Sum.inr (318, 18)),
    Sum.inr (Sum.inr (309, 19)),
    Sum.inr (Sum.inr (235, 12)),
    Sum.inr (Sum.inr (161, 14)),
    Sum.inr (Sum.inr (97, 15)),
    Sum.inr (Sum.inr (32, 13)),
    Sum.inr (Sum.inr (42, 0)),
    Sum.inr (Sum.inr (107, 1)),
    Sum.inr (Sum.inr (171, 2)),
    Sum.inr (Sum.inr (225, 3)),
    Sum.inr (Sum.inr (308, 4)),
    Sum.inr (Sum.inr (319, 5)),
    Sum.inr (Sum.inr (308, 6)),
    Sum.inr (Sum.inr (308, 7)),
    Sum.inr (Sum.inr (42, 8)),
    Sum.inr (Sum.inr (171, 9)),
    Sum.inr (Sum.inr (225, 10)),
    Sum.inr (Sum.inr (107, 11)),
    Sum.inr (Sum.inr (225, 12)),
    Sum.inr (Sum.inr (42, 13)),
    Sum.inr (Sum.inr (171, 14)),
    Sum.inr (Sum.inr (107, 15))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock078Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨19968 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock078InputMaskData : ℕ :=
  sixthHex% [
    "b7db2b9ddb2ba2d32bc8d32b8beb2b89e32b8aeb2bc8e32b84fb2b8cfb2b",
    "80fb2bc8fb2bf8032bd80b2be80b2b88032ba29b2a94932a8f932af99b2a",
    "9e532a80532aa7532af9532a86332aac332a933b2af93b2aba0b2ab8032a",
    "bb0b2af9032ab5132abd132ab1132af9132ac9e32ae9eb2ad9eb2ab9e32a",
    "89ab29bfa329a4a329d2ab29b56329ab63298c6329d26329ad0b29870b29",
    "b80329d20329913329933b29903329d23b299e23299623299a2329d22329",
    "e2d329c2db29f2db2992d329f84328ce4b28d54b28a34328c48b28da8b28",
    "fd8b28a38b28dce328f6e328c9eb28a3eb28e0d328e2db28e1d328a3db28",
    "efcb28e7cb28ebcb28a3cb28933328b33b28833b28e3332888b327bebb27",
    "a5bb27d3b327b47b27aa7b278d7b27d37b27ac1327861327b91b27d31b27",
    "902327922b27912327d32b279f33279733279b3327d33327e3cb27c3c327",
    "f3c32793cb27b95b268f5326945326e25b268593269b9326bc9326e29326",
    "9dfb26b7fb2688f326e2f326a1c326a3cb26a0c326e2cb26aedb26a6db26",
    "aadb26e2db26d22b26f22326c22326a22b26926b25a46325bf6325c96b25",
    "aea325b0a32597a325c9a325b6c3259cc325a3cb25c9cb258afb2588f325",
    "8bfb25c9f32585eb258deb2581eb25c9eb25f91b25d91325e91325891b25",
    "e38324d58b24ce8b24b88324df4b24c14b24e64b24b84b24c72b24ed2b24",
    "d22324b82324fb1b24f91324fa1b24b81324f40324fc0324f00324b80324",
    "88fb24a8f32498f324f8fb24b803238e0b23950b23e3032384c3239ac323",
    "bdc323e3c3239ca323b6a32389ab23e3ab23a09323a29b23a19323e39b23",
    "af8323a78323ab8323e38323d37323f37b23c37b23a37323c9eb22ffe322",
    "e4e32292eb22f52b22eb2b22cc2b22922b22ed4b22c74b22f84322924322",
    "d17322d37b22d07322927b22de6b22d66b22da6b22926b22a29322829b22",
    "b29b22d29322e2db21d4d321cfd321b9db21de1b21c01b21e71b21b91b21",
    "c67321ec7321d37b21b97b21fa4b21f84321fb4b21b94321f55b21fd5b21",
    "f15b21b95b2189a321a9ab2199ab21f9a321"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock078InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock078InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock078OutputMaskData : ℕ :=
  sixthHex% [
    "b8c98b845aabcdc8ba845b9184f98bc56b919362aba7f0ba8524f48d2cf4",
    "b424ffc92cf4b48391c18aabe7198be710ba8a60b0dc6181d1faa1f2fb9b",
    "ed6cf5c66cfed46cf58a6cf5cec981f25aa1bbc8b0f25b9b83b981c22b9b",
    "9422a1a0b0b0f324fefb2cfec224f5bf2cfeb3c39bc6caa1e05981e050b0",
    "8968b3df6982d2f2a2f1f398ee64f6c564fdd764f68964f6bc81828012a2",
    "c980b3801398f1f182b06398e66aa2d2f8b3f02cfdf824fdc12cf6bc24fd",
    "b0cb98c5c2a2e35182e358b38a68b2dc6983d1f2a3f2f399ed64f7c664fc",
    "d464f78a64f7bf81838312a3ca80b283139983b183c22399942aa3a0b8b2",
    "f32cfcfb24fcc22cf7bf24fcc28b99b782a39111839118b2760c49200d78",
    "2d96580e976211000c3a000728000c76000c43e5787f765836e4497f7762",
    "7fd5783e4762684e585cdc497e08077600074f080c3200074faf623aa658",
    "1c35781c3c49000c43560d725b96527897686700064c000d5e0006000006",
    "35e57209765240e4430977687895723907686f0e525b9c4308080d00000d",
    "39080644000d48ef683de6521b75721b7c43030440550571589e517b9f6b",
    "6408054f080e5d080503080547ad717b3e5132ac407b3f6b0add714b4f6b",
    "1d465129d4400b000e03080e3a000547080e4be76b3eee51187d71187440",
    "0004415605705b9e50789f6a6708044c080f5e080400080444ad70783e50",
    "31ac41783f6a789d70390f6a6f06505b944108000f00080f39000444080f",
    "39a76a4cae506a3d706a3441ce20b998218895baa8b6bb92d86cfcf36cf7",
    "e16cfcbf6cfcfbc988c75aa88ec8b9c75b92c7f988866b92d062a8e4f0b9",
    "c624f7ce2cf7f724fc8a2cf786c392f3caa8d55988d550b9cd20b89b2189",
    "96baa9b5bb93db6cfdf06cf6e26cfdbc6cfdf8c989c45aa98dc8b8c45b93",
    "b5b989f42b93a222a996b0b8c524f6cd2cf6f424fd892cf6f48393818aa9",
    "a71989a710b8ce28bb98298a95b2aab6b390d864fef364f5e164febf64fe",
    "8a818ab612aaff80bbb61390c7f18a866390d06aaae4f8bbc62cf5ce24f5",
    "f72cfe8a24f5f78b908282aaa4118aa418bb"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock078OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock078OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock078InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock078InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock078InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock078OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7e185f85f7e18617df96175d7df8617df7df85f7e17e17e1",
    "7df7df6df8e37e185f7e185f7e185f7e185f8617df96175d8617df7df7df",
    "85f7e185f85f7e18616e18e37df7e18617e186185f7df85f7e17df6e18e3",
    "7e17df7e17df86185f7df7e185f7df95f75d7df7e17df85f7df7e17df85f",
    "7e17df6e18e385f8617e17df86185f86185f8617df96175d8617df7df7df",
    "85f7e185f85f7df7df6df8e37e185f7e185f7e185f7e185f8617df96175d",
    "7df8617df7df85f7e17e17e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock078OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock078OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block078_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock078Input a) =
      generatedSixthXiShortBlock078InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock078Output a) =
      generatedSixthXiShortBlock078OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock078Input a) =
      generatedSixthXiShortBlock078InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock078Output a) =
      generatedSixthXiShortBlock078OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block078_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock078InputMask a) =
      generatedSixthXiShortBlock078OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock078InputMask a)) *
      generatedSixthXiShortBlock078InputNumerator a =
        generatedSixthXiShortBlock078OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block078_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock078Input a
    let y := generatedSixthXiShortBlock078Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block078_cache a
  have hs := generatedSixth_xi_short_block078_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block078_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock078Input a
    let y := generatedSixthXiShortBlock078Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block078_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block078_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock078Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block078_certificate a).1
    (generatedSixth_xi_short_block078_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
