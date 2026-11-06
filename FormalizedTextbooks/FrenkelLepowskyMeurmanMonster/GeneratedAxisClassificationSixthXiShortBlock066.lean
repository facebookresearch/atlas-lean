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
def generatedSixthXiShortBlock066Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (160, 0)),
    Sum.inr (Sum.inr (225, 1)),
    Sum.inr (Sum.inr (33, 2)),
    Sum.inr (Sum.inr (107, 3)),
    Sum.inr (Sum.inr (446, 4)),
    Sum.inr (Sum.inr (437, 5)),
    Sum.inr (Sum.inr (446, 6)),
    Sum.inr (Sum.inr (446, 7)),
    Sum.inr (Sum.inr (160, 8)),
    Sum.inr (Sum.inr (33, 9)),
    Sum.inr (Sum.inr (107, 10)),
    Sum.inr (Sum.inr (225, 11)),
    Sum.inr (Sum.inr (107, 12)),
    Sum.inr (Sum.inr (160, 13)),
    Sum.inr (Sum.inr (33, 14)),
    Sum.inr (Sum.inr (225, 15)),
    Sum.inr (Sum.inr (437, 16)),
    Sum.inr (Sum.inr (437, 17)),
    Sum.inr (Sum.inr (446, 18)),
    Sum.inr (Sum.inr (437, 19)),
    Sum.inr (Sum.inr (107, 20)),
    Sum.inr (Sum.inr (33, 21)),
    Sum.inr (Sum.inr (225, 22)),
    Sum.inr (Sum.inr (160, 23)),
    Sum.inr (Sum.inr (168, 23)),
    Sum.inr (Sum.inr (233, 22)),
    Sum.inr (Sum.inr (41, 21)),
    Sum.inr (Sum.inr (99, 20)),
    Sum.inr (Sum.inr (438, 4)),
    Sum.inr (Sum.inr (445, 5)),
    Sum.inr (Sum.inr (438, 6)),
    Sum.inr (Sum.inr (438, 7)),
    Sum.inr (Sum.inr (168, 13)),
    Sum.inr (Sum.inr (41, 14)),
    Sum.inr (Sum.inr (99, 12)),
    Sum.inr (Sum.inr (233, 15)),
    Sum.inr (Sum.inr (99, 10)),
    Sum.inr (Sum.inr (168, 8)),
    Sum.inr (Sum.inr (41, 9)),
    Sum.inr (Sum.inr (233, 11)),
    Sum.inr (Sum.inr (445, 16)),
    Sum.inr (Sum.inr (445, 17)),
    Sum.inr (Sum.inr (438, 18)),
    Sum.inr (Sum.inr (445, 19)),
    Sum.inr (Sum.inr (99, 3)),
    Sum.inr (Sum.inr (41, 2)),
    Sum.inr (Sum.inr (233, 1)),
    Sum.inr (Sum.inr (168, 0)),
    Sum.inr (Sum.inr (169, 13)),
    Sum.inr (Sum.inr (232, 15)),
    Sum.inr (Sum.inr (40, 14)),
    Sum.inr (Sum.inr (98, 12)),
    Sum.inr (Sum.inr (439, 4)),
    Sum.inr (Sum.inr (444, 5)),
    Sum.inr (Sum.inr (439, 6)),
    Sum.inr (Sum.inr (439, 7)),
    Sum.inr (Sum.inr (169, 23)),
    Sum.inr (Sum.inr (40, 21)),
    Sum.inr (Sum.inr (98, 20)),
    Sum.inr (Sum.inr (232, 22)),
    Sum.inr (Sum.inr (98, 3)),
    Sum.inr (Sum.inr (169, 0)),
    Sum.inr (Sum.inr (40, 2)),
    Sum.inr (Sum.inr (232, 1)),
    Sum.inr (Sum.inr (444, 16)),
    Sum.inr (Sum.inr (444, 17)),
    Sum.inr (Sum.inr (439, 18)),
    Sum.inr (Sum.inr (444, 19)),
    Sum.inr (Sum.inr (98, 10)),
    Sum.inr (Sum.inr (40, 9)),
    Sum.inr (Sum.inr (232, 11)),
    Sum.inr (Sum.inr (169, 8)),
    Sum.inr (Sum.inl (211, 53)),
    Sum.inr (Sum.inl (205, 50)),
    Sum.inr (Sum.inl (148, 11)),
    Sum.inr (Sum.inl (171, 2)),
    Sum.inr (Sum.inl (36, 11)),
    Sum.inr (Sum.inl (16, 4)),
    Sum.inr (Sum.inl (36, 14)),
    Sum.inr (Sum.inl (36, 2)),
    Sum.inr (Sum.inl (211, 42)),
    Sum.inr (Sum.inl (148, 20)),
    Sum.inr (Sum.inl (171, 29)),
    Sum.inr (Sum.inl (205, 45)),
    Sum.inr (Sum.inl (171, 35)),
    Sum.inr (Sum.inl (211, 20)),
    Sum.inr (Sum.inl (148, 42)),
    Sum.inr (Sum.inl (205, 19)),
    Sum.inr (Sum.inl (16, 27)),
    Sum.inr (Sum.inl (16, 43)),
    Sum.inr (Sum.inl (36, 7)),
    Sum.inr (Sum.inl (16, 52)),
    Sum.inr (Sum.inl (171, 60)),
    Sum.inr (Sum.inl (148, 53)),
    Sum.inr (Sum.inl (205, 12)),
    Sum.inr (Sum.inl (211, 11)),
    Sum.inr (Sum.inl (214, 42)),
    Sum.inr (Sum.inl (208, 53)),
    Sum.inr (Sum.inl (151, 23)),
    Sum.inr (Sum.inl (174, 3)),
    Sum.inr (Sum.inl (39, 11)),
    Sum.inr (Sum.inl (19, 4)),
    Sum.inr (Sum.inl (39, 27)),
    Sum.inr (Sum.inl (39, 36)),
    Sum.inr (Sum.inl (214, 53)),
    Sum.inr (Sum.inl (151, 8)),
    Sum.inr (Sum.inl (174, 28)),
    Sum.inr (Sum.inl (208, 42)),
    Sum.inr (Sum.inl (174, 44)),
    Sum.inr (Sum.inl (214, 5)),
    Sum.inr (Sum.inl (151, 56)),
    Sum.inr (Sum.inl (208, 26)),
    Sum.inr (Sum.inl (19, 27)),
    Sum.inr (Sum.inl (19, 43)),
    Sum.inr (Sum.inl (39, 52)),
    Sum.inr (Sum.inl (19, 52)),
    Sum.inr (Sum.inl (174, 51)),
    Sum.inr (Sum.inl (151, 39)),
    Sum.inr (Sum.inl (208, 5)),
    Sum.inr (Sum.inl (214, 26)),
    Sum.inr (Sum.inl (212, 27)),
    Sum.inr (Sum.inl (206, 44)),
    Sum.inr (Sum.inl (149, 37)),
    Sum.inr (Sum.inl (172, 32)),
    Sum.inr (Sum.inl (37, 52)),
    Sum.inr (Sum.inl (17, 59)),
    Sum.inr (Sum.inl (37, 49)),
    Sum.inr (Sum.inl (37, 61)),
    Sum.inr (Sum.inl (212, 30)),
    Sum.inr (Sum.inl (149, 32)),
    Sum.inr (Sum.inl (172, 37)),
    Sum.inr (Sum.inl (206, 41)),
    Sum.inr (Sum.inl (172, 41)),
    Sum.inr (Sum.inl (212, 18)),
    Sum.inr (Sum.inl (149, 44)),
    Sum.inr (Sum.inl (206, 37)),
    Sum.inr (Sum.inl (17, 49)),
    Sum.inr (Sum.inl (17, 50)),
    Sum.inr (Sum.inl (37, 56)),
    Sum.inr (Sum.inl (17, 56)),
    Sum.inr (Sum.inl (172, 44)),
    Sum.inr (Sum.inl (149, 41)),
    Sum.inr (Sum.inl (206, 32)),
    Sum.inr (Sum.inl (212, 23)),
    Sum.inr (Sum.inl (188, 33)),
    Sum.inr (Sum.inl (187, 62)),
    Sum.inr (Sum.inl (143, 31)),
    Sum.inr (Sum.inl (166, 26)),
    Sum.inr (Sum.inl (31, 59)),
    Sum.inr (Sum.inl (11, 7)),
    Sum.inr (Sum.inl (31, 62)),
    Sum.inr (Sum.inl (31, 50)),
    Sum.inr (Sum.inl (188, 36)),
    Sum.inr (Sum.inl (143, 26)),
    Sum.inr (Sum.inl (166, 31)),
    Sum.inr (Sum.inl (187, 59)),
    Sum.inr (Sum.inl (166, 33)),
    Sum.inr (Sum.inl (188, 26)),
    Sum.inr (Sum.inl (143, 36)),
    Sum.inr (Sum.inl (187, 5)),
    Sum.inr (Sum.inl (11, 24)),
    Sum.inr (Sum.inl (11, 40)),
    Sum.inr (Sum.inl (31, 55)),
    Sum.inr (Sum.inl (11, 55)),
    Sum.inr (Sum.inl (166, 36)),
    Sum.inr (Sum.inl (143, 33)),
    Sum.inr (Sum.inl (187, 0)),
    Sum.inr (Sum.inl (188, 31)),
    Sum.inr (Sum.inr (162, 13)),
    Sum.inr (Sum.inr (227, 15)),
    Sum.inr (Sum.inr (35, 14)),
    Sum.inr (Sum.inr (105, 12)),
    Sum.inr (Sum.inr (444, 4)),
    Sum.inr (Sum.inr (439, 5)),
    Sum.inr (Sum.inr (444, 6)),
    Sum.inr (Sum.inr (444, 7)),
    Sum.inr (Sum.inr (162, 23)),
    Sum.inr (Sum.inr (35, 21)),
    Sum.inr (Sum.inr (105, 20)),
    Sum.inr (Sum.inr (227, 22)),
    Sum.inr (Sum.inr (105, 3)),
    Sum.inr (Sum.inr (162, 0)),
    Sum.inr (Sum.inr (35, 2)),
    Sum.inr (Sum.inr (227, 1)),
    Sum.inr (Sum.inr (439, 16)),
    Sum.inr (Sum.inr (439, 17)),
    Sum.inr (Sum.inr (444, 18)),
    Sum.inr (Sum.inr (439, 19)),
    Sum.inr (Sum.inr (105, 10)),
    Sum.inr (Sum.inr (35, 9)),
    Sum.inr (Sum.inr (227, 11)),
    Sum.inr (Sum.inr (162, 8)),
    Sum.inr (Sum.inr (163, 23)),
    Sum.inr (Sum.inr (226, 22)),
    Sum.inr (Sum.inr (34, 21)),
    Sum.inr (Sum.inr (104, 20)),
    Sum.inr (Sum.inr (445, 4)),
    Sum.inr (Sum.inr (438, 5)),
    Sum.inr (Sum.inr (445, 6)),
    Sum.inr (Sum.inr (445, 7)),
    Sum.inr (Sum.inr (163, 13)),
    Sum.inr (Sum.inr (34, 14)),
    Sum.inr (Sum.inr (104, 12)),
    Sum.inr (Sum.inr (226, 15)),
    Sum.inr (Sum.inr (104, 10)),
    Sum.inr (Sum.inr (163, 8)),
    Sum.inr (Sum.inr (34, 9)),
    Sum.inr (Sum.inr (226, 11)),
    Sum.inr (Sum.inr (438, 16)),
    Sum.inr (Sum.inr (438, 17)),
    Sum.inr (Sum.inr (445, 18)),
    Sum.inr (Sum.inr (438, 19)),
    Sum.inr (Sum.inr (104, 3)),
    Sum.inr (Sum.inr (34, 2)),
    Sum.inr (Sum.inr (226, 1)),
    Sum.inr (Sum.inr (163, 0)),
    Sum.inr (Sum.inr (171, 0)),
    Sum.inr (Sum.inr (234, 1)),
    Sum.inr (Sum.inr (42, 2)),
    Sum.inr (Sum.inr (96, 3)),
    Sum.inr (Sum.inr (437, 4)),
    Sum.inr (Sum.inr (446, 5)),
    Sum.inr (Sum.inr (437, 6)),
    Sum.inr (Sum.inr (437, 7)),
    Sum.inr (Sum.inr (171, 8)),
    Sum.inr (Sum.inr (42, 9)),
    Sum.inr (Sum.inr (96, 10)),
    Sum.inr (Sum.inr (234, 11)),
    Sum.inr (Sum.inr (96, 12)),
    Sum.inr (Sum.inr (171, 13)),
    Sum.inr (Sum.inr (42, 14)),
    Sum.inr (Sum.inr (234, 15)),
    Sum.inr (Sum.inr (446, 16)),
    Sum.inr (Sum.inr (446, 17)),
    Sum.inr (Sum.inr (437, 18)),
    Sum.inr (Sum.inr (446, 19)),
    Sum.inr (Sum.inr (96, 20)),
    Sum.inr (Sum.inr (42, 21)),
    Sum.inr (Sum.inr (234, 22)),
    Sum.inr (Sum.inr (171, 23)),
    Sum.inr (Sum.inr (161, 8)),
    Sum.inr (Sum.inr (224, 11)),
    Sum.inr (Sum.inr (32, 9)),
    Sum.inr (Sum.inr (106, 10)),
    Sum.inr (Sum.inr (447, 4)),
    Sum.inr (Sum.inr (436, 5)),
    Sum.inr (Sum.inr (447, 6)),
    Sum.inr (Sum.inr (447, 7)),
    Sum.inr (Sum.inr (161, 0)),
    Sum.inr (Sum.inr (32, 2)),
    Sum.inr (Sum.inr (106, 3)),
    Sum.inr (Sum.inr (224, 1)),
    Sum.inr (Sum.inr (106, 20)),
    Sum.inr (Sum.inr (161, 23)),
    Sum.inr (Sum.inr (32, 21)),
    Sum.inr (Sum.inr (224, 22))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock066Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨16896 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock066InputMaskData : ℕ :=
  sixthHex% [
    "bbd93b91d13baed93bc4d13b87e13b85e93b86e93bc4e13b88f93b80f93b",
    "8cf93bc4f93bf4093bd4093be4013b84013bbc913a8a913a91993ae7993a",
    "80513a9e513ab9513ae7513a98313ab2393a8d313ae7393aa4013aa6093a",
    "a5093ae7013aab113aa3113aaf113ae7113ad7e93af7e93ac7e13aa7e13a",
    "aaa1399ca13987a939f1a939966139886139af6139f161398e0939a40139",
    "9b0939f10139b23939b03139b33139f13939bd2139b52139b92139f12139",
    "c1d939e1d939d1d139b1d139c94938ff4938e44138924138f58938eb8938",
    "cc8938928938ede138c7e938f8e13892e938d1d938d3d138d0d13892d938",
    "dec938d6c938dac93892c938a23938823938b23138d23138a9b9379fb937",
    "84b137f2b1379579378b7937ac7937f279378d1137a71937981137f21937",
    "b12937b32137b02137f22937be3137b63137ba3137f23137c2c137e2c137",
    "d2c937b2c9378a5136bc5136a75936d15936b69136a891368f9136d19136",
    "aef93684f136bbf936d1f13692c93690c13693c136d1c9369dd93695d936",
    "99d936d1d936e12136c12136f129369129369c6135aa6135b16935c76935",
    "a0a135bea13599a135c7a135b8c13592c935adc135c7c93584f13586f935",
    "85f935c7f1358be93583e9358fe935c7e935f71135d71135e71935871935",
    "ff8934c98934d28134a48134c34934dd4934fa4934a44934db2934f12134",
    "ce2934a42134e71134e51934e61934a41134e80134e00134ec0134a40134",
    "94f134b4f13484f934e4f934890933bf0933a40133d20133b5c133abc133",
    "8cc133d2c133ada13387a933b8a133d2a933919933939133909133d29933",
    "9e81339681339a8133d28133e27933c27933f27133927133eae132dce132",
    "c7e932b1e932d62932c82932ef2932b12932ce4932e44132db4932b14132",
    "f27932f07132f37132b17932fd6932f56932f96932b16932819932a19932",
    "919132f19132fcd131cad131d1d931a7d931c01931de1931f91931a71931",
    "d87131f27931cd7131a77931e44131e64931e54931a74131eb5931e35931",
    "ef5931a7593197a931b7a93187a131e7a131"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock066InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock066InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock066OutputMaskData : ℕ :=
  sixthHex% [
    "db1b9096c8b0df5aa1e7898a966b90d7f98af0b0b0c422a1e6f6efeefeef",
    "d7f6e4aafeefa6118aa258b0f58b9084c2a18afaabadbb9ad160ba832180",
    "9cb6eeb7b6e5a5b6eefbb6eebf139af2c0babb52ab83818083239ac2b180",
    "e5f8bad16aab82fee58af6e5b3feeecef6e5b35980b710bae0c39a918aab",
    "81f2a3a6b392da68b288298897bee6bcbeedaebee6f0bee6c55b928888b2",
    "c11aa3f9c988f96b92b8f9889fb0b2ab22a389f6ed81feedb8f6e6c5feed",
    "b85188bc18b2ebcb929a82a390faa2b7bb93cb60b399218986b6e7adb6ec",
    "bfb6e7e1b6e7d453939980b3d012a2e8c189992393d8b189fff8b3cb6aa2",
    "98feec90f6eca9fee7d4f6ecd81989dc50b38b8393facaa24e4443690572",
    "15de52479f6858080673080d6108063f08060aed72473e520eac43367f68",
    "479d72060f6821465215d44337000d3f080d0600067b080d77e76873ae52",
    "247d725534432a4c490d0d7871d6582397623c000c17000705000c5b000c",
    "6ee5782336586aa44952776252d578134762340e58009c495308075b0007",
    "62080c1f000762af6266e658313578407c492144410605707ade50289f6a",
    "3708041c080f0e080450080414ad70597e5010ec41283f6a289d70690f6a",
    "4e46507ad44158000f50080f69000414080f69a76a6dee503a3d704b7441",
    "304c40170d716bd65139976b2600050d000e1f000541000505a571487651",
    "01e44039376b48d57109476b2e0e511a9c4049080e41000e78080505000e",
    "09ef6b0da6515a75712b3c40d4b2a9f3f3988f28b8dd6982b3beec98bee7",
    "8abeecd4beec901b98ddc8b8945aa9ac8982dd6b989cf982bbb0b88f22a9",
    "adf6e7a5fee79cf6ece1fee79c51829818b8cfcb98be82a9c5baa8e2fb99",
    "9e20b9cc6183a2b6ed89b6e69bb6edc5b6ed811399ccc0b98552a8bd8183",
    "bd2399fcb183dbf8b9ef6aa8bcfee6b4f6e68dfeedf0f6e6fc1983f850b9",
    "af8399decaa8ceb2a0e9f3919528b1c7698ba9bee582beee90bee5cebee5",
    "fb5b91b688b1ff1aa0c7c98bc76b9186f98ba1b0b19522a0b7f6eebffeee",
    "86f6e5fbfeeef7118bf358b1a48b91d5c2a0"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock066OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock066OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock066InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock066InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock066InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock066OutputNumeratorData : ℕ :=
  sixthHex% [
    "8617df8618617e185f85f85f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "8617df96175d8617df7df7df85f7e185f85f86186196175d85f7e185f7e1",
    "85f7e185f7e185f86195f75d85f86185f8617df7e186185f7e18616e18e3",
    "7df7e18617e186185f7df85f85f86195f75d7e17df85f8617df7e17df7e1",
    "85f7df95f75d7df7e17df85f7df7e17df85f86186196175d85f7e185f7e1",
    "85f7e185f7e18617df96175d8617df7df7df85f7e185f85f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock066OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock066OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block066_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock066Input a) =
      generatedSixthXiShortBlock066InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock066Output a) =
      generatedSixthXiShortBlock066OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock066Input a) =
      generatedSixthXiShortBlock066InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock066Output a) =
      generatedSixthXiShortBlock066OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block066_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock066InputMask a) =
      generatedSixthXiShortBlock066OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock066InputMask a)) *
      generatedSixthXiShortBlock066InputNumerator a =
        generatedSixthXiShortBlock066OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block066_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock066Input a
    let y := generatedSixthXiShortBlock066Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block066_cache a
  have hs := generatedSixth_xi_short_block066_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block066_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock066Input a
    let y := generatedSixthXiShortBlock066Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block066_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block066_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock066Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block066_certificate a).1
    (generatedSixth_xi_short_block066_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
