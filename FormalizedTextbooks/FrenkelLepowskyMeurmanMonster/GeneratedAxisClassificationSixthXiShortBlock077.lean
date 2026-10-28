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
def generatedSixthXiShortBlock077Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (451, 0)),
    Sum.inr (Sum.inr (322, 9)),
    Sum.inr (Sum.inr (264, 20)),
    Sum.inr (Sum.inr (386, 15)),
    Sum.inr (Sum.inr (264, 3)),
    Sum.inr (Sum.inr (451, 23)),
    Sum.inr (Sum.inr (322, 14)),
    Sum.inr (Sum.inr (386, 11)),
    Sum.inr (Sum.inr (214, 16)),
    Sum.inr (Sum.inr (214, 17)),
    Sum.inr (Sum.inr (221, 6)),
    Sum.inr (Sum.inr (214, 19)),
    Sum.inr (Sum.inr (264, 10)),
    Sum.inr (Sum.inr (322, 21)),
    Sum.inr (Sum.inr (386, 1)),
    Sum.inr (Sum.inr (451, 13)),
    Sum.inr (Sum.inr (323, 0)),
    Sum.inr (Sum.inr (258, 15)),
    Sum.inr (Sum.inr (450, 9)),
    Sum.inr (Sum.inr (392, 20)),
    Sum.inr (Sum.inr (93, 7)),
    Sum.inr (Sum.inr (86, 5)),
    Sum.inr (Sum.inr (93, 18)),
    Sum.inr (Sum.inr (93, 4)),
    Sum.inr (Sum.inr (323, 8)),
    Sum.inr (Sum.inr (450, 2)),
    Sum.inr (Sum.inr (392, 12)),
    Sum.inr (Sum.inr (258, 22)),
    Sum.inr (Sum.inr (392, 10)),
    Sum.inr (Sum.inr (323, 13)),
    Sum.inr (Sum.inr (450, 21)),
    Sum.inr (Sum.inr (258, 1)),
    Sum.inr (Sum.inr (86, 16)),
    Sum.inr (Sum.inr (86, 17)),
    Sum.inr (Sum.inr (93, 6)),
    Sum.inr (Sum.inr (86, 19)),
    Sum.inr (Sum.inr (392, 3)),
    Sum.inr (Sum.inr (450, 14)),
    Sum.inr (Sum.inr (258, 11)),
    Sum.inr (Sum.inr (323, 23)),
    Sum.inr (Sum.inl (158, 17)),
    Sum.inr (Sum.inl (157, 36)),
    Sum.inr (Sum.inl (140, 6)),
    Sum.inr (Sum.inl (153, 38)),
    Sum.inr (Sum.inl (28, 4)),
    Sum.inr (Sum.inl (8, 0)),
    Sum.inr (Sum.inl (28, 12)),
    Sum.inr (Sum.inl (28, 14)),
    Sum.inr (Sum.inl (158, 62)),
    Sum.inr (Sum.inl (140, 41)),
    Sum.inr (Sum.inl (153, 4)),
    Sum.inr (Sum.inl (157, 6)),
    Sum.inr (Sum.inl (153, 36)),
    Sum.inr (Sum.inl (158, 42)),
    Sum.inr (Sum.inl (140, 20)),
    Sum.inr (Sum.inl (157, 59)),
    Sum.inr (Sum.inl (8, 32)),
    Sum.inr (Sum.inl (8, 16)),
    Sum.inr (Sum.inl (28, 6)),
    Sum.inr (Sum.inl (8, 48)),
    Sum.inr (Sum.inl (153, 6)),
    Sum.inr (Sum.inl (140, 59)),
    Sum.inr (Sum.inl (157, 25)),
    Sum.inr (Sum.inl (158, 5)),
    Sum.inr (Sum.inl (213, 41)),
    Sum.inr (Sum.inl (207, 7)),
    Sum.inr (Sum.inl (150, 49)),
    Sum.inr (Sum.inl (173, 5)),
    Sum.inr (Sum.inl (38, 37)),
    Sum.inr (Sum.inl (18, 9)),
    Sum.inr (Sum.inl (38, 45)),
    Sum.inr (Sum.inl (38, 47)),
    Sum.inr (Sum.inl (213, 54)),
    Sum.inr (Sum.inl (150, 17)),
    Sum.inr (Sum.inl (173, 39)),
    Sum.inr (Sum.inl (207, 38)),
    Sum.inr (Sum.inl (173, 37)),
    Sum.inr (Sum.inl (213, 8)),
    Sum.inr (Sum.inl (150, 57)),
    Sum.inr (Sum.inl (207, 57)),
    Sum.inr (Sum.inl (18, 41)),
    Sum.inr (Sum.inl (18, 25)),
    Sum.inr (Sum.inl (38, 39)),
    Sum.inr (Sum.inl (18, 57)),
    Sum.inr (Sum.inl (173, 7)),
    Sum.inr (Sum.inl (150, 25)),
    Sum.inr (Sum.inl (207, 24)),
    Sum.inr (Sum.inl (213, 23)),
    Sum.inr (Sum.inl (119, 11)),
    Sum.inr (Sum.inl (118, 42)),
    Sum.inr (Sum.inl (112, 27)),
    Sum.inr (Sum.inl (114, 36)),
    Sum.inr (Sum.inl (25, 52)),
    Sum.inr (Sum.inl (5, 12)),
    Sum.inr (Sum.inl (25, 60)),
    Sum.inr (Sum.inl (25, 62)),
    Sum.inr (Sum.inl (119, 26)),
    Sum.inr (Sum.inl (112, 9)),
    Sum.inr (Sum.inl (114, 52)),
    Sum.inr (Sum.inl (118, 53)),
    Sum.inr (Sum.inl (114, 54)),
    Sum.inr (Sum.inl (119, 36)),
    Sum.inr (Sum.inl (112, 38)),
    Sum.inr (Sum.inl (118, 29)),
    Sum.inr (Sum.inl (5, 44)),
    Sum.inr (Sum.inl (5, 28)),
    Sum.inr (Sum.inl (25, 54)),
    Sum.inr (Sum.inl (5, 60)),
    Sum.inr (Sum.inl (114, 38)),
    Sum.inr (Sum.inl (112, 52)),
    Sum.inr (Sum.inl (118, 2)),
    Sum.inr (Sum.inl (119, 53)),
    Sum.inr (Sum.inl (53, 58)),
    Sum.inr (Sum.inl (52, 11)),
    Sum.inr (Sum.inl (46, 42)),
    Sum.inr (Sum.inl (48, 10)),
    Sum.inr (Sum.inl (21, 27)),
    Sum.inr (Sum.inl (1, 55)),
    Sum.inr (Sum.inl (21, 19)),
    Sum.inr (Sum.inl (21, 17)),
    Sum.inr (Sum.inl (53, 43)),
    Sum.inr (Sum.inl (46, 59)),
    Sum.inr (Sum.inl (48, 26)),
    Sum.inr (Sum.inl (52, 43)),
    Sum.inr (Sum.inl (48, 14)),
    Sum.inr (Sum.inl (53, 59)),
    Sum.inr (Sum.inl (46, 58)),
    Sum.inr (Sum.inl (52, 42)),
    Sum.inr (Sum.inl (1, 23)),
    Sum.inr (Sum.inl (1, 39)),
    Sum.inr (Sum.inl (21, 25)),
    Sum.inr (Sum.inl (1, 7)),
    Sum.inr (Sum.inl (48, 30)),
    Sum.inr (Sum.inl (46, 43)),
    Sum.inr (Sum.inl (52, 10)),
    Sum.inr (Sum.inl (53, 42)),
    Sum.inr (Sum.inr (328, 0)),
    Sum.inr (Sum.inr (265, 15)),
    Sum.inr (Sum.inr (457, 9)),
    Sum.inr (Sum.inr (387, 20)),
    Sum.inr (Sum.inr (86, 7)),
    Sum.inr (Sum.inr (93, 5)),
    Sum.inr (Sum.inr (86, 18)),
    Sum.inr (Sum.inr (86, 4)),
    Sum.inr (Sum.inr (328, 8)),
    Sum.inr (Sum.inr (457, 2)),
    Sum.inr (Sum.inr (387, 12)),
    Sum.inr (Sum.inr (265, 22)),
    Sum.inr (Sum.inr (387, 10)),
    Sum.inr (Sum.inr (328, 13)),
    Sum.inr (Sum.inr (457, 21)),
    Sum.inr (Sum.inr (265, 1)),
    Sum.inr (Sum.inr (93, 16)),
    Sum.inr (Sum.inr (93, 17)),
    Sum.inr (Sum.inr (86, 6)),
    Sum.inr (Sum.inr (93, 19)),
    Sum.inr (Sum.inr (387, 3)),
    Sum.inr (Sum.inr (457, 14)),
    Sum.inr (Sum.inr (265, 11)),
    Sum.inr (Sum.inr (328, 23)),
    Sum.inr (Sum.inr (456, 8)),
    Sum.inr (Sum.inr (393, 22)),
    Sum.inr (Sum.inr (329, 2)),
    Sum.inr (Sum.inr (259, 12)),
    Sum.inr (Sum.inr (214, 7)),
    Sum.inr (Sum.inr (221, 5)),
    Sum.inr (Sum.inr (214, 18)),
    Sum.inr (Sum.inr (214, 4)),
    Sum.inr (Sum.inr (456, 0)),
    Sum.inr (Sum.inr (329, 9)),
    Sum.inr (Sum.inr (259, 20)),
    Sum.inr (Sum.inr (393, 15)),
    Sum.inr (Sum.inr (259, 3)),
    Sum.inr (Sum.inr (456, 23)),
    Sum.inr (Sum.inr (329, 14)),
    Sum.inr (Sum.inr (393, 11)),
    Sum.inr (Sum.inr (221, 16)),
    Sum.inr (Sum.inr (221, 17)),
    Sum.inr (Sum.inr (214, 6)),
    Sum.inr (Sum.inr (221, 19)),
    Sum.inr (Sum.inr (259, 10)),
    Sum.inr (Sum.inr (329, 21)),
    Sum.inr (Sum.inr (393, 1)),
    Sum.inr (Sum.inr (456, 13)),
    Sum.inr (Sum.inr (267, 13)),
    Sum.inr (Sum.inr (330, 1)),
    Sum.inr (Sum.inr (394, 21)),
    Sum.inr (Sum.inr (448, 10)),
    Sum.inr (Sum.inr (21, 7)),
    Sum.inr (Sum.inr (30, 5)),
    Sum.inr (Sum.inr (21, 18)),
    Sum.inr (Sum.inr (21, 4)),
    Sum.inr (Sum.inr (267, 23)),
    Sum.inr (Sum.inr (394, 14)),
    Sum.inr (Sum.inr (448, 3)),
    Sum.inr (Sum.inr (330, 11)),
    Sum.inr (Sum.inr (448, 20)),
    Sum.inr (Sum.inr (267, 0)),
    Sum.inr (Sum.inr (394, 9)),
    Sum.inr (Sum.inr (330, 15)),
    Sum.inr (Sum.inr (30, 16)),
    Sum.inr (Sum.inr (30, 17)),
    Sum.inr (Sum.inr (21, 6)),
    Sum.inr (Sum.inr (30, 19)),
    Sum.inr (Sum.inr (448, 12)),
    Sum.inr (Sum.inr (394, 2)),
    Sum.inr (Sum.inr (330, 22)),
    Sum.inr (Sum.inr (267, 8)),
    Sum.inr (Sum.inr (384, 23)),
    Sum.inr (Sum.inr (449, 11)),
    Sum.inr (Sum.inr (257, 14)),
    Sum.inr (Sum.inr (331, 3)),
    Sum.inr (Sum.inr (158, 7)),
    Sum.inr (Sum.inr (149, 5)),
    Sum.inr (Sum.inr (158, 18)),
    Sum.inr (Sum.inr (158, 4)),
    Sum.inr (Sum.inr (384, 13)),
    Sum.inr (Sum.inr (257, 21)),
    Sum.inr (Sum.inr (331, 10)),
    Sum.inr (Sum.inr (449, 1)),
    Sum.inr (Sum.inr (331, 12)),
    Sum.inr (Sum.inr (384, 8)),
    Sum.inr (Sum.inr (257, 2)),
    Sum.inr (Sum.inr (449, 22)),
    Sum.inr (Sum.inr (149, 16)),
    Sum.inr (Sum.inr (149, 17)),
    Sum.inr (Sum.inr (158, 6)),
    Sum.inr (Sum.inr (149, 19)),
    Sum.inr (Sum.inr (331, 20)),
    Sum.inr (Sum.inr (257, 9)),
    Sum.inr (Sum.inr (449, 15)),
    Sum.inr (Sum.inr (384, 0)),
    Sum.inr (Sum.inr (33, 0)),
    Sum.inr (Sum.inr (96, 1)),
    Sum.inr (Sum.inr (160, 2)),
    Sum.inr (Sum.inr (234, 3)),
    Sum.inr (Sum.inr (319, 4)),
    Sum.inr (Sum.inr (308, 5)),
    Sum.inr (Sum.inr (319, 6)),
    Sum.inr (Sum.inr (319, 7)),
    Sum.inr (Sum.inr (33, 8)),
    Sum.inr (Sum.inr (160, 9)),
    Sum.inr (Sum.inr (234, 10)),
    Sum.inr (Sum.inr (96, 11)),
    Sum.inr (Sum.inr (234, 12)),
    Sum.inr (Sum.inr (33, 13)),
    Sum.inr (Sum.inr (160, 14)),
    Sum.inr (Sum.inr (96, 15)),
    Sum.inr (Sum.inr (308, 16)),
    Sum.inr (Sum.inr (308, 17)),
    Sum.inr (Sum.inr (319, 18)),
    Sum.inr (Sum.inr (308, 19)),
    Sum.inr (Sum.inr (234, 20)),
    Sum.inr (Sum.inr (160, 21)),
    Sum.inr (Sum.inr (96, 22)),
    Sum.inr (Sum.inr (33, 23))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock077Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨19712 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock077InputMaskData : ℕ :=
  sixthHex% [
    "d33320e53b20fe3b20883320eff320f1f320d6f32088f320f79b20dd9b20",
    "e29320889320cbab20c9a320caab2088a320c4b320ccb320c0b32088b320",
    "b84320984b20a84b20c84320c5d2cff3d2cfe8dacf9edacff91acfe71acf",
    "c01acf9e1acfe172cfcb72cff47acf9e7acfdd4acfdf4acfdc4acf9e4acf",
    "d252cfda5acfd65acf9e52cfaeaacf8ea2cfbeaacfdea2cf9532cea332ce",
    "b83acece3acea9faceb7face90facecefaceb192ce9b92cea49acece9ace",
    "8da2ce8fa2ce8ca2cecea2ce82b2ce8abace86baceceb2cefe42cede4ace",
    "ee42ce8e4acebf0acd890acd9202cde402cd83c2cd9dc2cdbac2cde4c2cd",
    "9ba2cdb1a2cd8eaacde4aacda792cda592cda692cde492cda88acda082cd",
    "ac82cde48acdd47acdf472cdc47acda472cdafeacc99eacc82e2ccf4e2cc",
    "9322cc8d22ccaa22ccf422cc8b42cca142cc9e4accf44accb77accb57acc",
    "b67accf47accb86accb062ccbc62ccf46accc492cce49accd492ccb49acc",
    "9562cba362cbb86acbce6acba9a2cbb7a2cb90a2cbcea2cbb1c2cb9bc2cb",
    "a4cacbcecacb8dfacb8ffacb8cfacbcefacb82e2cb8aeacb86eacbcee2cb",
    "fe12cbde1acbee12cb8e1acb8582cab382caa88acade8acab942caa742ca",
    "8042cade42caa122ca8b22cab42acade2aca9d12ca9f12ca9c12cade12ca",
    "9202ca9a0aca960acade02caeefacacef2cafefaca9ef2caafbac999bac9",
    "82b2c9f4b2c9937ac98d7ac9aa7ac9f47ac98b12c9a112c99e1ac9f41ac9",
    "b722c9b522c9b622c9f422c9b83ac9b032c9bc32c9f43ac9c4c2c9e4cac9",
    "d4c2c9b4cac9ff5ac8c95ac8d252c8a452c8c39ac8dd9ac8fa9ac8a49ac8",
    "dbf2c8f1f2c8cefac8a4fac8e7cac8e5cac8e6cac8a4cac8e8dac8e0d2c8",
    "ecd2c8a4dac8942ac8b422c8842ac8e422c8a3a2c795a2c78eaac7f8aac7",
    "9f62c78162c7a662c7f862c7870ac7ad0ac79202c7f802c7bb32c7b932c7",
    "ba32c7f832c7b42ac7bc22c7b022c7f82ac7c8dac7e8d2c7d8dac7b8d2c7",
    "b342c68542c69e4ac6e84ac68f82c69182c6b682c6e882c697eac6bdeac6",
    "82e2c6e8e2c6abdac6a9dac6aadac6e8dac6"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock077InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock077InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock077OutputMaskData : ℕ :=
  sixthHex% [
    "b828b1ee2980e3b2a0c0b39aae64f48564ff9764f4c964f4fc8180c012a0",
    "8980b1c0139ac0b18081239ad72aa0e3b8b1b02cffb824ff812cf4fc24ff",
    "f0cb9a85c2a0a35180a358b1d88e30ffcf01831421d1551bbf827594827e",
    "868275d88275ed6701d1f421986630d1f51ba0170190c51bb78c21f25e30",
    "d08a7ea9c27e90ca759c827ee12d1b942421c3f701c3fe30b91c2b9e5d1a",
    "e2863ab0c700de106ef51065e7106eb9106e8cf51ab0663af9f42bb06700",
    "b0c51a801700a75e3ae28c2bb11865c85065f1586efd1065f1ff0084f63a",
    "d3251ad32c2bdccf08fb8e39875519d51423bbc34d90c34682c34ddcc34d",
    "986639a4f519ed6708a4f423a45639948423b3cd19f61f08d4cb46ad8346",
    "948b4d98c346942c23e12519b6f639b6ff08c85d18ef1c2993c709c18633",
    "af515d84515696515dc8515d8cf429b06709f9f518b06633c18429f15633",
    "d61f0993cd18c05956b9115680195d8c5156f1fe3384f709d32429d32d18",
    "11ebf136aac04a71e01830da07a7b42ca7bf3ea7b460a7b42402c01891e0",
    "5103f11890da6972c059a0da7ee9e03b3bf119efbf60a7bf59afb455e7bf",
    "5908da2c01e07bd2c07bdbf10579e12238d05ee3f00ca2ca1335a43835af",
    "2a35a47435a43090d00c03f04591e10c02ca0ca0d03c72ca1b3bf05ee9e1",
    "0d7daf7435af4d3da44175af3cdaca49d3f01e00d01e09e160aac247ebf3",
    "3b30d36971e976e6875de68c4fe68711e6872403f31890d35102c21891e9",
    "1833f328e1e90fa8d34a7ac268ae8c11e68c28ee8724a68c5909e92c00d3",
    "7bd3f37bdac20138d92679e85aa2c808e3f217749c3c74972e749c70749c",
    "4591e87902c83090d97903f208e1e83833f21f7ac85aa8d9093c97707497",
    "497c9c45349749dbf23cd2c86b01e86b08d9b15d13961c22eac702b88638",
    "a711568c115d9e1156c01156f5f422c9670280f513c96638b88422885638",
    "af1f02eacd13c8195db1515d88595684115d88fe38fdf702aa2422aa2d13",
    "a5cf03828e32fe5512ac1428b3834698834d8a8346d48346e16632ddf512",
    "946703ddf428dd5632ed8428cacd128f1f03"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock077OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock077OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock077InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock077InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock077InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock077OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e185f7e196175d8617df85f85f",
    "7df7df7e185f7e17e16df8e37e185f8617df86186185f85f7e185f6df8e3",
    "8617df7e17e18618617e185f85f85f96175d7e185f7df8617df7df85f85f",
    "7df85f6e18e37df7e17e18617e186186185f7df7e16e18e37e17df86185f",
    "7e18618617e18617e195f75d7df7e185f7df85f7df86185f7df7e16e18e3",
    "85f86186185f7e18617df85f7e17e16df8e385f7e18617df8618617e17e1",
    "85f7e196175d7df86185f85f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock077OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock077OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block077_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock077Input a) =
      generatedSixthXiShortBlock077InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock077Output a) =
      generatedSixthXiShortBlock077OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock077Input a) =
      generatedSixthXiShortBlock077InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock077Output a) =
      generatedSixthXiShortBlock077OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block077_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock077InputMask a) =
      generatedSixthXiShortBlock077OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock077InputMask a)) *
      generatedSixthXiShortBlock077InputNumerator a =
        generatedSixthXiShortBlock077OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block077_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock077Input a
    let y := generatedSixthXiShortBlock077Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block077_cache a
  have hs := generatedSixth_xi_short_block077_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block077_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock077Input a
    let y := generatedSixthXiShortBlock077Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block077_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block077_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock077Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block077_certificate a).1
    (generatedSixth_xi_short_block077_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
