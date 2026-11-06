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
def generatedSixthXiShortBlock076Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (2, 29)),
    Sum.inr (Sum.inl (2, 45)),
    Sum.inr (Sum.inl (22, 49)),
    Sum.inr (Sum.inl (2, 13)),
    Sum.inr (Sum.inl (66, 60)),
    Sum.inr (Sum.inl (64, 51)),
    Sum.inr (Sum.inl (70, 12)),
    Sum.inr (Sum.inl (71, 51)),
    Sum.inr (Sum.inr (281, 8)),
    Sum.inr (Sum.inr (344, 1)),
    Sum.inr (Sum.inr (408, 14)),
    Sum.inr (Sum.inr (466, 20)),
    Sum.inr (Sum.inr (7, 6)),
    Sum.inr (Sum.inr (12, 5)),
    Sum.inr (Sum.inr (7, 4)),
    Sum.inr (Sum.inr (7, 18)),
    Sum.inr (Sum.inr (281, 0)),
    Sum.inr (Sum.inr (408, 21)),
    Sum.inr (Sum.inr (466, 12)),
    Sum.inr (Sum.inr (344, 11)),
    Sum.inr (Sum.inr (466, 10)),
    Sum.inr (Sum.inr (281, 23)),
    Sum.inr (Sum.inr (408, 2)),
    Sum.inr (Sum.inr (344, 15)),
    Sum.inr (Sum.inr (12, 16)),
    Sum.inr (Sum.inr (12, 17)),
    Sum.inr (Sum.inr (7, 7)),
    Sum.inr (Sum.inr (12, 19)),
    Sum.inr (Sum.inr (466, 3)),
    Sum.inr (Sum.inr (408, 9)),
    Sum.inr (Sum.inr (344, 22)),
    Sum.inr (Sum.inr (281, 13)),
    Sum.inr (Sum.inr (345, 0)),
    Sum.inr (Sum.inr (280, 11)),
    Sum.inr (Sum.inr (472, 21)),
    Sum.inr (Sum.inr (402, 12)),
    Sum.inr (Sum.inr (71, 6)),
    Sum.inr (Sum.inr (76, 5)),
    Sum.inr (Sum.inr (71, 4)),
    Sum.inr (Sum.inr (71, 18)),
    Sum.inr (Sum.inr (345, 8)),
    Sum.inr (Sum.inr (472, 14)),
    Sum.inr (Sum.inr (402, 20)),
    Sum.inr (Sum.inr (280, 1)),
    Sum.inr (Sum.inr (402, 3)),
    Sum.inr (Sum.inr (345, 13)),
    Sum.inr (Sum.inr (472, 9)),
    Sum.inr (Sum.inr (280, 22)),
    Sum.inr (Sum.inr (76, 16)),
    Sum.inr (Sum.inr (76, 17)),
    Sum.inr (Sum.inr (71, 7)),
    Sum.inr (Sum.inr (76, 19)),
    Sum.inr (Sum.inr (402, 10)),
    Sum.inr (Sum.inr (472, 2)),
    Sum.inr (Sum.inr (280, 15)),
    Sum.inr (Sum.inr (345, 23)),
    Sum.inr (Sum.inr (475, 23)),
    Sum.inr (Sum.inr (410, 15)),
    Sum.inr (Sum.inr (346, 2)),
    Sum.inr (Sum.inr (272, 10)),
    Sum.inr (Sum.inr (197, 6)),
    Sum.inr (Sum.inr (206, 5)),
    Sum.inr (Sum.inr (197, 4)),
    Sum.inr (Sum.inr (197, 18)),
    Sum.inr (Sum.inr (475, 13)),
    Sum.inr (Sum.inr (346, 9)),
    Sum.inr (Sum.inr (272, 3)),
    Sum.inr (Sum.inr (410, 22)),
    Sum.inr (Sum.inr (272, 20)),
    Sum.inr (Sum.inr (475, 8)),
    Sum.inr (Sum.inr (346, 14)),
    Sum.inr (Sum.inr (410, 1)),
    Sum.inr (Sum.inr (206, 16)),
    Sum.inr (Sum.inr (206, 17)),
    Sum.inr (Sum.inr (197, 7)),
    Sum.inr (Sum.inr (206, 19)),
    Sum.inr (Sum.inr (272, 12)),
    Sum.inr (Sum.inr (346, 21)),
    Sum.inr (Sum.inr (410, 11)),
    Sum.inr (Sum.inr (475, 0)),
    Sum.inr (Sum.inr (400, 13)),
    Sum.inr (Sum.inr (465, 22)),
    Sum.inr (Sum.inr (273, 9)),
    Sum.inr (Sum.inr (347, 3)),
    Sum.inr (Sum.inr (142, 6)),
    Sum.inr (Sum.inr (133, 5)),
    Sum.inr (Sum.inr (142, 4)),
    Sum.inr (Sum.inr (142, 18)),
    Sum.inr (Sum.inr (400, 23)),
    Sum.inr (Sum.inr (273, 2)),
    Sum.inr (Sum.inr (347, 10)),
    Sum.inr (Sum.inr (465, 15)),
    Sum.inr (Sum.inr (347, 12)),
    Sum.inr (Sum.inr (400, 0)),
    Sum.inr (Sum.inr (273, 21)),
    Sum.inr (Sum.inr (465, 11)),
    Sum.inr (Sum.inr (133, 16)),
    Sum.inr (Sum.inr (133, 17)),
    Sum.inr (Sum.inr (142, 7)),
    Sum.inr (Sum.inr (133, 19)),
    Sum.inr (Sum.inr (347, 20)),
    Sum.inr (Sum.inr (273, 14)),
    Sum.inr (Sum.inr (465, 1)),
    Sum.inr (Sum.inr (400, 8)),
    Sum.inr (Sum.inl (53, 54)),
    Sum.inr (Sum.inl (52, 7)),
    Sum.inr (Sum.inl (46, 38)),
    Sum.inr (Sum.inl (48, 9)),
    Sum.inr (Sum.inl (21, 21)),
    Sum.inr (Sum.inl (1, 5)),
    Sum.inr (Sum.inl (21, 29)),
    Sum.inr (Sum.inl (21, 31)),
    Sum.inr (Sum.inl (53, 39)),
    Sum.inr (Sum.inl (46, 55)),
    Sum.inr (Sum.inl (48, 25)),
    Sum.inr (Sum.inl (52, 39)),
    Sum.inr (Sum.inl (48, 13)),
    Sum.inr (Sum.inl (53, 55)),
    Sum.inr (Sum.inl (46, 54)),
    Sum.inr (Sum.inl (52, 38)),
    Sum.inr (Sum.inl (1, 37)),
    Sum.inr (Sum.inl (1, 21)),
    Sum.inr (Sum.inl (21, 23)),
    Sum.inr (Sum.inl (1, 53)),
    Sum.inr (Sum.inl (48, 29)),
    Sum.inr (Sum.inl (46, 39)),
    Sum.inr (Sum.inl (52, 6)),
    Sum.inr (Sum.inl (53, 38)),
    Sum.inr (Sum.inl (119, 7)),
    Sum.inr (Sum.inl (118, 41)),
    Sum.inr (Sum.inl (112, 23)),
    Sum.inr (Sum.inl (114, 40)),
    Sum.inr (Sum.inl (25, 58)),
    Sum.inr (Sum.inl (5, 62)),
    Sum.inr (Sum.inl (25, 50)),
    Sum.inr (Sum.inl (25, 48)),
    Sum.inr (Sum.inl (119, 22)),
    Sum.inr (Sum.inl (112, 5)),
    Sum.inr (Sum.inl (114, 56)),
    Sum.inr (Sum.inl (118, 54)),
    Sum.inr (Sum.inl (114, 58)),
    Sum.inr (Sum.inl (119, 40)),
    Sum.inr (Sum.inl (112, 42)),
    Sum.inr (Sum.inl (118, 30)),
    Sum.inr (Sum.inl (5, 30)),
    Sum.inr (Sum.inl (5, 46)),
    Sum.inr (Sum.inl (25, 56)),
    Sum.inr (Sum.inl (5, 14)),
    Sum.inr (Sum.inl (114, 42)),
    Sum.inr (Sum.inl (112, 56)),
    Sum.inr (Sum.inl (118, 1)),
    Sum.inr (Sum.inl (119, 57)),
    Sum.inr (Sum.inl (213, 37)),
    Sum.inr (Sum.inl (207, 11)),
    Sum.inr (Sum.inl (150, 50)),
    Sum.inr (Sum.inl (173, 9)),
    Sum.inr (Sum.inl (38, 43)),
    Sum.inr (Sum.inl (18, 59)),
    Sum.inr (Sum.inl (38, 35)),
    Sum.inr (Sum.inl (38, 33)),
    Sum.inr (Sum.inl (213, 58)),
    Sum.inr (Sum.inl (150, 18)),
    Sum.inr (Sum.inl (173, 43)),
    Sum.inr (Sum.inl (207, 42)),
    Sum.inr (Sum.inl (173, 41)),
    Sum.inr (Sum.inl (213, 4)),
    Sum.inr (Sum.inl (150, 58)),
    Sum.inr (Sum.inl (207, 53)),
    Sum.inr (Sum.inl (18, 27)),
    Sum.inr (Sum.inl (18, 43)),
    Sum.inr (Sum.inl (38, 41)),
    Sum.inr (Sum.inl (18, 11)),
    Sum.inr (Sum.inl (173, 11)),
    Sum.inr (Sum.inl (150, 26)),
    Sum.inr (Sum.inl (207, 20)),
    Sum.inr (Sum.inl (213, 27)),
    Sum.inr (Sum.inl (158, 18)),
    Sum.inr (Sum.inl (157, 40)),
    Sum.inr (Sum.inl (140, 10)),
    Sum.inr (Sum.inl (153, 42)),
    Sum.inr (Sum.inl (28, 10)),
    Sum.inr (Sum.inl (8, 50)),
    Sum.inr (Sum.inl (28, 2)),
    Sum.inr (Sum.inl (28, 0)),
    Sum.inr (Sum.inl (158, 61)),
    Sum.inr (Sum.inl (140, 37)),
    Sum.inr (Sum.inl (153, 8)),
    Sum.inr (Sum.inl (157, 10)),
    Sum.inr (Sum.inl (153, 40)),
    Sum.inr (Sum.inl (158, 41)),
    Sum.inr (Sum.inl (140, 24)),
    Sum.inr (Sum.inl (157, 55)),
    Sum.inr (Sum.inl (8, 18)),
    Sum.inr (Sum.inl (8, 34)),
    Sum.inr (Sum.inl (28, 8)),
    Sum.inr (Sum.inl (8, 2)),
    Sum.inr (Sum.inl (153, 10)),
    Sum.inr (Sum.inl (140, 55)),
    Sum.inr (Sum.inl (157, 21)),
    Sum.inr (Sum.inl (158, 6)),
    Sum.inr (Sum.inr (395, 23)),
    Sum.inr (Sum.inr (458, 11)),
    Sum.inr (Sum.inr (266, 14)),
    Sum.inr (Sum.inr (320, 3)),
    Sum.inr (Sum.inr (149, 7)),
    Sum.inr (Sum.inr (158, 5)),
    Sum.inr (Sum.inr (149, 18)),
    Sum.inr (Sum.inr (149, 4)),
    Sum.inr (Sum.inr (395, 13)),
    Sum.inr (Sum.inr (266, 21)),
    Sum.inr (Sum.inr (320, 10)),
    Sum.inr (Sum.inr (458, 1)),
    Sum.inr (Sum.inr (320, 12)),
    Sum.inr (Sum.inr (395, 8)),
    Sum.inr (Sum.inr (266, 2)),
    Sum.inr (Sum.inr (458, 22)),
    Sum.inr (Sum.inr (158, 16)),
    Sum.inr (Sum.inr (158, 17)),
    Sum.inr (Sum.inr (149, 6)),
    Sum.inr (Sum.inr (158, 19)),
    Sum.inr (Sum.inr (320, 20)),
    Sum.inr (Sum.inr (266, 9)),
    Sum.inr (Sum.inr (458, 15)),
    Sum.inr (Sum.inr (395, 0)),
    Sum.inr (Sum.inr (256, 13)),
    Sum.inr (Sum.inr (321, 1)),
    Sum.inr (Sum.inr (385, 21)),
    Sum.inr (Sum.inr (459, 10)),
    Sum.inr (Sum.inr (30, 7)),
    Sum.inr (Sum.inr (21, 5)),
    Sum.inr (Sum.inr (30, 18)),
    Sum.inr (Sum.inr (30, 4)),
    Sum.inr (Sum.inr (256, 23)),
    Sum.inr (Sum.inr (385, 14)),
    Sum.inr (Sum.inr (459, 3)),
    Sum.inr (Sum.inr (321, 11)),
    Sum.inr (Sum.inr (459, 20)),
    Sum.inr (Sum.inr (256, 0)),
    Sum.inr (Sum.inr (385, 9)),
    Sum.inr (Sum.inr (321, 15)),
    Sum.inr (Sum.inr (21, 16)),
    Sum.inr (Sum.inr (21, 17)),
    Sum.inr (Sum.inr (30, 6)),
    Sum.inr (Sum.inr (21, 19)),
    Sum.inr (Sum.inr (459, 12)),
    Sum.inr (Sum.inr (385, 2)),
    Sum.inr (Sum.inr (321, 22)),
    Sum.inr (Sum.inr (256, 8)),
    Sum.inr (Sum.inr (451, 8)),
    Sum.inr (Sum.inr (386, 22)),
    Sum.inr (Sum.inr (322, 2)),
    Sum.inr (Sum.inr (264, 12)),
    Sum.inr (Sum.inr (221, 7)),
    Sum.inr (Sum.inr (214, 5)),
    Sum.inr (Sum.inr (221, 18)),
    Sum.inr (Sum.inr (221, 4))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock076Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨19456 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock076InputMaskData : ℕ :=
  sixthHex% [
    "a4cac6acc2c6a0c2c6e8cac6d832c6f83ac6c832c6a83ac6997ac5af7ac5",
    "b472c5c272c5a5bac5bbbac59cbac5c2bac5bddac597dac5a8d2c5c2d2c5",
    "81eac583eac580eac5c2eac58ef2c586fac58afac5c2f2c5f20ac5d202c5",
    "e20ac58202c5c99ac4ff9ac4e492c49292c4f55ac4eb5ac4cc5ac4925ac4",
    "ed3ac4c73ac4f832c49232c4d102c4d302c4d002c49202c4de12c4d61ac4",
    "da1ac49212c4a2e2c482eac4b2e2c4d2eac4b312c38512c39e1ac3e81ac3",
    "8fdac391dac3b6dac3e8dac397bac3bdbac382b2c3e8b2c3ab82c3a982c3",
    "aa82c3e882c3a49ac3ac92c3a092c3e89ac3d862c3f86ac3c862c3a86ac3",
    "e3f2c2d5f2c2cefac2b8fac2df3ac2c13ac2e63ac2b83ac2c75ac2ed5ac2",
    "d252c2b852c2fb6ac2f96ac2fa6ac2b86ac2f47ac2fc72c2f072c2b87ac2",
    "888ac2a882c2988ac2f882c2c9cac1ffcac1e4c2c192c2c1f502c1eb02c1",
    "cc02c19202c1ed6ac1c76ac1f862c19262c1d15ac1d35ac1d05ac1925ac1",
    "de42c1d64ac1da4ac19242c1a2b2c182bac1b2b2c1d2bac1d92ac0ef2ac0",
    "f422c08222c0e5e2c0fbe2c0dce2c082e2c0fd8ac0d78ac0e882c08282c0",
    "c1b2c0c3b2c0c0b2c082b2c0cea2c0c6aac0caaac082a2c0b25ac09252c0",
    "a25ac0c252c0da4aafec4aaff74aaf814aafe68aaff88aafdf8aaf818aaf",
    "fee2afd4eaafebe2af81eaafc2d2afc0daafc3d2af81daafcdcaafc5c2af",
    "c9caaf81c2afb13aaf9132afa13aafc132af8ba2aebda2aea6a2aed0a2ae",
    "b762aea962ae8e62aed062aeaf0aae8502aeba0aaed002ae9332ae913aae",
    "9232aed03aae9c22ae942aae9822aed02aaee0daaec0d2aef0daae90d2ae",
    "9f92ada992adb292adc492ada352adbd52ad9a52adc452adbb32ad913aad",
    "ae32adc43aad870aad8502ad860aadc402ad8812ad801aad8c12adc41aad",
    "f4eaadd4e2ade4eaad84e2ad8e7aacb87aaca37aacd57aacb2baacacbaac",
    "8bbaacd5baacaadaac80d2acbfdaacd5d2ac96eaac94e2ac97eaacd5e2ac",
    "99faac91f2ac9dfaacd5f2ace50aacc502acf50aac9502ac8afaabbcfaab",
    "a7faabd1faabb632aba832ab8f32abd132ab"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock076InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock076InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock076OutputMaskData : ℕ :=
  sixthHex% [
    "dc8b4da5c34d9ccb4690834ded2c28982512cff632cfff03c01c20e75d11",
    "9b8631c9c70bd65065fd506eef5065b15065f5f511c9663180f420c9670b",
    "c9c511f9170bde5e319b8c20b9586ec0106ef91865f5506e88ff0bfdf631",
    "aa2511aa2c20a18e3b86cf0afa142aa85510b7c27e9cc2758ec27ed0c27e",
    "94670aa8f42ae1663ba8f510d9170ae9c510ce8c2a8b5e3bd8ca75a18275",
    "988a7e94c275982d10ed242abaf70abafe3b0d38d92a79e856a2c804e3f2",
    "6a349c41349753349c0d349c4991e87502c83c90d97503f204e1e83433f2",
    "137ac856a8d9747c970d3497343c9c38749745dbf230d2c86701e86708d9",
    "6caac24bebf33730d36571e90ba68720a68c32a6876ca6872803f31490d3",
    "5d02c21491e91433f324e1e903a8d3467ac215ee8c6ca68c55ae8759e68c",
    "5509e92000d377d3f377dac20979e12e38d052e3f000a2ca6e75a44575af",
    "5775a40975a43c90d00003f04991e10002ca00a0d03072ca173bf052e9e1",
    "703daf0975af307da43c35af30daca45d3f01200d01209e11debf13aaac0",
    "4671e01430da7ae7b451e7bf43e7b41de7b42802c01491e05d03f11490da",
    "6572c055a0da72e9e0373bf164afbf1de7bf24efb428a7bf5508da2001e0",
    "77d2c077dbf1bfee5098af61953441c7757ba9a21582a21e90a215cea215",
    "fb4761b69441ff0650c7d57bc7776186e57bd0ec41e47e50b7ea1ecea21e",
    "86ea158aa21ef70d7b820441d5d761d5de50b8a76b9fe65a927d7ac03c40",
    "aeeb2e85eb2597eb2ec9eb2efc0e5ab1dd7af84f6bc09c40b17e5af0ec40",
    "a6e57a92776bb0a325c9eb2581a32e8deb25810440f40d7aa3de5aa3d76b",
    "837d79a43c48a9a768fbe65295313cbe3137ac313cf2313cb69448fb4768",
    "b2d5798a0652fbe448ba7652ec7f68d8ed798b7937f23137ba793cb63137",
    "bade52cfd768980448980d79f13449d67578dbee5889af62e7780ccc7807",
    "de780c80780cc4dd78890e58c09c49f84f62f8ed78b97f62ef7658dbe449",
    "f93007807807c8300cc47807b9d762ccde589b0d789b0449768b9151caa0",
    "5c51800e10ba1187d43a87df2887d47687d4"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock076OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock076OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock076InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock076InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock076InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock076OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df85f7e185f85f96175d85f7e17df8617df7df7e17e17e185f6df8e3",
    "7df8617e17e186186185f7e186185f95f75d7e17df7df7e185f7df8617e1",
    "7df85f6e18e386185f7e18617e18617df7e186185f95f75d85f8617df7e1",
    "85f7df7df85f8617e195f75d86185f85f7df85f7df7df7e185f86195f75d",
    "7e17df85f8617df7e17df7e185f7df95f75d7df7e17df85f7df7e17df85f",
    "7e17df6e18e37e17df7e17df86185f7df7e17e18616e18e37df7e18617e1",
    "86185f7df85f7df7df6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock076OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock076OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block076_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock076Input a) =
      generatedSixthXiShortBlock076InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock076Output a) =
      generatedSixthXiShortBlock076OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock076Input a) =
      generatedSixthXiShortBlock076InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock076Output a) =
      generatedSixthXiShortBlock076OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block076_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock076InputMask a) =
      generatedSixthXiShortBlock076OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock076InputMask a)) *
      generatedSixthXiShortBlock076InputNumerator a =
        generatedSixthXiShortBlock076OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block076_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock076Input a
    let y := generatedSixthXiShortBlock076Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block076_cache a
  have hs := generatedSixth_xi_short_block076_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block076_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock076Input a
    let y := generatedSixthXiShortBlock076Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block076_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block076_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock076Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block076_certificate a).1
    (generatedSixth_xi_short_block076_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
