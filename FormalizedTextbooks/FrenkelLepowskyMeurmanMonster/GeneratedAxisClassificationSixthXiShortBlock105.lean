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
def generatedSixthXiShortBlock105Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (84, 13)),
    Sum.inr (Sum.inr (21, 1)),
    Sum.inr (Sum.inr (213, 21)),
    Sum.inr (Sum.inr (159, 10)),
    Sum.inr (Sum.inr (330, 7)),
    Sum.inr (Sum.inr (321, 5)),
    Sum.inr (Sum.inr (330, 18)),
    Sum.inr (Sum.inr (330, 4)),
    Sum.inr (Sum.inr (84, 23)),
    Sum.inr (Sum.inr (213, 14)),
    Sum.inr (Sum.inr (159, 3)),
    Sum.inr (Sum.inr (21, 11)),
    Sum.inr (Sum.inr (159, 20)),
    Sum.inr (Sum.inr (84, 0)),
    Sum.inr (Sum.inr (213, 9)),
    Sum.inr (Sum.inr (21, 15)),
    Sum.inr (Sum.inr (321, 16)),
    Sum.inr (Sum.inr (321, 17)),
    Sum.inr (Sum.inr (330, 6)),
    Sum.inr (Sum.inr (321, 19)),
    Sum.inr (Sum.inr (159, 12)),
    Sum.inr (Sum.inr (213, 2)),
    Sum.inr (Sum.inr (21, 22)),
    Sum.inr (Sum.inr (84, 8)),
    Sum.inr (Sum.inr (151, 8)),
    Sum.inr (Sum.inr (214, 22)),
    Sum.inr (Sum.inr (22, 2)),
    Sum.inr (Sum.inr (92, 12)),
    Sum.inr (Sum.inr (393, 7)),
    Sum.inr (Sum.inr (386, 5)),
    Sum.inr (Sum.inr (393, 18)),
    Sum.inr (Sum.inr (393, 4)),
    Sum.inr (Sum.inr (151, 0)),
    Sum.inr (Sum.inr (22, 9)),
    Sum.inr (Sum.inr (92, 20)),
    Sum.inr (Sum.inr (214, 15)),
    Sum.inr (Sum.inr (92, 3)),
    Sum.inr (Sum.inr (151, 23)),
    Sum.inr (Sum.inr (22, 14)),
    Sum.inr (Sum.inr (214, 11)),
    Sum.inr (Sum.inr (386, 16)),
    Sum.inr (Sum.inr (386, 17)),
    Sum.inr (Sum.inr (393, 6)),
    Sum.inr (Sum.inr (386, 19)),
    Sum.inr (Sum.inr (92, 10)),
    Sum.inr (Sum.inr (22, 21)),
    Sum.inr (Sum.inr (214, 1)),
    Sum.inr (Sum.inr (151, 13)),
    Sum.inr (Sum.inr (23, 0)),
    Sum.inr (Sum.inr (86, 15)),
    Sum.inr (Sum.inr (150, 9)),
    Sum.inr (Sum.inr (220, 20)),
    Sum.inr (Sum.inr (265, 7)),
    Sum.inr (Sum.inr (258, 5)),
    Sum.inr (Sum.inr (265, 18)),
    Sum.inr (Sum.inr (265, 4)),
    Sum.inr (Sum.inr (23, 8)),
    Sum.inr (Sum.inr (150, 2)),
    Sum.inr (Sum.inr (220, 12)),
    Sum.inr (Sum.inr (86, 22)),
    Sum.inr (Sum.inr (220, 10)),
    Sum.inr (Sum.inr (23, 13)),
    Sum.inr (Sum.inr (150, 21)),
    Sum.inr (Sum.inr (86, 1)),
    Sum.inr (Sum.inr (258, 16)),
    Sum.inr (Sum.inr (258, 17)),
    Sum.inr (Sum.inr (265, 6)),
    Sum.inr (Sum.inr (258, 19)),
    Sum.inr (Sum.inr (220, 3)),
    Sum.inr (Sum.inr (150, 14)),
    Sum.inr (Sum.inr (86, 11)),
    Sum.inr (Sum.inr (23, 23)),
    Sum.inr (Sum.inl (53, 18)),
    Sum.inr (Sum.inl (52, 34)),
    Sum.inr (Sum.inl (46, 2)),
    Sum.inr (Sum.inl (48, 0)),
    Sum.inr (Sum.inl (21, 1)),
    Sum.inr (Sum.inl (1, 49)),
    Sum.inr (Sum.inl (21, 9)),
    Sum.inr (Sum.inl (21, 11)),
    Sum.inr (Sum.inl (53, 3)),
    Sum.inr (Sum.inl (46, 19)),
    Sum.inr (Sum.inl (48, 16)),
    Sum.inr (Sum.inl (52, 2)),
    Sum.inr (Sum.inl (48, 4)),
    Sum.inr (Sum.inl (53, 19)),
    Sum.inr (Sum.inl (46, 18)),
    Sum.inr (Sum.inl (52, 3)),
    Sum.inr (Sum.inl (1, 17)),
    Sum.inr (Sum.inl (1, 33)),
    Sum.inr (Sum.inl (21, 3)),
    Sum.inr (Sum.inl (1, 1)),
    Sum.inr (Sum.inl (48, 20)),
    Sum.inr (Sum.inl (46, 3)),
    Sum.inr (Sum.inl (52, 35)),
    Sum.inr (Sum.inl (53, 2)),
    Sum.inr (Sum.inl (119, 1)),
    Sum.inr (Sum.inl (118, 63)),
    Sum.inr (Sum.inl (112, 18)),
    Sum.inr (Sum.inl (114, 45)),
    Sum.inr (Sum.inl (25, 63)),
    Sum.inr (Sum.inl (5, 15)),
    Sum.inr (Sum.inl (25, 55)),
    Sum.inr (Sum.inl (25, 53)),
    Sum.inr (Sum.inl (119, 16)),
    Sum.inr (Sum.inl (112, 0)),
    Sum.inr (Sum.inl (114, 61)),
    Sum.inr (Sum.inl (118, 32)),
    Sum.inr (Sum.inl (114, 63)),
    Sum.inr (Sum.inl (119, 46)),
    Sum.inr (Sum.inl (112, 47)),
    Sum.inr (Sum.inl (118, 8)),
    Sum.inr (Sum.inl (5, 47)),
    Sum.inr (Sum.inl (5, 31)),
    Sum.inr (Sum.inl (25, 61)),
    Sum.inr (Sum.inl (5, 63)),
    Sum.inr (Sum.inl (114, 47)),
    Sum.inr (Sum.inl (112, 61)),
    Sum.inr (Sum.inl (118, 23)),
    Sum.inr (Sum.inl (119, 63)),
    Sum.inr (Sum.inl (213, 33)),
    Sum.inr (Sum.inl (207, 17)),
    Sum.inr (Sum.inl (150, 12)),
    Sum.inr (Sum.inl (173, 50)),
    Sum.inr (Sum.inl (38, 16)),
    Sum.inr (Sum.inl (18, 52)),
    Sum.inr (Sum.inl (38, 24)),
    Sum.inr (Sum.inl (38, 26)),
    Sum.inr (Sum.inl (213, 62)),
    Sum.inr (Sum.inl (150, 44)),
    Sum.inr (Sum.inl (173, 16)),
    Sum.inr (Sum.inl (207, 48)),
    Sum.inr (Sum.inl (173, 18)),
    Sum.inr (Sum.inl (213, 0)),
    Sum.inr (Sum.inl (150, 4)),
    Sum.inr (Sum.inl (207, 47)),
    Sum.inr (Sum.inl (18, 20)),
    Sum.inr (Sum.inl (18, 36)),
    Sum.inr (Sum.inl (38, 18)),
    Sum.inr (Sum.inl (18, 4)),
    Sum.inr (Sum.inl (173, 48)),
    Sum.inr (Sum.inl (150, 36)),
    Sum.inr (Sum.inl (207, 14)),
    Sum.inr (Sum.inl (213, 31)),
    Sum.inr (Sum.inl (158, 51)),
    Sum.inr (Sum.inl (157, 49)),
    Sum.inr (Sum.inl (140, 46)),
    Sum.inr (Sum.inl (153, 17)),
    Sum.inr (Sum.inl (28, 46)),
    Sum.inr (Sum.inl (8, 10)),
    Sum.inr (Sum.inl (28, 38)),
    Sum.inr (Sum.inl (28, 36)),
    Sum.inr (Sum.inl (158, 28)),
    Sum.inr (Sum.inl (140, 1)),
    Sum.inr (Sum.inl (153, 51)),
    Sum.inr (Sum.inl (157, 19)),
    Sum.inr (Sum.inl (153, 19)),
    Sum.inr (Sum.inl (158, 8)),
    Sum.inr (Sum.inl (140, 60)),
    Sum.inr (Sum.inl (157, 46)),
    Sum.inr (Sum.inl (8, 42)),
    Sum.inr (Sum.inl (8, 26)),
    Sum.inr (Sum.inl (28, 44)),
    Sum.inr (Sum.inl (8, 58)),
    Sum.inr (Sum.inl (153, 49)),
    Sum.inr (Sum.inl (140, 19)),
    Sum.inr (Sum.inl (157, 12)),
    Sum.inr (Sum.inl (158, 39)),
    Sum.inr (Sum.inr (28, 0)),
    Sum.inr (Sum.inr (93, 15)),
    Sum.inr (Sum.inr (157, 9)),
    Sum.inr (Sum.inr (215, 20)),
    Sum.inr (Sum.inr (258, 7)),
    Sum.inr (Sum.inr (265, 5)),
    Sum.inr (Sum.inr (258, 18)),
    Sum.inr (Sum.inr (258, 4)),
    Sum.inr (Sum.inr (28, 8)),
    Sum.inr (Sum.inr (157, 2)),
    Sum.inr (Sum.inr (215, 12)),
    Sum.inr (Sum.inr (93, 22)),
    Sum.inr (Sum.inr (215, 10)),
    Sum.inr (Sum.inr (28, 13)),
    Sum.inr (Sum.inr (157, 21)),
    Sum.inr (Sum.inr (93, 1)),
    Sum.inr (Sum.inr (265, 16)),
    Sum.inr (Sum.inr (265, 17)),
    Sum.inr (Sum.inr (258, 6)),
    Sum.inr (Sum.inr (265, 19)),
    Sum.inr (Sum.inr (215, 3)),
    Sum.inr (Sum.inr (157, 14)),
    Sum.inr (Sum.inr (93, 11)),
    Sum.inr (Sum.inr (28, 23)),
    Sum.inr (Sum.inr (156, 8)),
    Sum.inr (Sum.inr (221, 22)),
    Sum.inr (Sum.inr (29, 2)),
    Sum.inr (Sum.inr (87, 12)),
    Sum.inr (Sum.inr (386, 7)),
    Sum.inr (Sum.inr (393, 5)),
    Sum.inr (Sum.inr (386, 18)),
    Sum.inr (Sum.inr (386, 4)),
    Sum.inr (Sum.inr (156, 0)),
    Sum.inr (Sum.inr (29, 9)),
    Sum.inr (Sum.inr (87, 20)),
    Sum.inr (Sum.inr (221, 15)),
    Sum.inr (Sum.inr (87, 3)),
    Sum.inr (Sum.inr (156, 23)),
    Sum.inr (Sum.inr (29, 14)),
    Sum.inr (Sum.inr (221, 11)),
    Sum.inr (Sum.inr (393, 16)),
    Sum.inr (Sum.inr (393, 17)),
    Sum.inr (Sum.inr (386, 6)),
    Sum.inr (Sum.inr (393, 19)),
    Sum.inr (Sum.inr (87, 10)),
    Sum.inr (Sum.inr (29, 21)),
    Sum.inr (Sum.inr (221, 1)),
    Sum.inr (Sum.inr (156, 13)),
    Sum.inr (Sum.inr (95, 13)),
    Sum.inr (Sum.inr (30, 1)),
    Sum.inr (Sum.inr (222, 21)),
    Sum.inr (Sum.inr (148, 10)),
    Sum.inr (Sum.inr (321, 7)),
    Sum.inr (Sum.inr (330, 5)),
    Sum.inr (Sum.inr (321, 18)),
    Sum.inr (Sum.inr (321, 4)),
    Sum.inr (Sum.inr (95, 23)),
    Sum.inr (Sum.inr (222, 14)),
    Sum.inr (Sum.inr (148, 3)),
    Sum.inr (Sum.inr (30, 11)),
    Sum.inr (Sum.inr (148, 20)),
    Sum.inr (Sum.inr (95, 0)),
    Sum.inr (Sum.inr (222, 9)),
    Sum.inr (Sum.inr (30, 15)),
    Sum.inr (Sum.inr (330, 16)),
    Sum.inr (Sum.inr (330, 17)),
    Sum.inr (Sum.inr (321, 6)),
    Sum.inr (Sum.inr (330, 19)),
    Sum.inr (Sum.inr (148, 12)),
    Sum.inr (Sum.inr (222, 2)),
    Sum.inr (Sum.inr (30, 22)),
    Sum.inr (Sum.inr (95, 8)),
    Sum.inr (Sum.inr (212, 23)),
    Sum.inr (Sum.inr (149, 11)),
    Sum.inr (Sum.inr (85, 14)),
    Sum.inr (Sum.inr (31, 3)),
    Sum.inr (Sum.inr (458, 7)),
    Sum.inr (Sum.inr (449, 5)),
    Sum.inr (Sum.inr (458, 18)),
    Sum.inr (Sum.inr (458, 4)),
    Sum.inr (Sum.inr (212, 13)),
    Sum.inr (Sum.inr (85, 21)),
    Sum.inr (Sum.inr (31, 10)),
    Sum.inr (Sum.inr (149, 1)),
    Sum.inr (Sum.inr (31, 12)),
    Sum.inr (Sum.inr (212, 8)),
    Sum.inr (Sum.inr (85, 2)),
    Sum.inr (Sum.inr (149, 22))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock105Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨26880 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock105InputMaskData : ℕ :=
  sixthHex% [
    "9cd7bbb6dfbb89d7bbe3d7bba0efbba2e7bba1e7bbe3e7bbafffbba7f7bb",
    "abffbbe3ffbbd307bbf30fbbc30fbba30fbb8b77babd7fbaa67fbad07fba",
    "b7b7baa9bfba8eb7bad0b7baafdfba85d7babadfbad0dfba93efba91e7ba",
    "92e7bad0e7ba9cf7ba94ffba98f7bad0f7bae007bac00fbaf00fba900fba",
    "9d77b9ab7fb9b07fb9c67fb9a1b7b9bfbfb998b7b9c6b7b9b9d7b993dfb9",
    "acd7b9c6d7b985e7b987efb984efb9c6efb98af7b982ffb98ef7b9c6f7b9",
    "f607b9d60fb9e60fb9860fb9ee77b8d87fb8c37fb8b57fb8d2b7b8ccbfb8",
    "ebb7b8b5b7b8cad7b8e0dfb8dfd7b8b5d7b8f6efb8f4e7b8f7e7b8b5e7b8",
    "f9f7b8f1ffb8fdf7b8b5f7b8850fb8a507b89507b8f507b89a77b7ac7fb7",
    "b77fb7c17fb7a6b7b7b8bfb79fb7b7c1b7b7bed7b794dfb7abd7b7c1d7b7",
    "82efb780e7b783e7b7c1e7b78dffb785f7b789ffb7c1ffb7f107b7d10fb7",
    "e10fb7810fb7a97fb69f77b68477b6f277b695bfb68bb7b6acbfb6f2bfb6",
    "8ddfb6a7d7b698dfb6f2dfb6b1efb6b3e7b6b0e7b6f2e7b6bef7b6b6ffb6",
    "baf7b6f2f7b6c207b6e20fb6d20fb6b20fb6bf7fb58977b59277b5e477b5",
    "83bfb59db7b5babfb5e4bfb59bd7b5b1dfb58ed7b5e4d7b5a7e7b5a5efb5",
    "a6efb5e4efb5a8f7b5a0ffb5acf7b5e4f7b5d407b5f40fb5c40fb5a40fb5",
    "cc7fb4fa77b4e177b49777b4f0bfb4eeb7b4c9bfb497bfb4e8d7b4c2dfb4",
    "fdd7b497d7b4d4efb4d6e7b4d5e7b497e7b4dbf7b4d3ffb4dff7b497f7b4",
    "a70fb48707b4b707b4d707b4937fb3a577b3be77b3c877b3afb7b3b1bfb3",
    "96b7b3c8b7b3b7dfb39dd7b3a2dfb3c8dfb38be7b389efb38aefb3c8efb3",
    "84f7b38cffb380f7b3c8f7b3f807b3d80fb3e80fb3880fb3e07fb2d677b2",
    "cd77b2bb77b2dcb7b2c2bfb2e5b7b2bbb7b2c4dfb2eed7b2d1dfb2bbdfb2",
    "f8efb2fae7b2f9e7b2bbe7b2f7f7b2ffffb2f3f7b2bbf7b28b0fb2ab07b2",
    "9b07b2fb07b2f67fb1c077b1db77b1ad77b1cab7b1d4bfb1f3b7b1adb7b1",
    "d2d7b1f8dfb1c7d7b1add7b1eee7b1ecefb1efefb1adefb1e1f7b1e9ffb1",
    "e5f7b1adf7b19d0fb1bd07b18d07b1ed07b1"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock105InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock105InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock105OutputMaskData : ℕ :=
  sixthHex% [
    "b54275f89155b10344f8906ff83275b9a06f9ee955db3b44f9ef0a80a70a",
    "c8ef01b5e70ac8486fbd41559bd275ea9b4482d95fd4d86ed9434e8b0274",
    "94951aced511ad951af3951ac6706e8ba34ec2315f8ba274fa406ebbd274",
    "9c9b4ed9495f8add11f39511bbdd1ac6d511ca3a74bf334e99a06ee8e95f",
    "aa7a7cfc7b4df1e06da3a157bc3639e67632853639db36399f934dd2406d",
    "9bd27cd24157a3a34de23157c5786d80aa7ca27e32db3632937e39ee7632",
    "e2995797906db1034dc04a7cdd086c8b095d86927dd4d347cb4429910422",
    "f24429ac4429e8e15da5327deca06ca53347a5915de40347c34a7d86986c",
    "d50c22ac4422e40c29990422e4ab4791a27db7315dc6786c3a10d96c11e8",
    "618ac833cbf22c5c9c761c97155c9c4b5c9c0ff9e8422ac80bb8d9422bf2",
    "4289e8031bf22452c86180d94354973a1c9772549c0f5c9772f3f207fac8",
    "2169e85020d94922c21f23f312b8d340f9e95f6e87052e8c666e87386e87",
    "7ccbf33118d3788ac23119e940fbf30169e92620d363f2c230668c492e8c",
    "0166877c6e8c7081e90588d3231bf35252c26181e13780d03a1bf0685aca",
    "77cda42d8daf4ecda410cda42528d068fbf02169e168faca1918d0588aca",
    "7fc3f03a11e118c5af618daf29c5a454cdaf5822ca2d2bf00bb8d07af1e1",
    "16f3f140f2c04d69e01f28da00bfb45affbf39bfb467bfb4525ac01f89e0",
    "561bf11f88da1f2ac05eb8da79f1e03c23f16fb7bf16ffbf5eb7b423bfbf",
    "5e10da2b19e00d8ac07cc3f1d540678341568eda76dc9b4cb24c22e80c29",
    "8b4c22d54c22e0a956ad7a76e4e867ad7b4cadd956ec4b4ccb02768ed067",
    "ac0429d54c299d0422e00c29ece34c99ea76bf7956ce3067a23277f43346",
    "f9a866abe95cc53e329f7e39fc3e32a23e3297db46da0866939a77da095c",
    "abeb46ea795ccd306688e277db7639a23e39ea7632977e39ead15c9fd866",
    "b94b46c802778a9154dc9065d10b45834a7fed9d11b7dd1ad49d118a9d11",
    "ce386583eb45ca795483ea7ff20865b39a7f94d345d10154f3d51a8a9d1a",
    "c2d511bfdd1ac2727fb77b4591e865e0a154"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock105OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock105OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock105InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock105InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock105InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock105OutputNumeratorData : ℕ :=
  sixthHex% [
    "8617df85f85f7df7df7e185f85f85f96175d85f7e17df8617df7df7e17e1",
    "85f7e196175d7df86185f85f7df7df85f7e17e17e16df8e385f7e18617df",
    "8618617e17e186185f95f75d7e17df7df7e185f7df8617e18617e195f75d",
    "7df7e185f7df85f7df86185f7df7e16e18e37e17df86185f7e18618617e1",
    "7df85f6e18e37df7e17e18617e186186185f85f85f96175d7e185f7df861",
    "7df7df85f85f7e185f6df8e38617df7e17e18618617e185f7e17e16df8e3",
    "7e185f8617df86186185f85f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock105OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock105OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block105_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock105Input a) =
      generatedSixthXiShortBlock105InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock105Output a) =
      generatedSixthXiShortBlock105OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock105Input a) =
      generatedSixthXiShortBlock105InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock105Output a) =
      generatedSixthXiShortBlock105OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block105_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock105InputMask a) =
      generatedSixthXiShortBlock105OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock105InputMask a)) *
      generatedSixthXiShortBlock105InputNumerator a =
        generatedSixthXiShortBlock105OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block105_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock105Input a
    let y := generatedSixthXiShortBlock105Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block105_cache a
  have hs := generatedSixth_xi_short_block105_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block105_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock105Input a
    let y := generatedSixthXiShortBlock105Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block105_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block105_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock105Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block105_certificate a).1
    (generatedSixth_xi_short_block105_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
