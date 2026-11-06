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
def generatedSixthXiShortBlock086Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (508, 13)),
    Sum.inr (Sum.inr (381, 14)),
    Sum.inr (Sum.inr (311, 12)),
    Sum.inr (Sum.inr (445, 15)),
    Sum.inr (Sum.inr (311, 10)),
    Sum.inr (Sum.inr (508, 8)),
    Sum.inr (Sum.inr (381, 9)),
    Sum.inr (Sum.inr (445, 11)),
    Sum.inr (Sum.inr (233, 16)),
    Sum.inr (Sum.inr (233, 17)),
    Sum.inr (Sum.inr (226, 18)),
    Sum.inr (Sum.inr (233, 19)),
    Sum.inr (Sum.inr (311, 3)),
    Sum.inr (Sum.inr (381, 2)),
    Sum.inr (Sum.inr (445, 1)),
    Sum.inr (Sum.inr (508, 0)),
    Sum.inr (Sum.inr (509, 13)),
    Sum.inr (Sum.inr (444, 15)),
    Sum.inr (Sum.inr (380, 14)),
    Sum.inr (Sum.inr (310, 12)),
    Sum.inr (Sum.inr (227, 4)),
    Sum.inr (Sum.inr (232, 5)),
    Sum.inr (Sum.inr (227, 6)),
    Sum.inr (Sum.inr (227, 7)),
    Sum.inr (Sum.inr (509, 23)),
    Sum.inr (Sum.inr (380, 21)),
    Sum.inr (Sum.inr (310, 20)),
    Sum.inr (Sum.inr (444, 22)),
    Sum.inr (Sum.inr (310, 3)),
    Sum.inr (Sum.inr (509, 0)),
    Sum.inr (Sum.inr (380, 2)),
    Sum.inr (Sum.inr (444, 1)),
    Sum.inr (Sum.inr (232, 16)),
    Sum.inr (Sum.inr (232, 17)),
    Sum.inr (Sum.inr (227, 18)),
    Sum.inr (Sum.inr (232, 19)),
    Sum.inr (Sum.inr (310, 10)),
    Sum.inr (Sum.inr (380, 9)),
    Sum.inr (Sum.inr (444, 11)),
    Sum.inr (Sum.inr (509, 8)),
    Sum.inr (Sum.inl (188, 1)),
    Sum.inr (Sum.inl (187, 4)),
    Sum.inr (Sum.inl (143, 63)),
    Sum.inr (Sum.inl (166, 58)),
    Sum.inr (Sum.inl (31, 9)),
    Sum.inr (Sum.inl (11, 15)),
    Sum.inr (Sum.inl (31, 12)),
    Sum.inr (Sum.inl (31, 0)),
    Sum.inr (Sum.inl (188, 4)),
    Sum.inr (Sum.inl (143, 58)),
    Sum.inr (Sum.inl (166, 63)),
    Sum.inr (Sum.inl (187, 1)),
    Sum.inr (Sum.inl (166, 1)),
    Sum.inr (Sum.inl (188, 58)),
    Sum.inr (Sum.inl (143, 4)),
    Sum.inr (Sum.inl (187, 63)),
    Sum.inr (Sum.inl (11, 16)),
    Sum.inr (Sum.inl (11, 32)),
    Sum.inr (Sum.inl (31, 5)),
    Sum.inr (Sum.inl (11, 63)),
    Sum.inr (Sum.inl (166, 4)),
    Sum.inr (Sum.inl (143, 1)),
    Sum.inr (Sum.inl (187, 58)),
    Sum.inr (Sum.inl (188, 63)),
    Sum.inr (Sum.inl (212, 52)),
    Sum.inr (Sum.inl (206, 49)),
    Sum.inr (Sum.inl (149, 53)),
    Sum.inr (Sum.inl (172, 48)),
    Sum.inr (Sum.inl (37, 57)),
    Sum.inr (Sum.inl (17, 63)),
    Sum.inr (Sum.inl (37, 60)),
    Sum.inr (Sum.inl (37, 48)),
    Sum.inr (Sum.inl (212, 49)),
    Sum.inr (Sum.inl (149, 48)),
    Sum.inr (Sum.inl (172, 53)),
    Sum.inr (Sum.inl (206, 52)),
    Sum.inr (Sum.inl (172, 57)),
    Sum.inr (Sum.inl (212, 61)),
    Sum.inr (Sum.inl (149, 60)),
    Sum.inr (Sum.inl (206, 56)),
    Sum.inr (Sum.inl (17, 53)),
    Sum.inr (Sum.inl (17, 54)),
    Sum.inr (Sum.inl (37, 53)),
    Sum.inr (Sum.inl (17, 60)),
    Sum.inr (Sum.inl (172, 60)),
    Sum.inr (Sum.inl (149, 57)),
    Sum.inr (Sum.inl (206, 61)),
    Sum.inr (Sum.inl (212, 56)),
    Sum.inr (Sum.inl (214, 43)),
    Sum.inr (Sum.inl (208, 58)),
    Sum.inr (Sum.inl (151, 21)),
    Sum.inr (Sum.inl (174, 1)),
    Sum.inr (Sum.inl (39, 38)),
    Sum.inr (Sum.inl (19, 6)),
    Sum.inr (Sum.inl (39, 54)),
    Sum.inr (Sum.inl (39, 9)),
    Sum.inr (Sum.inl (214, 52)),
    Sum.inr (Sum.inl (151, 10)),
    Sum.inr (Sum.inl (174, 30)),
    Sum.inr (Sum.inl (208, 37)),
    Sum.inr (Sum.inl (174, 46)),
    Sum.inr (Sum.inl (214, 4)),
    Sum.inr (Sum.inl (151, 58)),
    Sum.inr (Sum.inl (208, 21)),
    Sum.inr (Sum.inl (19, 25)),
    Sum.inr (Sum.inl (19, 41)),
    Sum.inr (Sum.inl (39, 25)),
    Sum.inr (Sum.inl (19, 54)),
    Sum.inr (Sum.inl (174, 49)),
    Sum.inr (Sum.inl (151, 37)),
    Sum.inr (Sum.inl (208, 10)),
    Sum.inr (Sum.inl (214, 27)),
    Sum.inr (Sum.inl (211, 37)),
    Sum.inr (Sum.inl (205, 44)),
    Sum.inr (Sum.inl (148, 27)),
    Sum.inr (Sum.inl (171, 18)),
    Sum.inr (Sum.inl (36, 57)),
    Sum.inr (Sum.inl (16, 12)),
    Sum.inr (Sum.inl (36, 60)),
    Sum.inr (Sum.inl (36, 48)),
    Sum.inr (Sum.inl (211, 58)),
    Sum.inr (Sum.inl (148, 4)),
    Sum.inr (Sum.inl (171, 13)),
    Sum.inr (Sum.inl (205, 51)),
    Sum.inr (Sum.inl (171, 51)),
    Sum.inr (Sum.inl (211, 4)),
    Sum.inr (Sum.inl (148, 58)),
    Sum.inr (Sum.inl (205, 13)),
    Sum.inr (Sum.inl (16, 19)),
    Sum.inr (Sum.inl (16, 35)),
    Sum.inr (Sum.inl (36, 53)),
    Sum.inr (Sum.inl (16, 60)),
    Sum.inr (Sum.inl (171, 44)),
    Sum.inr (Sum.inl (148, 37)),
    Sum.inr (Sum.inl (205, 18)),
    Sum.inr (Sum.inl (211, 27)),
    Sum.inr (Sum.inr (502, 13)),
    Sum.inr (Sum.inr (439, 15)),
    Sum.inr (Sum.inr (375, 14)),
    Sum.inr (Sum.inr (317, 12)),
    Sum.inr (Sum.inr (232, 4)),
    Sum.inr (Sum.inr (227, 5)),
    Sum.inr (Sum.inr (232, 6)),
    Sum.inr (Sum.inr (232, 7)),
    Sum.inr (Sum.inr (502, 23)),
    Sum.inr (Sum.inr (375, 21)),
    Sum.inr (Sum.inr (317, 20)),
    Sum.inr (Sum.inr (439, 22)),
    Sum.inr (Sum.inr (317, 3)),
    Sum.inr (Sum.inr (502, 0)),
    Sum.inr (Sum.inr (375, 2)),
    Sum.inr (Sum.inr (439, 1)),
    Sum.inr (Sum.inr (227, 16)),
    Sum.inr (Sum.inr (227, 17)),
    Sum.inr (Sum.inr (232, 18)),
    Sum.inr (Sum.inr (227, 19)),
    Sum.inr (Sum.inr (317, 10)),
    Sum.inr (Sum.inr (375, 9)),
    Sum.inr (Sum.inr (439, 11)),
    Sum.inr (Sum.inr (502, 8)),
    Sum.inr (Sum.inr (503, 23)),
    Sum.inr (Sum.inr (438, 22)),
    Sum.inr (Sum.inr (374, 21)),
    Sum.inr (Sum.inr (316, 20)),
    Sum.inr (Sum.inr (233, 4)),
    Sum.inr (Sum.inr (226, 5)),
    Sum.inr (Sum.inr (233, 6)),
    Sum.inr (Sum.inr (233, 7)),
    Sum.inr (Sum.inr (503, 13)),
    Sum.inr (Sum.inr (374, 14)),
    Sum.inr (Sum.inr (316, 12)),
    Sum.inr (Sum.inr (438, 15)),
    Sum.inr (Sum.inr (316, 10)),
    Sum.inr (Sum.inr (503, 8)),
    Sum.inr (Sum.inr (374, 9)),
    Sum.inr (Sum.inr (438, 11)),
    Sum.inr (Sum.inr (226, 16)),
    Sum.inr (Sum.inr (226, 17)),
    Sum.inr (Sum.inr (233, 18)),
    Sum.inr (Sum.inr (226, 19)),
    Sum.inr (Sum.inr (316, 3)),
    Sum.inr (Sum.inr (374, 2)),
    Sum.inr (Sum.inr (438, 1)),
    Sum.inr (Sum.inr (503, 0)),
    Sum.inr (Sum.inr (511, 0)),
    Sum.inr (Sum.inr (446, 1)),
    Sum.inr (Sum.inr (382, 2)),
    Sum.inr (Sum.inr (308, 3)),
    Sum.inr (Sum.inr (225, 4)),
    Sum.inr (Sum.inr (234, 5)),
    Sum.inr (Sum.inr (225, 6)),
    Sum.inr (Sum.inr (225, 7)),
    Sum.inr (Sum.inr (511, 8)),
    Sum.inr (Sum.inr (382, 9)),
    Sum.inr (Sum.inr (308, 10)),
    Sum.inr (Sum.inr (446, 11)),
    Sum.inr (Sum.inr (308, 12)),
    Sum.inr (Sum.inr (511, 13)),
    Sum.inr (Sum.inr (382, 14)),
    Sum.inr (Sum.inr (446, 15)),
    Sum.inr (Sum.inr (234, 16)),
    Sum.inr (Sum.inr (234, 17)),
    Sum.inr (Sum.inr (225, 18)),
    Sum.inr (Sum.inr (234, 19)),
    Sum.inr (Sum.inr (308, 20)),
    Sum.inr (Sum.inr (382, 21)),
    Sum.inr (Sum.inr (446, 22)),
    Sum.inr (Sum.inr (511, 23)),
    Sum.inr (Sum.inr (501, 8)),
    Sum.inr (Sum.inr (436, 11)),
    Sum.inr (Sum.inr (372, 9)),
    Sum.inr (Sum.inr (318, 10)),
    Sum.inr (Sum.inr (235, 4)),
    Sum.inr (Sum.inr (224, 5)),
    Sum.inr (Sum.inr (235, 6)),
    Sum.inr (Sum.inr (235, 7)),
    Sum.inr (Sum.inr (501, 0)),
    Sum.inr (Sum.inr (372, 2)),
    Sum.inr (Sum.inr (318, 3)),
    Sum.inr (Sum.inr (436, 1)),
    Sum.inr (Sum.inr (318, 20)),
    Sum.inr (Sum.inr (501, 23)),
    Sum.inr (Sum.inr (372, 21)),
    Sum.inr (Sum.inr (436, 22)),
    Sum.inr (Sum.inr (224, 16)),
    Sum.inr (Sum.inr (224, 17)),
    Sum.inr (Sum.inr (235, 18)),
    Sum.inr (Sum.inr (224, 19)),
    Sum.inr (Sum.inr (318, 12)),
    Sum.inr (Sum.inr (372, 14)),
    Sum.inr (Sum.inr (436, 15)),
    Sum.inr (Sum.inr (501, 13)),
    Sum.inr (Sum.inr (31, 23)),
    Sum.inr (Sum.inr (94, 11)),
    Sum.inr (Sum.inr (158, 14)),
    Sum.inr (Sum.inr (212, 3)),
    Sum.inr (Sum.inr (257, 7)),
    Sum.inr (Sum.inr (266, 5)),
    Sum.inr (Sum.inr (257, 18)),
    Sum.inr (Sum.inr (257, 4)),
    Sum.inr (Sum.inr (31, 13)),
    Sum.inr (Sum.inr (158, 21)),
    Sum.inr (Sum.inr (212, 10)),
    Sum.inr (Sum.inr (94, 1)),
    Sum.inr (Sum.inr (212, 12)),
    Sum.inr (Sum.inr (31, 8)),
    Sum.inr (Sum.inr (158, 2)),
    Sum.inr (Sum.inr (94, 22)),
    Sum.inr (Sum.inr (266, 16)),
    Sum.inr (Sum.inr (266, 17)),
    Sum.inr (Sum.inr (257, 6)),
    Sum.inr (Sum.inr (266, 19)),
    Sum.inr (Sum.inr (212, 20)),
    Sum.inr (Sum.inr (158, 9)),
    Sum.inr (Sum.inr (94, 15)),
    Sum.inr (Sum.inr (31, 0))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock086Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨22016 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock086InputMaskData : ℕ :=
  sixthHex% [
    "ab04909d0490860490f00c9097cc9089c490aecc90f0cc908fa490a5ac90",
    "9aac90f0ac90b39c90b19c90b29490f09c90bc8c90b48490b88c90f08c90",
    "c07c90e07c90d07c90b0749093944fa59c4fbe9c4fc89c4faf5c4fb1544f",
    "965c4fc85c4fb73c4f9d3c4fa2344fc83c4f8b044f89044f8a044fc80c4f",
    "84144f8c144f801c4fc8144ff8e44fd8e44fe8e44f88ec4fd3944ee59c4e",
    "fe9c4e889c4eef5c4ef1544ed65c4e885c4ef73c4edd3c4ee2344e883c4e",
    "cb0c4ec90c4eca0c4e88044ec4144ecc144ec01c4e88144eb8ec4e98ec4e",
    "a8ec4ec8e44ef99c4dcf944dd4944da2944dc5544ddb5c4dfc544da2544d",
    "dd3c4df73c4dc8344da23c4de10c4de30c4de00c4da2044dee1c4de61c4d",
    "ea144da21c4d92e44db2e44d82e44de2ec4df9944ccf9c4cd49c4ca29c4c",
    "c55c4cdb544cfc5c4ca25c4cdd344cf7344cc83c4ca2344ce10c4ce30c4c",
    "e00c4ca2044cee144ce6144cea1c4ca2144c92e44cb2e44c82e44ce2ec4c",
    "ea9c4bdc944bc7944bb1944bd65c4bc8544bef5c4bb15c4bce344be4344b",
    "db3c4bb1344bf20c4bf00c4bf30c4bb1044bfd1c4bf51c4bf9144bb11c4b",
    "81e44ba1e44b91e44bf1ec4bea944adc9c4ac79c4ab19c4ad6544ac85c4a",
    "ef544ab1544ace3c4ae43c4adb344ab13c4af20c4af00c4af30c4ab1044a",
    "fd144af5144af91c4ab1144a81e44aa1e44a91e44af1ec4ac09c49f69449",
    "ed94499b9449fc5c49e25449c55c499b5c49e43c49ce3c49f134499b3c49",
    "d80c49da0c49d90c499b0449d71c49df1c49d314499b1c49abec498bec49",
    "bbec49dbe449809c48b69448ad9448db9448bc5c48a25448855c48db5c48",
    "a43c488e3c48b13448db3c489804489a0448990448db0c48971c489f1c48",
    "931448db1c48ebe448cbe448fbe4489bec48c89447fe9c47e59c47939c47",
    "f45447ea5c47cd5447935447ec3447c63447f93c47933447d00c47d20c47",
    "d10c47930447df1c47d71c47db1447931c47a3e44783e447b3e447d3ec47",
    "c89c46fe9446e59446939446f45c46ea5446cd5c46935c46ec3c46c63c46",
    "f93446933c46d00c46d20c46d10c46930446"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock086InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock086InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock086OutputMaskData : ℕ :=
  sixthHex% [
    "b8486f9f095e92927eb19344df442a850421e6442ab8442a8da15ec0727e",
    "f8a06fb13344c0d15ef00344a60a7e92986fc10c21b84421f00c2a8d0421",
    "81eb4485a27ea3315ea3386fb6dfd5e0dee4ed45c4bf04fed1d3908b939b",
    "e8d390b6d390f276e4cee5c48777d5bfa4febf06e48fd4fea89dc49c0fd5",
    "bedb9bb6d39bfe9b90f2d39bfe3cfefa75c4dce6e4dcefd5c077df9676ee",
    "9bedcec9acf4a77b9afd3b919e7b9ac07b9a84deeeb84dcef1dfdfc90cf4",
    "b8eeee883cf4af75ce9be7dfc87391c07b9188339a847b91f9d4f4fd9dce",
    "db0eeedb07df860fd7d00ee6dd95c68fd4fce10392bb4399d80392860392",
    "b3e6e68f75c6c6e7d7fe34fc8fd6e6bf04fc984dc6acdfd78e0b99860399",
    "ce4b92c20399bfacfcbbe5c69d76e69d7fd7f4e7d6a2e6e7af7dc7fd3cfd",
    "93eb93c9ab98aaeb93f4eb93c10ee7fd9dc7b40fd68cdcfd8c7ee7bcacfd",
    "9be5c7af77d6fce398f4eb98bca393b0eb98bc04fdb84dc79edee79ed7d6",
    "0a1c405c1d7151865103c76b1c500546100e2550057b50054eb571722651",
    "3bb44003676b03c57133176b145e5120cc4002180e0a100e4258054e100e",
    "33bf6b37f651116571116c4078f4412ef570236e50712f6a6eb80434f80f",
    "57b80409b8043c5d7000ce50495c41718f6a006d7030bf6a17f650236441",
    "70f00f78f80f30b0043cf80f30176a345e5012cd7012c4413e8c49688d78",
    "65165837576228c00c72800711c00c4fc00c0b657837f6587e644946b762",
    "37557807876220ce58145c493688073e800776c80c7a8007766f62722658",
    "54b57854bc494824431e257213be5241ff685e680604280d676806396806",
    "7dcd72415e5208cc43301f6830bd72006f6827265213b44340200d48280d",
    "0060060c280d71876875ce52535d72535443c1e7dd97e6ec9a7dccc83cf6",
    "d7ab988deb93eeab98b0ab98f40eecc89dcc810fddb9dcf6b97eec89acf6",
    "aee5cc9a77ddb8a393b0ab93f8e398f4ab938904f68d4dccabdeecabd7dd",
    "b30fdce50eede895cdbad4f7a54399ff03929c4399c2439986e6edba75cd",
    "f3e7dccb34f7bad6ed8a04f7ad4dcd99dfdc"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock086OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock086OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock086InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock086InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock086InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock086OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f6df8e37df8617e17e186186185f7e18617df96175d7df8617df7df",
    "85f7e17e17e17df7df6df8e385f7e17e185f7e185f85f7e18617df96175d",
    "8617df7df7df85f7e185f85f86186196175d85f7e185f7e185f7e185f7e1",
    "85f7df95f75d7df7e17df85f7df7e17df85f85f86195f75d7e17df85f861",
    "7df7e17df7e17e18616e18e37df7e18617e186185f7df85f7e17df6e18e3",
    "7e17df7e17df86185f7df7e186186196175d85f7e185f7e185f7e185f7e1",
    "8617df96175d8617df7df7df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock086OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock086OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block086_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock086Input a) =
      generatedSixthXiShortBlock086InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock086Output a) =
      generatedSixthXiShortBlock086OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock086Input a) =
      generatedSixthXiShortBlock086InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock086Output a) =
      generatedSixthXiShortBlock086OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block086_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock086InputMask a) =
      generatedSixthXiShortBlock086OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock086InputMask a)) *
      generatedSixthXiShortBlock086InputNumerator a =
        generatedSixthXiShortBlock086OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block086_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock086Input a
    let y := generatedSixthXiShortBlock086Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block086_cache a
  have hs := generatedSixth_xi_short_block086_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block086_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock086Input a
    let y := generatedSixthXiShortBlock086Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block086_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block086_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock086Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block086_certificate a).1
    (generatedSixth_xi_short_block086_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
