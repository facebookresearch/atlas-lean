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
def generatedSixthXiShortBlock104Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (316, 13)),
    Sum.inr (Sum.inr (445, 14)),
    Sum.inr (Sum.inr (503, 12)),
    Sum.inr (Sum.inr (381, 15)),
    Sum.inr (Sum.inr (503, 10)),
    Sum.inr (Sum.inr (316, 8)),
    Sum.inr (Sum.inr (445, 9)),
    Sum.inr (Sum.inr (381, 11)),
    Sum.inr (Sum.inr (41, 16)),
    Sum.inr (Sum.inr (41, 17)),
    Sum.inr (Sum.inr (34, 18)),
    Sum.inr (Sum.inr (41, 19)),
    Sum.inr (Sum.inr (503, 3)),
    Sum.inr (Sum.inr (445, 2)),
    Sum.inr (Sum.inr (381, 1)),
    Sum.inr (Sum.inr (316, 0)),
    Sum.inr (Sum.inr (317, 13)),
    Sum.inr (Sum.inr (380, 15)),
    Sum.inr (Sum.inr (444, 14)),
    Sum.inr (Sum.inr (502, 12)),
    Sum.inr (Sum.inr (35, 4)),
    Sum.inr (Sum.inr (40, 5)),
    Sum.inr (Sum.inr (35, 6)),
    Sum.inr (Sum.inr (35, 7)),
    Sum.inr (Sum.inr (317, 23)),
    Sum.inr (Sum.inr (444, 21)),
    Sum.inr (Sum.inr (502, 20)),
    Sum.inr (Sum.inr (380, 22)),
    Sum.inr (Sum.inr (502, 3)),
    Sum.inr (Sum.inr (317, 0)),
    Sum.inr (Sum.inr (444, 2)),
    Sum.inr (Sum.inr (380, 1)),
    Sum.inr (Sum.inr (40, 16)),
    Sum.inr (Sum.inr (40, 17)),
    Sum.inr (Sum.inr (35, 18)),
    Sum.inr (Sum.inr (40, 19)),
    Sum.inr (Sum.inr (502, 10)),
    Sum.inr (Sum.inr (444, 9)),
    Sum.inr (Sum.inr (380, 11)),
    Sum.inr (Sum.inr (317, 8)),
    Sum.inr (Sum.inl (188, 49)),
    Sum.inr (Sum.inl (187, 30)),
    Sum.inr (Sum.inl (143, 37)),
    Sum.inr (Sum.inl (166, 10)),
    Sum.inr (Sum.inl (31, 54)),
    Sum.inr (Sum.inl (11, 3)),
    Sum.inr (Sum.inl (31, 51)),
    Sum.inr (Sum.inl (31, 63)),
    Sum.inr (Sum.inl (188, 52)),
    Sum.inr (Sum.inl (143, 32)),
    Sum.inr (Sum.inl (166, 15)),
    Sum.inr (Sum.inl (187, 27)),
    Sum.inr (Sum.inl (166, 49)),
    Sum.inr (Sum.inl (188, 10)),
    Sum.inr (Sum.inl (143, 30)),
    Sum.inr (Sum.inl (187, 37)),
    Sum.inr (Sum.inl (11, 28)),
    Sum.inr (Sum.inl (11, 44)),
    Sum.inr (Sum.inl (31, 58)),
    Sum.inr (Sum.inl (11, 51)),
    Sum.inr (Sum.inl (166, 52)),
    Sum.inr (Sum.inl (143, 27)),
    Sum.inr (Sum.inl (187, 32)),
    Sum.inr (Sum.inl (188, 15)),
    Sum.inr (Sum.inl (212, 11)),
    Sum.inr (Sum.inl (206, 60)),
    Sum.inr (Sum.inl (149, 56)),
    Sum.inr (Sum.inl (172, 16)),
    Sum.inr (Sum.inl (37, 25)),
    Sum.inr (Sum.inl (17, 31)),
    Sum.inr (Sum.inl (37, 28)),
    Sum.inr (Sum.inl (37, 16)),
    Sum.inr (Sum.inl (212, 14)),
    Sum.inr (Sum.inl (149, 61)),
    Sum.inr (Sum.inl (172, 21)),
    Sum.inr (Sum.inl (206, 57)),
    Sum.inr (Sum.inl (172, 25)),
    Sum.inr (Sum.inl (212, 2)),
    Sum.inr (Sum.inl (149, 49)),
    Sum.inr (Sum.inl (206, 53)),
    Sum.inr (Sum.inl (17, 21)),
    Sum.inr (Sum.inl (17, 22)),
    Sum.inr (Sum.inl (37, 21)),
    Sum.inr (Sum.inl (17, 28)),
    Sum.inr (Sum.inl (172, 28)),
    Sum.inr (Sum.inl (149, 52)),
    Sum.inr (Sum.inl (206, 48)),
    Sum.inr (Sum.inl (212, 7)),
    Sum.inr (Sum.inl (214, 40)),
    Sum.inr (Sum.inl (208, 55)),
    Sum.inr (Sum.inl (151, 24)),
    Sum.inr (Sum.inl (174, 7)),
    Sum.inr (Sum.inl (39, 32)),
    Sum.inr (Sum.inl (19, 0)),
    Sum.inr (Sum.inl (39, 48)),
    Sum.inr (Sum.inl (39, 15)),
    Sum.inr (Sum.inl (214, 55)),
    Sum.inr (Sum.inl (151, 7)),
    Sum.inr (Sum.inl (174, 24)),
    Sum.inr (Sum.inl (208, 40)),
    Sum.inr (Sum.inl (174, 40)),
    Sum.inr (Sum.inl (214, 7)),
    Sum.inr (Sum.inl (151, 55)),
    Sum.inr (Sum.inl (208, 24)),
    Sum.inr (Sum.inl (19, 31)),
    Sum.inr (Sum.inl (19, 47)),
    Sum.inr (Sum.inl (39, 31)),
    Sum.inr (Sum.inl (19, 48)),
    Sum.inr (Sum.inl (174, 55)),
    Sum.inr (Sum.inl (151, 40)),
    Sum.inr (Sum.inl (208, 7)),
    Sum.inr (Sum.inl (214, 24)),
    Sum.inr (Sum.inl (211, 49)),
    Sum.inr (Sum.inl (205, 58)),
    Sum.inr (Sum.inl (148, 21)),
    Sum.inr (Sum.inl (171, 10)),
    Sum.inr (Sum.inl (36, 38)),
    Sum.inr (Sum.inl (16, 6)),
    Sum.inr (Sum.inl (36, 35)),
    Sum.inr (Sum.inl (36, 47)),
    Sum.inr (Sum.inl (211, 46)),
    Sum.inr (Sum.inl (148, 10)),
    Sum.inr (Sum.inl (171, 21)),
    Sum.inr (Sum.inl (205, 37)),
    Sum.inr (Sum.inl (171, 43)),
    Sum.inr (Sum.inl (211, 16)),
    Sum.inr (Sum.inl (148, 52)),
    Sum.inr (Sum.inl (205, 27)),
    Sum.inr (Sum.inl (16, 25)),
    Sum.inr (Sum.inl (16, 41)),
    Sum.inr (Sum.inl (36, 42)),
    Sum.inr (Sum.inl (16, 54)),
    Sum.inr (Sum.inl (171, 52)),
    Sum.inr (Sum.inl (148, 43)),
    Sum.inr (Sum.inl (205, 4)),
    Sum.inr (Sum.inl (211, 15)),
    Sum.inr (Sum.inr (310, 13)),
    Sum.inr (Sum.inr (375, 15)),
    Sum.inr (Sum.inr (439, 14)),
    Sum.inr (Sum.inr (509, 12)),
    Sum.inr (Sum.inr (40, 4)),
    Sum.inr (Sum.inr (35, 5)),
    Sum.inr (Sum.inr (40, 6)),
    Sum.inr (Sum.inr (40, 7)),
    Sum.inr (Sum.inr (310, 23)),
    Sum.inr (Sum.inr (439, 21)),
    Sum.inr (Sum.inr (509, 20)),
    Sum.inr (Sum.inr (375, 22)),
    Sum.inr (Sum.inr (509, 3)),
    Sum.inr (Sum.inr (310, 0)),
    Sum.inr (Sum.inr (439, 2)),
    Sum.inr (Sum.inr (375, 1)),
    Sum.inr (Sum.inr (35, 16)),
    Sum.inr (Sum.inr (35, 17)),
    Sum.inr (Sum.inr (40, 18)),
    Sum.inr (Sum.inr (35, 19)),
    Sum.inr (Sum.inr (509, 10)),
    Sum.inr (Sum.inr (439, 9)),
    Sum.inr (Sum.inr (375, 11)),
    Sum.inr (Sum.inr (310, 8)),
    Sum.inr (Sum.inr (311, 23)),
    Sum.inr (Sum.inr (374, 22)),
    Sum.inr (Sum.inr (438, 21)),
    Sum.inr (Sum.inr (508, 20)),
    Sum.inr (Sum.inr (41, 4)),
    Sum.inr (Sum.inr (34, 5)),
    Sum.inr (Sum.inr (41, 6)),
    Sum.inr (Sum.inr (41, 7)),
    Sum.inr (Sum.inr (311, 13)),
    Sum.inr (Sum.inr (438, 14)),
    Sum.inr (Sum.inr (508, 12)),
    Sum.inr (Sum.inr (374, 15)),
    Sum.inr (Sum.inr (508, 10)),
    Sum.inr (Sum.inr (311, 8)),
    Sum.inr (Sum.inr (438, 9)),
    Sum.inr (Sum.inr (374, 11)),
    Sum.inr (Sum.inr (34, 16)),
    Sum.inr (Sum.inr (34, 17)),
    Sum.inr (Sum.inr (41, 18)),
    Sum.inr (Sum.inr (34, 19)),
    Sum.inr (Sum.inr (508, 3)),
    Sum.inr (Sum.inr (438, 2)),
    Sum.inr (Sum.inr (374, 1)),
    Sum.inr (Sum.inr (311, 0)),
    Sum.inr (Sum.inr (319, 0)),
    Sum.inr (Sum.inr (382, 1)),
    Sum.inr (Sum.inr (446, 2)),
    Sum.inr (Sum.inr (500, 3)),
    Sum.inr (Sum.inr (33, 4)),
    Sum.inr (Sum.inr (42, 5)),
    Sum.inr (Sum.inr (33, 6)),
    Sum.inr (Sum.inr (33, 7)),
    Sum.inr (Sum.inr (319, 8)),
    Sum.inr (Sum.inr (446, 9)),
    Sum.inr (Sum.inr (500, 10)),
    Sum.inr (Sum.inr (382, 11)),
    Sum.inr (Sum.inr (500, 12)),
    Sum.inr (Sum.inr (319, 13)),
    Sum.inr (Sum.inr (446, 14)),
    Sum.inr (Sum.inr (382, 15)),
    Sum.inr (Sum.inr (42, 16)),
    Sum.inr (Sum.inr (42, 17)),
    Sum.inr (Sum.inr (33, 18)),
    Sum.inr (Sum.inr (42, 19)),
    Sum.inr (Sum.inr (500, 20)),
    Sum.inr (Sum.inr (446, 21)),
    Sum.inr (Sum.inr (382, 22)),
    Sum.inr (Sum.inr (319, 23)),
    Sum.inr (Sum.inr (309, 8)),
    Sum.inr (Sum.inr (372, 11)),
    Sum.inr (Sum.inr (436, 9)),
    Sum.inr (Sum.inr (510, 10)),
    Sum.inr (Sum.inr (43, 4)),
    Sum.inr (Sum.inr (32, 5)),
    Sum.inr (Sum.inr (43, 6)),
    Sum.inr (Sum.inr (43, 7)),
    Sum.inr (Sum.inr (309, 0)),
    Sum.inr (Sum.inr (436, 2)),
    Sum.inr (Sum.inr (510, 3)),
    Sum.inr (Sum.inr (372, 1)),
    Sum.inr (Sum.inr (510, 20)),
    Sum.inr (Sum.inr (309, 23)),
    Sum.inr (Sum.inr (436, 21)),
    Sum.inr (Sum.inr (372, 22)),
    Sum.inr (Sum.inr (32, 16)),
    Sum.inr (Sum.inr (32, 17)),
    Sum.inr (Sum.inr (43, 18)),
    Sum.inr (Sum.inr (32, 19)),
    Sum.inr (Sum.inr (510, 12)),
    Sum.inr (Sum.inr (436, 14)),
    Sum.inr (Sum.inr (372, 15)),
    Sum.inr (Sum.inr (309, 13)),
    Sum.inr (Sum.inr (223, 23)),
    Sum.inr (Sum.inr (158, 11)),
    Sum.inr (Sum.inr (94, 14)),
    Sum.inr (Sum.inr (20, 3)),
    Sum.inr (Sum.inr (449, 7)),
    Sum.inr (Sum.inr (458, 5)),
    Sum.inr (Sum.inr (449, 18)),
    Sum.inr (Sum.inr (449, 4)),
    Sum.inr (Sum.inr (223, 13)),
    Sum.inr (Sum.inr (94, 21)),
    Sum.inr (Sum.inr (20, 10)),
    Sum.inr (Sum.inr (158, 1)),
    Sum.inr (Sum.inr (20, 12)),
    Sum.inr (Sum.inr (223, 8)),
    Sum.inr (Sum.inr (94, 2)),
    Sum.inr (Sum.inr (158, 22)),
    Sum.inr (Sum.inr (458, 16)),
    Sum.inr (Sum.inr (458, 17)),
    Sum.inr (Sum.inr (449, 6)),
    Sum.inr (Sum.inr (458, 19)),
    Sum.inr (Sum.inr (20, 20)),
    Sum.inr (Sum.inr (94, 9)),
    Sum.inr (Sum.inr (158, 15)),
    Sum.inr (Sum.inr (223, 0))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock104Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨26624 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock104InputMaskData : ℕ :=
  sixthHex% [
    "c577b0f37fb0e87fb09e7fb0f9bfb0e7b7b0c0bfb09ebfb0e1dfb0cbd7b0",
    "f4dfb09edfb0dde7b0dfefb0dcefb09eefb0d2ffb0daf7b0d6ffb09effb0",
    "ae0fb08e07b0be07b0de07b0ead76fdcd76fc7d76fb1df6fd61f6fc8176f",
    "ef1f6fb11f6fce776fe4776fdb776fb17f6ff24f6ff0476ff34f6fb14f6f",
    "fd576ff5576ff95f6fb1576f81a76fa1af6f91af6ff1af6f9bd76eadd76e",
    "b6d76ec0df6ea71f6eb9176e9e1f6ec01f6ebf776e95776eaa776ec07f6e",
    "83476e814f6e82476ec0476e8c576e84576e885f6ec0576ef0af6ed0a76e",
    "e0a76e80a76e9adf6dacdf6db7df6dc1d76da6176db81f6d9f176dc1176d",
    "be776d94776dab776dc17f6d82476d804f6d83476dc1476d8d5f6d855f6d",
    "89576dc15f6df1a76dd1af6de1af6d81af6dabd76c9dd76c86d76cf0df6c",
    "971f6c89176cae1f6cf01f6c8f7f6ca57f6c9a7f6cf0776cb3476cb14f6c",
    "b2476cf0476cbc576cb4576cb85f6cf0576cc0a76ce0af6cd0af6cb0af6c",
    "a3d76b95d76b8ed76bf8df6b9f176b811f6ba6176bf8176b87776bad776b",
    "92776bf87f6bbb4f6bb9476bba4f6bf84f6bb4576bbc576bb05f6bf8576b",
    "c8af6be8a76bd8a76bb8a76b92df6aa4df6abfdf6ac9d76aae1f6ab0176a",
    "971f6ac91f6ab67f6a9c7f6aa37f6ac9776a8a4f6a88476a8b4f6ac94f6a",
    "855f6a8d5f6a81576ac95f6af9af6ad9a76ae9a76a89a76a93d769a5d769",
    "bed769c8df69af1769b11f69961769c81769b77f699d7f69a27f69c87769",
    "8b4f698947698a4f69c84f698457698c5769805f69c85769f8a769d8af69",
    "e8af6988af69e2d768d4d768cfd768b9df68de1768c01f68e71768b91768",
    "c67f68ec7f68d37f68b97768fa4768f84f68fb4768b94768f55768fd5768",
    "f15f68b9576889af68a9a76899a768f9a7689ad767acd767b7d767c1df67",
    "a61767b81f679f1767c11767be7f67947f67ab7f67c17767824767804f67",
    "834767c147678d5f67855f67895767c15f67f1a767d1af67e1af6781af67",
    "abdf669ddf6686df66f0d766971f66891766ae1f66f01f668f7766a57766",
    "9a7766f07f66b34766b14f66b24766f04766"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock104InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock104InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock104OutputMaskData : ℕ :=
  sixthHex% [
    "f9a34fafa27ea2395ef078649eaf0ac4ef01a7af0af9af0abd0a7ef0d95e",
    "b94b4ff0d864f07a7eb1e86496a15ed3734f80e701f9af01b1e70accef01",
    "c00064b5095e939a7ee2d34fe00cf5c74dc4cad6e4e9d7de8700b0dd40bb",
    "be00b0e000b0d5e5c4e976e4d1a4f5e977de9895c4d907de8f0ee4cadcf5",
    "e808bbe000bba848b0a400bba8efdedde6e4fb75c48a3cf5a7acff80edce",
    "8d76eeae77d4c0a0ba9ae0b1f9a0baa7a0ba9245ceaed6ee9604ffaed7d4",
    "ae75ceefe7d4b9eeeefc3cffafa8b1a7a0b1efe8bae3a0b19e0fd4eb06ee",
    "cd95cebcdcffcadcf7ed9dc6e006e6c307dcadd0b2f790b994d0b2cad0b2",
    "8e75c6b2e6e68a34f7b2e7dcb245c6f3d7dca5dee6e00cf7c2d8b9cad0b9",
    "8298b28ed0b9f37fdc8676e6a0e5c6d1acf7893cf6ae7dc7a3e6e780e7dd",
    "ee30b3b470b8d730b38930b3cd95c7f106e7c9d4f6f107dd80e5c7c177dd",
    "977ee7d2acf68138b88930b8c178b3cd30b8c1dfddb4d6e79245c7e30cf6",
    "0b1c402c5d7121c65102c76b1d500547100e2450057a50053ef571026651",
    "3ab44002676b73857132176b641e5121cc4003180e0b100e4358054f100e",
    "32bf6b47b651612571106c4048fc416fbd7062265041276a5eb00404f00f",
    "67b00439b0047d157041865079544141876a41257000b76a56be50136c41",
    "40f80f48f00f00b8040cf00f001f6a75165053857022cc41258c4902cd78",
    "0f56582c576233c00c6980070ac00c54c00c6125785db6586564495db762",
    "5d15781c87624a8e580f5c492d88072580076dc80c6180076d6f62186658",
    "3ef5784fbc49622c43456d7248f6526bf7687460062e200d4d6006136006",
    "2685721a165222c4431a17686bf5722a67687c6e5239bc436a280d62200d",
    "2a680626200d5b8f682e8652081572795c43bc3cfd9b7dcc96e6ecb5e7d6",
    "aa70b8f030b39370b8cd70b8f895ccc406ecfcd4fdc407d6b5e5ccf477d6",
    "a27eece7acfdc578b3cd70b38538b88970b3f4dfd681d6eca745ccd60cfd",
    "ffdcfcd89dcdd506edf607d7e990b9b3d0b2d090b98e90b9bb75cd87e6ed",
    "bf34fc87e7d78745cdc6d7d790deedd50cfc"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock104OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock104OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock104InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock104InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock104InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock104OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f6df8e37df8617e17e186186185f7e18617df96175d7df8617df7df",
    "85f7e17e17e17df7df6df8e385f7e17e185f7e185f85f7e17df8616df8e3",
    "7df8618618617e185f7e17e17df7df6df8e37e185f7e185f7e185f7e185f",
    "7e18616e18e386185f8617e186185f8617e17e17df6e18e385f8617e17df",
    "86185f86185f7e18616e18e37df7e18617e186185f7df85f7e17df6e18e3",
    "7e17df7e17df86185f7df7e17df7df6df8e37e185f7e185f7e185f7e185f",
    "7df8616df8e37df861861861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock104OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock104OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block104_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock104Input a) =
      generatedSixthXiShortBlock104InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock104Output a) =
      generatedSixthXiShortBlock104OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock104Input a) =
      generatedSixthXiShortBlock104InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock104Output a) =
      generatedSixthXiShortBlock104OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block104_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock104InputMask a) =
      generatedSixthXiShortBlock104OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock104InputMask a)) *
      generatedSixthXiShortBlock104InputNumerator a =
        generatedSixthXiShortBlock104OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block104_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock104Input a
    let y := generatedSixthXiShortBlock104Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block104_cache a
  have hs := generatedSixth_xi_short_block104_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block104_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock104Input a
    let y := generatedSixthXiShortBlock104Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block104_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block104_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock104Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block104_certificate a).1
    (generatedSixth_xi_short_block104_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
