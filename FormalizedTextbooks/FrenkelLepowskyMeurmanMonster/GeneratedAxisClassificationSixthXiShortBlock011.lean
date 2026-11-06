/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortNumbering
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressMaskEight

/-! Original sparse masks and full signed phases certify a bounded part of actual short support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Candidate sparse outputs are checked against the original full binary and phase action. -/
def generatedSixthXiShortBlock011Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (298, 7)),
    Sum.inr (Sum.inr (52, 6)),
    Sum.inr (Sum.inr (289, 6)),
    Sum.inr (Sum.inr (63, 7)),
    Sum.inr (Sum.inr (298, 4)),
    Sum.inr (Sum.inr (52, 18)),
    Sum.inr (Sum.inr (289, 18)),
    Sum.inr (Sum.inr (63, 4)),
    Sum.inr (Sum.inr (352, 18)),
    Sum.inr (Sum.inr (126, 4)),
    Sum.inr (Sum.inr (363, 4)),
    Sum.inr (Sum.inr (117, 18)),
    Sum.inr (Sum.inr (352, 6)),
    Sum.inr (Sum.inr (126, 7)),
    Sum.inr (Sum.inr (363, 7)),
    Sum.inr (Sum.inr (117, 6)),
    Sum.inr (Sum.inr (352, 7)),
    Sum.inr (Sum.inr (126, 6)),
    Sum.inr (Sum.inr (363, 6)),
    Sum.inr (Sum.inr (117, 7)),
    Sum.inr (Sum.inr (352, 4)),
    Sum.inr (Sum.inr (126, 18)),
    Sum.inr (Sum.inr (363, 18)),
    Sum.inr (Sum.inr (117, 4)),
    Sum.inr (Sum.inr (181, 4)),
    Sum.inr (Sum.inr (427, 18)),
    Sum.inr (Sum.inr (190, 18)),
    Sum.inr (Sum.inr (416, 4)),
    Sum.inr (Sum.inr (181, 7)),
    Sum.inr (Sum.inr (427, 6)),
    Sum.inr (Sum.inr (190, 6)),
    Sum.inr (Sum.inr (416, 7)),
    Sum.inr (Sum.inr (181, 6)),
    Sum.inr (Sum.inr (427, 7)),
    Sum.inr (Sum.inr (190, 7)),
    Sum.inr (Sum.inr (416, 6)),
    Sum.inr (Sum.inr (181, 18)),
    Sum.inr (Sum.inr (427, 4)),
    Sum.inr (Sum.inr (190, 4)),
    Sum.inr (Sum.inr (416, 18)),
    Sum.inr (Sum.inr (497, 18)),
    Sum.inr (Sum.inr (36, 4)),
    Sum.inr (Sum.inr (47, 18)),
    Sum.inr (Sum.inr (506, 4)),
    Sum.inr (Sum.inr (36, 6)),
    Sum.inr (Sum.inr (497, 7)),
    Sum.inr (Sum.inr (506, 6)),
    Sum.inr (Sum.inr (47, 7)),
    Sum.inr (Sum.inr (36, 7)),
    Sum.inr (Sum.inr (497, 6)),
    Sum.inr (Sum.inr (506, 7)),
    Sum.inr (Sum.inr (47, 6)),
    Sum.inr (Sum.inr (497, 4)),
    Sum.inr (Sum.inr (36, 18)),
    Sum.inr (Sum.inr (47, 4)),
    Sum.inr (Sum.inr (506, 18)),
    Sum.inr (Sum.inr (314, 18)),
    Sum.inr (Sum.inr (239, 4)),
    Sum.inr (Sum.inr (228, 18)),
    Sum.inr (Sum.inr (305, 4)),
    Sum.inr (Sum.inr (239, 6)),
    Sum.inr (Sum.inr (314, 7)),
    Sum.inr (Sum.inr (305, 6)),
    Sum.inr (Sum.inr (228, 7)),
    Sum.inr (Sum.inr (239, 7)),
    Sum.inr (Sum.inr (314, 6)),
    Sum.inr (Sum.inr (305, 7)),
    Sum.inr (Sum.inr (228, 6)),
    Sum.inr (Sum.inr (314, 4)),
    Sum.inr (Sum.inr (239, 18)),
    Sum.inr (Sum.inr (228, 4)),
    Sum.inr (Sum.inr (305, 18)),
    Sum.inr (Sum.inr (443, 18)),
    Sum.inr (Sum.inr (110, 4)),
    Sum.inr (Sum.inr (101, 18)),
    Sum.inr (Sum.inr (432, 4)),
    Sum.inr (Sum.inr (110, 6)),
    Sum.inr (Sum.inr (443, 7)),
    Sum.inr (Sum.inr (432, 6)),
    Sum.inr (Sum.inr (101, 7)),
    Sum.inr (Sum.inr (110, 7)),
    Sum.inr (Sum.inr (443, 6)),
    Sum.inr (Sum.inr (432, 7)),
    Sum.inr (Sum.inr (101, 6)),
    Sum.inr (Sum.inr (443, 4)),
    Sum.inr (Sum.inr (110, 18)),
    Sum.inr (Sum.inr (101, 4)),
    Sum.inr (Sum.inr (432, 18)),
    Sum.inr (Sum.inr (368, 18)),
    Sum.inr (Sum.inr (165, 4)),
    Sum.inr (Sum.inr (174, 18)),
    Sum.inr (Sum.inr (379, 4)),
    Sum.inr (Sum.inr (165, 6)),
    Sum.inr (Sum.inr (368, 7)),
    Sum.inr (Sum.inr (379, 6)),
    Sum.inr (Sum.inr (174, 7)),
    Sum.inr (Sum.inr (165, 7)),
    Sum.inr (Sum.inr (368, 6)),
    Sum.inr (Sum.inr (379, 7)),
    Sum.inr (Sum.inr (174, 6)),
    Sum.inr (Sum.inr (368, 4)),
    Sum.inr (Sum.inr (165, 18)),
    Sum.inr (Sum.inr (174, 4)),
    Sum.inr (Sum.inr (379, 18)),
    Sum.inr (Sum.inr (504, 18)),
    Sum.inr (Sum.inr (167, 4)),
    Sum.inr (Sum.inr (172, 18)),
    Sum.inr (Sum.inr (499, 4)),
    Sum.inr (Sum.inr (167, 6)),
    Sum.inr (Sum.inr (504, 7)),
    Sum.inr (Sum.inr (499, 6)),
    Sum.inr (Sum.inr (172, 7)),
    Sum.inr (Sum.inr (167, 7)),
    Sum.inr (Sum.inr (504, 6)),
    Sum.inr (Sum.inr (499, 7)),
    Sum.inr (Sum.inr (172, 6)),
    Sum.inr (Sum.inr (504, 4)),
    Sum.inr (Sum.inr (167, 18)),
    Sum.inr (Sum.inr (172, 4)),
    Sum.inr (Sum.inr (499, 18)),
    Sum.inr (Sum.inr (370, 18)),
    Sum.inr (Sum.inr (45, 4)),
    Sum.inr (Sum.inr (38, 18)),
    Sum.inr (Sum.inr (377, 4)),
    Sum.inr (Sum.inr (45, 6)),
    Sum.inr (Sum.inr (370, 7)),
    Sum.inr (Sum.inr (377, 6)),
    Sum.inr (Sum.inr (38, 7)),
    Sum.inr (Sum.inr (45, 7)),
    Sum.inr (Sum.inr (370, 6)),
    Sum.inr (Sum.inr (377, 7)),
    Sum.inr (Sum.inr (38, 6)),
    Sum.inr (Sum.inr (370, 4)),
    Sum.inr (Sum.inr (45, 18)),
    Sum.inr (Sum.inr (38, 4)),
    Sum.inr (Sum.inr (377, 18)),
    Sum.inr (Sum.inr (312, 18)),
    Sum.inr (Sum.inr (103, 4)),
    Sum.inr (Sum.inr (108, 18)),
    Sum.inr (Sum.inr (307, 4)),
    Sum.inr (Sum.inr (103, 6)),
    Sum.inr (Sum.inr (312, 7)),
    Sum.inr (Sum.inr (307, 6)),
    Sum.inr (Sum.inr (108, 7)),
    Sum.inr (Sum.inr (103, 7)),
    Sum.inr (Sum.inr (312, 6)),
    Sum.inr (Sum.inr (307, 7)),
    Sum.inr (Sum.inr (108, 6)),
    Sum.inr (Sum.inr (312, 4)),
    Sum.inr (Sum.inr (103, 18)),
    Sum.inr (Sum.inr (108, 4)),
    Sum.inr (Sum.inr (307, 18)),
    Sum.inr (Sum.inr (434, 18)),
    Sum.inr (Sum.inr (237, 4)),
    Sum.inr (Sum.inr (230, 18)),
    Sum.inr (Sum.inr (441, 4)),
    Sum.inr (Sum.inr (237, 6)),
    Sum.inr (Sum.inr (434, 7)),
    Sum.inr (Sum.inr (441, 6)),
    Sum.inr (Sum.inr (230, 7)),
    Sum.inr (Sum.inr (237, 7)),
    Sum.inr (Sum.inr (434, 6)),
    Sum.inr (Sum.inr (441, 7)),
    Sum.inr (Sum.inr (230, 6)),
    Sum.inr (Sum.inr (434, 4)),
    Sum.inr (Sum.inr (237, 18)),
    Sum.inr (Sum.inr (230, 4)),
    Sum.inr (Sum.inr (441, 18)),
    Sum.inr (Sum.inr (83, 6)),
    Sum.inr (Sum.inr (460, 18)),
    Sum.inr (Sum.inr (83, 7)),
    Sum.inr (Sum.inr (460, 4)),
    Sum.inr (Sum.inr (88, 18)),
    Sum.inr (Sum.inr (455, 6)),
    Sum.inr (Sum.inr (88, 4)),
    Sum.inr (Sum.inr (455, 7)),
    Sum.inr (Sum.inr (83, 4)),
    Sum.inr (Sum.inr (460, 7)),
    Sum.inr (Sum.inr (83, 18)),
    Sum.inr (Sum.inr (460, 6)),
    Sum.inr (Sum.inr (88, 7)),
    Sum.inr (Sum.inr (455, 4)),
    Sum.inr (Sum.inr (88, 6)),
    Sum.inr (Sum.inr (455, 18)),
    Sum.inr (Sum.inr (333, 18)),
    Sum.inr (Sum.inr (210, 6)),
    Sum.inr (Sum.inr (333, 4)),
    Sum.inr (Sum.inr (210, 7)),
    Sum.inr (Sum.inr (326, 6)),
    Sum.inr (Sum.inr (217, 18)),
    Sum.inr (Sum.inr (326, 7)),
    Sum.inr (Sum.inr (217, 4)),
    Sum.inr (Sum.inr (333, 7)),
    Sum.inr (Sum.inr (210, 4)),
    Sum.inr (Sum.inr (333, 6)),
    Sum.inr (Sum.inr (210, 18)),
    Sum.inr (Sum.inr (326, 4)),
    Sum.inr (Sum.inr (217, 7)),
    Sum.inr (Sum.inr (326, 18)),
    Sum.inr (Sum.inr (217, 6)),
    Sum.inr (Sum.inr (390, 18)),
    Sum.inr (Sum.inr (25, 6)),
    Sum.inr (Sum.inr (390, 4)),
    Sum.inr (Sum.inr (25, 7)),
    Sum.inr (Sum.inr (397, 6)),
    Sum.inr (Sum.inr (18, 18)),
    Sum.inr (Sum.inr (397, 7)),
    Sum.inr (Sum.inr (18, 4)),
    Sum.inr (Sum.inr (390, 7)),
    Sum.inr (Sum.inr (25, 4)),
    Sum.inr (Sum.inr (390, 6)),
    Sum.inr (Sum.inr (25, 18)),
    Sum.inr (Sum.inr (397, 4)),
    Sum.inr (Sum.inr (18, 7)),
    Sum.inr (Sum.inr (397, 18)),
    Sum.inr (Sum.inr (18, 6)),
    Sum.inr (Sum.inr (152, 6)),
    Sum.inr (Sum.inr (263, 18)),
    Sum.inr (Sum.inr (152, 7)),
    Sum.inr (Sum.inr (263, 4)),
    Sum.inr (Sum.inr (147, 18)),
    Sum.inr (Sum.inr (268, 6)),
    Sum.inr (Sum.inr (147, 4)),
    Sum.inr (Sum.inr (268, 7)),
    Sum.inr (Sum.inr (152, 4)),
    Sum.inr (Sum.inr (263, 7)),
    Sum.inr (Sum.inr (152, 18)),
    Sum.inr (Sum.inr (263, 6)),
    Sum.inr (Sum.inr (147, 7)),
    Sum.inr (Sum.inr (268, 4)),
    Sum.inr (Sum.inr (147, 6)),
    Sum.inr (Sum.inr (268, 18)),
    Sum.inr (Sum.inr (496, 18)),
    Sum.inr (Sum.inr (238, 6)),
    Sum.inr (Sum.inr (175, 6)),
    Sum.inr (Sum.inr (433, 18)),
    Sum.inr (Sum.inr (111, 6)),
    Sum.inr (Sum.inr (369, 18)),
    Sum.inr (Sum.inr (304, 18)),
    Sum.inr (Sum.inr (46, 6)),
    Sum.inr (Sum.inr (37, 6)),
    Sum.inr (Sum.inr (315, 18)),
    Sum.inr (Sum.inr (378, 18)),
    Sum.inr (Sum.inr (100, 6)),
    Sum.inr (Sum.inr (442, 18)),
    Sum.inr (Sum.inr (164, 6)),
    Sum.inr (Sum.inr (229, 6)),
    Sum.inr (Sum.inr (507, 18)),
    Sum.inr (Sum.inr (496, 7)),
    Sum.inr (Sum.inr (238, 4)),
    Sum.inr (Sum.inr (175, 4)),
    Sum.inr (Sum.inr (433, 7)),
    Sum.inr (Sum.inr (111, 4)),
    Sum.inr (Sum.inr (369, 7)),
    Sum.inr (Sum.inr (304, 7)),
    Sum.inr (Sum.inr (46, 4))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock011Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨2816 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock011InputMaskData : ℕ :=
  sixthHex% [
    "70080f74f80f14f80f10000f24f80f20000f40000f44f00f40f80f44080f",
    "24080f20f00f14080f10f00f70f00f74000f34080f30f00f50f00f54000f",
    "60f00f64000f04000f00f80f11fe8c784e8c68be8c01068c20be8c49068c",
    "59f68c30468c24be8c4d068c5df68c34468c15f68c7c468c6cb68c050e8c",
    "68ae8c01168c11e68c78568c59e68c30568c20a68c491e8c5de68c34568c",
    "24a68c4d1e8c6ca68c051e8c15ee8c7c5e8c689e8c01268c11d68c78668c",
    "59d68c30668c20968c492e8c5dd68c34668c24968c4d2e8c6c968c052e8c",
    "15de8c7c6e8c11c68c78768c68868c013e8c20868c493e8c59ce8c307e8c",
    "24868c4d3e8c5dce8c347e8c15ce8c7c7e8c6c8e8c05368c7688071b0807",
    "5308073e80075f08073280077a80071700075708073a80077280071f0007",
    "7e80071300075b00073688071b88077600073e00075380073200075f8007",
    "1780077a08073a00075780071f80077208071380077e08073608075b8807",
    "6d88070000074800072580074400072980076180070c08074c0007218007",
    "6980070408076580070808074008072d88070080076d0007250007488807",
    "2900074488070c88076108072100074c8807048807690807088807650807",
    "2d080740800742180e03080e4b080e0a100e47080e06100e4e100e0f000e",
    "4f080e0e100e46100e07000e4a100e0b000e43000e02180e03180e42000e",
    "0a000e4b100e06000e47100e0f100e4e080e0e000e4f100e07100e46080e",
    "0b100e4a080e02080e43180e41180e00000e48000e09100e44000e05100e",
    "4d100e0c080e4c000e0d100e45100e04080e49100e08080e40080e01180e",
    "00100e41000e09000e48180e05000e44180e0c180e4d080e0d000e4c180e",
    "04180e45080e08180e49080e01080e40100e1434202d84202574201ccc20",
    "29742010cc20183c20218c2021742018cc20103c20298c201c3c20258c20",
    "2d7c2014c4202c642015dc201d2c20249c20112c20289c20206c2019d420",
    "192c20209c20286c2011d420246c201dd4201524202c942038542001ec20",
    "091c2030ac20051c203cac20345c200de420"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock011InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock011InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock011OutputMaskData : ℕ :=
  sixthHex% [
    "a758bebc24f0cd6dc1a7518febfee181c2aff08b9eebf7d0abb7dbb0cb95",
    "c182a4abbeeae711848d2dcafc64fbe718b5e358be8964f0f82dc1e3518f",
    "debee1c5c2afb48b9edeb7d0ed442c9ca27394042c94a273e90c27e9aa78",
    "e10c2790ea78d80c2cd8aa73d00c2ca1ea73ad0427dce278d44427d4e278",
    "8b98628b3e3d839862f27e3dfe90698f763687d069877636cf9062be763d",
    "b6d062b6763dcbd869cb7e36c3d869b23e36a83349a89516a03349d1d516",
    "dd3b42acdd1da47b42a4dd1dec3b499ddd16957b4995dd16e87342e8d51d",
    "e0734291951dbfaf07ce4958c6ef07c64958bbe70cbb4153b3e70cc20153",
    "8ae7078a415882e707f30158ffef0c8e095386af0c86095395bee9f6f396",
    "8bfb9d99f6e2b2f396a0fee9ddf6e2bebb9dbafb96a8f6e9d5fee2b6b39d",
    "ecf6e98fbb96f2b39de0bee2ca64f3d8698ca56187c62cf89c698cff24f3",
    "822cf890218794618cf72cf38a24f8982987b32cf3a1218cdc2987bf64f8",
    "9825c98a28b6f720bd946dc2ce28b6ad65c9d06dc2c260bdc620b6a56dc9",
    "d865c2ca68bde16dc9f360b68e68bded25c2b6bfd3d5f2aca8faa7baf7d8",
    "91f2ac83ffd3fef7d89dbaa799faac8bf7d3f6ffd895b2a7cff7d3acbaac",
    "d1b2a7c3bfd8ad2dcbd02aaead22a5a165c0942aae986dcbe565c09862a5",
    "9c22ae9065cbed6dc0906aa5d465cba962aed46aa5d82dc0cfb6e0c3f185",
    "bef98ec3feeb87f185faf6e087feeb8bb98e8ff985f2fee08ff6eb83b18e",
    "b6fee0bab985c7b18ebab6eb8a64f1862394fb2b9f862cfac22394bf24f1",
    "c22cface6b9fca2b94b72cf1ca24fac6639ff32cf1ff6b9482639fff64fa",
    "99bfdae4b8bf99b0b495f7d1a0b8bfacffdad1f7d1acf0b4a8b0bfa4f7da",
    "d9ffd1a4f8b4e0f7da9df0bfe0f8b4ecbfd1e88e80ceb2ceecc68bbbbac5",
    "d5ce8082b2cea0c68b86fac5ddc6808abacea8ce8b8ef2c591c680b7face",
    "958e8bc2f2c5ecc9e5bbb5ab99c1eebffda0a0c9e586f5aba481eef3fda0",
    "a8c1e58efdabac89eefbf5a09581e5c2fdabe089eec6b5a0dcb8df8bc491",
    "a9b0d48f8c9a90b8dfb6849194f0d4c38c9a"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock011OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock011OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerator data, checked against the original coefficient. -/
def generatedSixthXiShortBlock011InputNumeratorData : ℕ :=
  sixthHex% [
    "85f8618617e185f8618617e17df85f85f8617e17df8617e17df85f7e17df",
    "8617e185f8617e17df8617e17df85f7e17df85f8617df85f7e17df8617e1",
    "7df85f7e17df85f8618617e17df85f85f8618617e17e17df85f8618617e1",
    "8617e17e17df85f8618617e17e17df7df85f8617e17e17df7df85f85f861",
    "7e17df7df85f85f8618617e17df85f85f8617e17df7df85f8617e17e17df",
    "7df85f85f8617e17df7df85f7df85f85f8617e17df7df85f7e17df7df85f",
    "8617e17e17df85f8618617e1"
  ]

/-- Decode the candidate signed numerator with the original sign convention. -/
def generatedSixthXiShortBlock011InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock011InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerator data, checked against the original coefficient. -/
def generatedSixthXiShortBlock011OutputNumeratorData : ℕ :=
  sixthHex% [
    "86185f85f7df7df7e17e18617e186186185f85f8618617e18617e17e17df",
    "7df85f85f86185f8618617e18617e17e17df7e17df7df85f85f8618617e1",
    "8617e17e17df7df85f85f8617e17df7df85f7e17df7df85f8617e17e17df",
    "85f8618617e17df85f85f8617df85f85f8617e17df7df85f8617e17e17df",
    "85f8618617e185f8618617e17df85f85f8617e17df7df85f8617e17e17df",
    "8617e17e17df85f8618617e185f7df7df7e186185f85f7df86185f85f7df",
    "7e186186185f7df7e17e1861"
  ]

/-- Decode the candidate signed numerator with the original sign convention. -/
def generatedSixthXiShortBlock011OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock011OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block011_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock011Input a) =
      generatedSixthXiShortBlock011InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock011Output a) =
      generatedSixthXiShortBlock011OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock011Input a) =
      generatedSixthXiShortBlock011InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock011Output a) =
      generatedSixthXiShortBlock011OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block011_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock011InputMask a) =
      generatedSixthXiShortBlock011OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortBlock011InputMask a)) *
      generatedSixthXiShortBlock011InputNumerator a =
        generatedSixthXiShortBlock011OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block011_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock011Input a
    let y := generatedSixthXiShortBlock011Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block011_cache a
  have hs := generatedSixth_xi_short_block011_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block011_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock011Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block011_certificate a).1
    (generatedSixth_xi_short_block011_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
