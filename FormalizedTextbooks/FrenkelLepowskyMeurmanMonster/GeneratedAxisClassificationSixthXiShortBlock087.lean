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
def generatedSixthXiShortBlock087Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (148, 13)),
    Sum.inr (Sum.inr (213, 1)),
    Sum.inr (Sum.inr (21, 21)),
    Sum.inr (Sum.inr (95, 10)),
    Sum.inr (Sum.inr (394, 7)),
    Sum.inr (Sum.inr (385, 5)),
    Sum.inr (Sum.inr (394, 18)),
    Sum.inr (Sum.inr (394, 4)),
    Sum.inr (Sum.inr (148, 23)),
    Sum.inr (Sum.inr (21, 14)),
    Sum.inr (Sum.inr (95, 3)),
    Sum.inr (Sum.inr (213, 11)),
    Sum.inr (Sum.inr (95, 20)),
    Sum.inr (Sum.inr (148, 0)),
    Sum.inr (Sum.inr (21, 9)),
    Sum.inr (Sum.inr (213, 15)),
    Sum.inr (Sum.inr (385, 16)),
    Sum.inr (Sum.inr (385, 17)),
    Sum.inr (Sum.inr (394, 6)),
    Sum.inr (Sum.inr (385, 19)),
    Sum.inr (Sum.inr (95, 12)),
    Sum.inr (Sum.inr (21, 2)),
    Sum.inr (Sum.inr (213, 22)),
    Sum.inr (Sum.inr (148, 8)),
    Sum.inr (Sum.inr (87, 8)),
    Sum.inr (Sum.inr (22, 22)),
    Sum.inr (Sum.inr (214, 2)),
    Sum.inr (Sum.inr (156, 12)),
    Sum.inr (Sum.inr (329, 7)),
    Sum.inr (Sum.inr (322, 5)),
    Sum.inr (Sum.inr (329, 18)),
    Sum.inr (Sum.inr (329, 4)),
    Sum.inr (Sum.inr (87, 0)),
    Sum.inr (Sum.inr (214, 9)),
    Sum.inr (Sum.inr (156, 20)),
    Sum.inr (Sum.inr (22, 15)),
    Sum.inr (Sum.inr (156, 3)),
    Sum.inr (Sum.inr (87, 23)),
    Sum.inr (Sum.inr (214, 14)),
    Sum.inr (Sum.inr (22, 11)),
    Sum.inr (Sum.inr (322, 16)),
    Sum.inr (Sum.inr (322, 17)),
    Sum.inr (Sum.inr (329, 6)),
    Sum.inr (Sum.inr (322, 19)),
    Sum.inr (Sum.inr (156, 10)),
    Sum.inr (Sum.inr (214, 21)),
    Sum.inr (Sum.inr (22, 1)),
    Sum.inr (Sum.inr (87, 13)),
    Sum.inr (Sum.inr (215, 0)),
    Sum.inr (Sum.inr (150, 15)),
    Sum.inr (Sum.inr (86, 9)),
    Sum.inr (Sum.inr (28, 20)),
    Sum.inr (Sum.inr (457, 7)),
    Sum.inr (Sum.inr (450, 5)),
    Sum.inr (Sum.inr (457, 18)),
    Sum.inr (Sum.inr (457, 4)),
    Sum.inr (Sum.inr (215, 8)),
    Sum.inr (Sum.inr (86, 2)),
    Sum.inr (Sum.inr (28, 12)),
    Sum.inr (Sum.inr (150, 22)),
    Sum.inr (Sum.inr (28, 10)),
    Sum.inr (Sum.inr (215, 13)),
    Sum.inr (Sum.inr (86, 21)),
    Sum.inr (Sum.inr (150, 1)),
    Sum.inr (Sum.inr (450, 16)),
    Sum.inr (Sum.inr (450, 17)),
    Sum.inr (Sum.inr (457, 6)),
    Sum.inr (Sum.inr (450, 19)),
    Sum.inr (Sum.inr (28, 3)),
    Sum.inr (Sum.inr (86, 14)),
    Sum.inr (Sum.inr (150, 11)),
    Sum.inr (Sum.inr (215, 23)),
    Sum.inr (Sum.inl (53, 13)),
    Sum.inr (Sum.inl (52, 19)),
    Sum.inr (Sum.inl (46, 51)),
    Sum.inr (Sum.inl (48, 40)),
    Sum.inr (Sum.inl (21, 49)),
    Sum.inr (Sum.inl (1, 61)),
    Sum.inr (Sum.inl (21, 57)),
    Sum.inr (Sum.inl (21, 59)),
    Sum.inr (Sum.inl (53, 28)),
    Sum.inr (Sum.inl (46, 34)),
    Sum.inr (Sum.inl (48, 56)),
    Sum.inr (Sum.inl (52, 51)),
    Sum.inr (Sum.inl (48, 44)),
    Sum.inr (Sum.inl (53, 12)),
    Sum.inr (Sum.inl (46, 35)),
    Sum.inr (Sum.inl (52, 50)),
    Sum.inr (Sum.inl (1, 29)),
    Sum.inr (Sum.inl (1, 45)),
    Sum.inr (Sum.inl (21, 51)),
    Sum.inr (Sum.inl (1, 13)),
    Sum.inr (Sum.inl (48, 60)),
    Sum.inr (Sum.inl (46, 50)),
    Sum.inr (Sum.inl (52, 18)),
    Sum.inr (Sum.inl (53, 29)),
    Sum.inr (Sum.inl (119, 3)),
    Sum.inr (Sum.inl (118, 40)),
    Sum.inr (Sum.inl (112, 62)),
    Sum.inr (Sum.inl (114, 19)),
    Sum.inr (Sum.inl (25, 1)),
    Sum.inr (Sum.inl (5, 49)),
    Sum.inr (Sum.inl (25, 9)),
    Sum.inr (Sum.inl (25, 11)),
    Sum.inr (Sum.inl (119, 18)),
    Sum.inr (Sum.inl (112, 44)),
    Sum.inr (Sum.inl (114, 3)),
    Sum.inr (Sum.inl (118, 55)),
    Sum.inr (Sum.inl (114, 1)),
    Sum.inr (Sum.inl (119, 44)),
    Sum.inr (Sum.inl (112, 3)),
    Sum.inr (Sum.inl (118, 31)),
    Sum.inr (Sum.inl (5, 17)),
    Sum.inr (Sum.inl (5, 33)),
    Sum.inr (Sum.inl (25, 3)),
    Sum.inr (Sum.inl (5, 1)),
    Sum.inr (Sum.inl (114, 17)),
    Sum.inr (Sum.inl (112, 17)),
    Sum.inr (Sum.inl (118, 0)),
    Sum.inr (Sum.inl (119, 61)),
    Sum.inr (Sum.inl (213, 35)),
    Sum.inr (Sum.inl (207, 13)),
    Sum.inr (Sum.inl (150, 27)),
    Sum.inr (Sum.inl (173, 12)),
    Sum.inr (Sum.inl (38, 46)),
    Sum.inr (Sum.inl (18, 10)),
    Sum.inr (Sum.inl (38, 38)),
    Sum.inr (Sum.inl (38, 36)),
    Sum.inr (Sum.inl (213, 60)),
    Sum.inr (Sum.inl (150, 59)),
    Sum.inr (Sum.inl (173, 46)),
    Sum.inr (Sum.inl (207, 44)),
    Sum.inr (Sum.inl (173, 44)),
    Sum.inr (Sum.inl (213, 2)),
    Sum.inr (Sum.inl (150, 19)),
    Sum.inr (Sum.inl (207, 51)),
    Sum.inr (Sum.inl (18, 42)),
    Sum.inr (Sum.inl (18, 26)),
    Sum.inr (Sum.inl (38, 44)),
    Sum.inr (Sum.inl (18, 58)),
    Sum.inr (Sum.inl (173, 14)),
    Sum.inr (Sum.inl (150, 51)),
    Sum.inr (Sum.inl (207, 18)),
    Sum.inr (Sum.inl (213, 29)),
    Sum.inr (Sum.inl (158, 27)),
    Sum.inr (Sum.inl (157, 60)),
    Sum.inr (Sum.inl (140, 35)),
    Sum.inr (Sum.inl (153, 62)),
    Sum.inr (Sum.inl (28, 30)),
    Sum.inr (Sum.inl (8, 6)),
    Sum.inr (Sum.inl (28, 22)),
    Sum.inr (Sum.inl (28, 20)),
    Sum.inr (Sum.inl (158, 52)),
    Sum.inr (Sum.inl (140, 12)),
    Sum.inr (Sum.inl (153, 28)),
    Sum.inr (Sum.inl (157, 30)),
    Sum.inr (Sum.inl (153, 60)),
    Sum.inr (Sum.inl (158, 32)),
    Sum.inr (Sum.inl (140, 49)),
    Sum.inr (Sum.inl (157, 35)),
    Sum.inr (Sum.inl (8, 38)),
    Sum.inr (Sum.inl (8, 22)),
    Sum.inr (Sum.inl (28, 28)),
    Sum.inr (Sum.inl (8, 54)),
    Sum.inr (Sum.inl (153, 30)),
    Sum.inr (Sum.inl (140, 30)),
    Sum.inr (Sum.inl (157, 1)),
    Sum.inr (Sum.inl (158, 15)),
    Sum.inr (Sum.inr (220, 0)),
    Sum.inr (Sum.inr (157, 15)),
    Sum.inr (Sum.inr (93, 9)),
    Sum.inr (Sum.inr (23, 20)),
    Sum.inr (Sum.inr (450, 7)),
    Sum.inr (Sum.inr (457, 5)),
    Sum.inr (Sum.inr (450, 18)),
    Sum.inr (Sum.inr (450, 4)),
    Sum.inr (Sum.inr (220, 8)),
    Sum.inr (Sum.inr (93, 2)),
    Sum.inr (Sum.inr (23, 12)),
    Sum.inr (Sum.inr (157, 22)),
    Sum.inr (Sum.inr (23, 10)),
    Sum.inr (Sum.inr (220, 13)),
    Sum.inr (Sum.inr (93, 21)),
    Sum.inr (Sum.inr (157, 1)),
    Sum.inr (Sum.inr (457, 16)),
    Sum.inr (Sum.inr (457, 17)),
    Sum.inr (Sum.inr (450, 6)),
    Sum.inr (Sum.inr (457, 19)),
    Sum.inr (Sum.inr (23, 3)),
    Sum.inr (Sum.inr (93, 14)),
    Sum.inr (Sum.inr (157, 11)),
    Sum.inr (Sum.inr (220, 23)),
    Sum.inr (Sum.inr (92, 8)),
    Sum.inr (Sum.inr (29, 22)),
    Sum.inr (Sum.inr (221, 2)),
    Sum.inr (Sum.inr (151, 12)),
    Sum.inr (Sum.inr (322, 7)),
    Sum.inr (Sum.inr (329, 5)),
    Sum.inr (Sum.inr (322, 18)),
    Sum.inr (Sum.inr (322, 4)),
    Sum.inr (Sum.inr (92, 0)),
    Sum.inr (Sum.inr (221, 9)),
    Sum.inr (Sum.inr (151, 20)),
    Sum.inr (Sum.inr (29, 15)),
    Sum.inr (Sum.inr (151, 3)),
    Sum.inr (Sum.inr (92, 23)),
    Sum.inr (Sum.inr (221, 14)),
    Sum.inr (Sum.inr (29, 11)),
    Sum.inr (Sum.inr (329, 16)),
    Sum.inr (Sum.inr (329, 17)),
    Sum.inr (Sum.inr (322, 6)),
    Sum.inr (Sum.inr (329, 19)),
    Sum.inr (Sum.inr (151, 10)),
    Sum.inr (Sum.inr (221, 21)),
    Sum.inr (Sum.inr (29, 1)),
    Sum.inr (Sum.inr (92, 13)),
    Sum.inr (Sum.inr (159, 13)),
    Sum.inr (Sum.inr (222, 1)),
    Sum.inr (Sum.inr (30, 21)),
    Sum.inr (Sum.inr (84, 10)),
    Sum.inr (Sum.inr (385, 7)),
    Sum.inr (Sum.inr (394, 5)),
    Sum.inr (Sum.inr (385, 18)),
    Sum.inr (Sum.inr (385, 4)),
    Sum.inr (Sum.inr (159, 23)),
    Sum.inr (Sum.inr (30, 14)),
    Sum.inr (Sum.inr (84, 3)),
    Sum.inr (Sum.inr (222, 11)),
    Sum.inr (Sum.inr (84, 20)),
    Sum.inr (Sum.inr (159, 0)),
    Sum.inr (Sum.inr (30, 9)),
    Sum.inr (Sum.inr (222, 15)),
    Sum.inr (Sum.inr (394, 16)),
    Sum.inr (Sum.inr (394, 17)),
    Sum.inr (Sum.inr (385, 6)),
    Sum.inr (Sum.inr (394, 19)),
    Sum.inr (Sum.inr (84, 12)),
    Sum.inr (Sum.inr (30, 2)),
    Sum.inr (Sum.inr (222, 22)),
    Sum.inr (Sum.inr (159, 8)),
    Sum.inr (Sum.inr (20, 23)),
    Sum.inr (Sum.inr (85, 11)),
    Sum.inr (Sum.inr (149, 14)),
    Sum.inr (Sum.inr (223, 3)),
    Sum.inr (Sum.inr (266, 7)),
    Sum.inr (Sum.inr (257, 5)),
    Sum.inr (Sum.inr (266, 18)),
    Sum.inr (Sum.inr (266, 4)),
    Sum.inr (Sum.inr (20, 13)),
    Sum.inr (Sum.inr (149, 21)),
    Sum.inr (Sum.inr (223, 10)),
    Sum.inr (Sum.inr (85, 1)),
    Sum.inr (Sum.inr (223, 12)),
    Sum.inr (Sum.inr (20, 8)),
    Sum.inr (Sum.inr (149, 2)),
    Sum.inr (Sum.inr (85, 22))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock087Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨22272 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock087InputMaskData : ℕ :=
  sixthHex% [
    "f2ac9bd8a49be7a49b8da49bce949bcc949bcf9c9b8d949bc18c9bc9849b",
    "c58c9b8d8c9bbd749b9d749bad749bcd7c9bd40c9ae20c9af90c9a8f049a",
    "e8cc9af6c49ad1cc9a8fcc9af0ac9adaa49ae5a49a8fa49acc9c9ace9c9a",
    "cd949a8f9c9ac38c9acb849ac78c9a8f8c9abf7c9a9f7c9aaf7c9acf749a",
    "e90c99df0c99c40c99b20499d5cc99cbc499eccc99b2cc99cda499e7ac99",
    "d8ac99b2ac99f19499f39499f09c99b29499fe8c99f68499fa8c99b28c99",
    "827c99a27c99927c99f27499ab04989d0498860498f00c9897c49889cc98",
    "aec498f0c4988fac98a5a4989aa498f0a498b39498b19498b29c98f09498",
    "bc8498b48c98b88498f08498c07c98e07c98d07c98b07498ef0c97d90c97",
    "c20c97b40497d3cc97cdc497eacc97b4cc97cba497e1ac97deac97b4ac97",
    "f79c97f59c97f69497b49c97f88497f08c97fc8497b48497847c97a47c97",
    "947c97f47497ed0c96db0c96c00c96b60496d1cc96cfc496e8cc96b6cc96",
    "c9a496e3ac96dcac96b6ac96f59496f79496f49c96b69496fa8496f28c96",
    "fe8496b68496867496a67496967496f67c96d00c95e60c95fd0c958b0495",
    "eccc95f2c495d5cc958bcc95f4ac95dea495e1a4958ba495c89c95ca9c95",
    "c994958b9c95c78495cf8c95c384958b8495bb74959b7495ab7495cb7c95",
    "920494a40494bf0494c90c94aec494b0cc9497c494c9c494b6a4949cac94",
    "a3ac94c9ac948a9c94889c948b9494c99c94858c948d8494818c94c98c94",
    "f97494d97494e97494897c94d60c93e00c93fb0c938d0493eac493f4cc93",
    "d3c4938dc493f2a493d8ac93e7ac938dac93ce9c93cc9c93cf94938d9c93",
    "c18493c98c93c584938d8493bd74939d7493ad7493cd7c93940492a20492",
    "b90492cf0c92a8cc92b6c49291cc92cfcc92b0ac929aa492a5a492cfa492",
    "8c9c928e9c928d9492cf9c92838c928b8492878c92cf8c92ff7492df7492",
    "ef74928f7c92a904919f0491840491f20c9195cc918bc491accc91f2cc91",
    "8da491a7ac9198ac91f2ac91b19491b39491b09c91f29491be8c91b68491",
    "ba8c91f28c91c27491e27491d27491b27c91"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock087InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock087InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock087OutputMaskData : ℕ :=
  sixthHex% [
    "85e955c83a75f0e864b97b4fc89955f84b4fae42759ad064b8042ac14c2a",
    "890421f40c2a89a34f8dea75ab7955ab7064837a7fa43b4ea9a06e8aa154",
    "95363acf7631ac363af2363ab6934efb406ec3927f8a01548aa34eba7154",
    "ec786ed8ea7f8b7e31f23631ba7e3ac77631cb9954cfd06ee9434ee94a7f",
    "80d15ca7906daa0b4d890a77969d19ccdd12af9d19f19d19c4786d89ab4d",
    "b1795cf8ea77f8486dc89a779e934daa015c88d512f19d12b9d519c4dd12",
    "c83277cc7b4deae86deae15cb7eb4c90aa7d9d315dbe3067a1a709fbe702",
    "98a709c6a709f3427dbe915d86434ccfd067be327d8ee067d8e95dec7b4c",
    "bfef02c6a7028eef09f3e7028e48678a015dac927dac9b4c0720d92061e8",
    "2dfac80efbf2116c9c4b2c97286c9c766c9c4389e80e5ac83688d97f1bf2",
    "0ef9e83e2bf26822c85cb0d97e6497072c974f649c326c974fc3f24b8ac8",
    "6d19e86d10d9345ac2131bf31e80d33d81e922168778568c1b1687451687",
    "70f3f33d20d305f2c24c61e94cc3f37c11e92a18d31e8ac24d1e8c34568c",
    "7c1e8701168c0df9e909b0d32f23f32f2ac237f1e110b0d01d2bf03e2aca",
    "21bda47bfdaf18bda446bda40218d04fcbf07719e13e8aca3e28d00efaca",
    "58f3f06c61e14eb5af37fdaf7fb5a402bdaf0e52ca0a1bf02c88d02c81e1",
    "00cbf1278ac02a11e00910da1687b44cc7bf2f87b47187b43522c078f1e0",
    "4023f109b0da7852c04880da1e89e02a1bf1798fbf00c7bf488fb43587bf",
    "4828da4c61e06af2c06afbf1bfa34798e276957956b6786cd8af0282ef09",
    "e1af02bfaf02fb0a76b6d9568e0b47c7986cb67a7686a86cd0a156e43347",
    "c6e709bfaf09f7e7028aef0986006c824956a4da76a4d347889957afd866",
    "a2434681427cef9512b5d519d69512889512cc306681e346b93157f0a27c",
    "f00066c0d27c96db46a24957f1dd19889519c0dd12bdd519c07a7cc43346",
    "e2a066e2a9578b3274ac7345a1e86582e95fec3e31b67e3ad53e318b3e31",
    "bedb45f30865cbda7482495f82eb45b2395fe43065d0a274f2763a8b3e3a",
    "c37631be7e3ac3d15fc79865e10b45e10274"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock087OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock087OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock087InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock087InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock087InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock087OutputNumeratorData : ℕ :=
  sixthHex% [
    "8617df85f85f7df7df7e185f7e17e16df8e37e185f8617df86186185f85f",
    "85f7e196175d7df86185f85f7df7df85f7e185f85f96175d7e185f7df861",
    "7df7df85f85f86185f95f75d7e17df7df7e185f7df8617e17df85f6e18e3",
    "86185f7e18617e18617df7e17df7e16e18e37e17df86185f7e18618617e1",
    "8617e195f75d86185f85f7df85f7df7df7e17e17e16df8e385f7e18617df",
    "8618617e17e17e185f6df8e38617df7e17e18618617e185f85f85f96175d",
    "85f7e17df8617df7df7e17e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock087OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock087OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block087_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock087Input a) =
      generatedSixthXiShortBlock087InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock087Output a) =
      generatedSixthXiShortBlock087OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock087Input a) =
      generatedSixthXiShortBlock087InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock087Output a) =
      generatedSixthXiShortBlock087OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block087_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock087InputMask a) =
      generatedSixthXiShortBlock087OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock087InputMask a)) *
      generatedSixthXiShortBlock087InputNumerator a =
        generatedSixthXiShortBlock087OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block087_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock087Input a
    let y := generatedSixthXiShortBlock087Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block087_cache a
  have hs := generatedSixth_xi_short_block087_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block087_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock087Input a
    let y := generatedSixthXiShortBlock087Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block087_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block087_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock087Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block087_certificate a).1
    (generatedSixth_xi_short_block087_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
