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
def generatedSixthXiShortBlock046Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (405, 12)),
    Sum.inr (Sum.inr (479, 3)),
    Sum.inr (Sum.inr (405, 10)),
    Sum.inr (Sum.inr (479, 20)),
    Sum.inr (Sum.inr (75, 3)),
    Sum.inr (Sum.inr (1, 12)),
    Sum.inr (Sum.inr (75, 20)),
    Sum.inr (Sum.inr (1, 10)),
    Sum.inr (Sum.inr (202, 20)),
    Sum.inr (Sum.inr (128, 10)),
    Sum.inr (Sum.inr (202, 3)),
    Sum.inr (Sum.inr (128, 12)),
    Sum.inr (Sum.inr (276, 10)),
    Sum.inr (Sum.inr (350, 20)),
    Sum.inr (Sum.inr (276, 12)),
    Sum.inr (Sum.inr (350, 3)),
    Sum.inr (Sum.inr (287, 10)),
    Sum.inr (Sum.inr (341, 20)),
    Sum.inr (Sum.inr (287, 12)),
    Sum.inr (Sum.inr (341, 3)),
    Sum.inr (Sum.inr (193, 20)),
    Sum.inr (Sum.inr (139, 10)),
    Sum.inr (Sum.inr (193, 3)),
    Sum.inr (Sum.inr (139, 12)),
    Sum.inr (Sum.inr (202, 12)),
    Sum.inr (Sum.inr (128, 3)),
    Sum.inr (Sum.inr (202, 10)),
    Sum.inr (Sum.inr (128, 20)),
    Sum.inr (Sum.inr (276, 3)),
    Sum.inr (Sum.inr (350, 12)),
    Sum.inr (Sum.inr (276, 20)),
    Sum.inr (Sum.inr (350, 10)),
    Sum.inr (Sum.inr (287, 3)),
    Sum.inr (Sum.inr (341, 12)),
    Sum.inr (Sum.inr (287, 20)),
    Sum.inr (Sum.inr (341, 10)),
    Sum.inr (Sum.inr (193, 12)),
    Sum.inr (Sum.inr (139, 3)),
    Sum.inr (Sum.inr (193, 10)),
    Sum.inr (Sum.inr (139, 20)),
    Sum.inr (Sum.inl (54, 2)),
    Sum.inr (Sum.inl (230, 36)),
    Sum.inr (Sum.inl (54, 14)),
    Sum.inr (Sum.inl (230, 44)),
    Sum.inr (Sum.inl (73, 62)),
    Sum.inr (Sum.inl (111, 61)),
    Sum.inr (Sum.inl (73, 60)),
    Sum.inr (Sum.inl (111, 49)),
    Sum.inr (Sum.inl (107, 32)),
    Sum.inr (Sum.inl (156, 32)),
    Sum.inr (Sum.inl (107, 50)),
    Sum.inr (Sum.inl (156, 44)),
    Sum.inr (Sum.inl (92, 63)),
    Sum.inr (Sum.inl (176, 31)),
    Sum.inr (Sum.inl (92, 60)),
    Sum.inr (Sum.inl (176, 29)),
    Sum.inr (Sum.inl (73, 26)),
    Sum.inr (Sum.inl (111, 45)),
    Sum.inr (Sum.inl (73, 24)),
    Sum.inr (Sum.inl (111, 33)),
    Sum.inr (Sum.inl (54, 60)),
    Sum.inr (Sum.inl (230, 26)),
    Sum.inr (Sum.inl (54, 48)),
    Sum.inr (Sum.inl (230, 18)),
    Sum.inr (Sum.inl (92, 27)),
    Sum.inr (Sum.inl (176, 11)),
    Sum.inr (Sum.inl (92, 24)),
    Sum.inr (Sum.inl (176, 9)),
    Sum.inr (Sum.inl (107, 30)),
    Sum.inr (Sum.inl (156, 30)),
    Sum.inr (Sum.inl (107, 12)),
    Sum.inr (Sum.inl (156, 18)),
    Sum.inr (Sum.inl (230, 6)),
    Sum.inr (Sum.inl (54, 34)),
    Sum.inr (Sum.inl (230, 14)),
    Sum.inr (Sum.inl (54, 46)),
    Sum.inr (Sum.inl (111, 3)),
    Sum.inr (Sum.inl (73, 17)),
    Sum.inr (Sum.inl (111, 15)),
    Sum.inr (Sum.inl (73, 19)),
    Sum.inr (Sum.inl (156, 2)),
    Sum.inr (Sum.inl (107, 36)),
    Sum.inr (Sum.inl (156, 14)),
    Sum.inr (Sum.inl (107, 54)),
    Sum.inr (Sum.inl (176, 62)),
    Sum.inr (Sum.inl (92, 8)),
    Sum.inr (Sum.inl (176, 60)),
    Sum.inr (Sum.inl (92, 11)),
    Sum.inr (Sum.inl (111, 19)),
    Sum.inr (Sum.inl (73, 53)),
    Sum.inr (Sum.inl (111, 31)),
    Sum.inr (Sum.inl (73, 55)),
    Sum.inr (Sum.inl (230, 56)),
    Sum.inr (Sum.inl (54, 28)),
    Sum.inr (Sum.inl (230, 48)),
    Sum.inr (Sum.inl (54, 16)),
    Sum.inr (Sum.inl (176, 42)),
    Sum.inr (Sum.inl (92, 44)),
    Sum.inr (Sum.inl (176, 40)),
    Sum.inr (Sum.inl (92, 47)),
    Sum.inr (Sum.inl (156, 60)),
    Sum.inr (Sum.inl (107, 26)),
    Sum.inr (Sum.inl (156, 48)),
    Sum.inr (Sum.inl (107, 8)),
    Sum.inr (Sum.inl (124, 36)),
    Sum.inr (Sum.inl (78, 48)),
    Sum.inr (Sum.inl (78, 60)),
    Sum.inr (Sum.inl (124, 44)),
    Sum.inr (Sum.inl (225, 55)),
    Sum.inr (Sum.inl (139, 61)),
    Sum.inr (Sum.inl (139, 49)),
    Sum.inr (Sum.inl (225, 37)),
    Sum.inr (Sum.inl (155, 60)),
    Sum.inr (Sum.inl (72, 45)),
    Sum.inr (Sum.inl (72, 33)),
    Sum.inr (Sum.inl (155, 62)),
    Sum.inr (Sum.inl (55, 22)),
    Sum.inr (Sum.inl (177, 7)),
    Sum.inr (Sum.inl (177, 4)),
    Sum.inr (Sum.inl (55, 20)),
    Sum.inr (Sum.inl (124, 48)),
    Sum.inr (Sum.inl (78, 32)),
    Sum.inr (Sum.inl (78, 44)),
    Sum.inr (Sum.inl (124, 56)),
    Sum.inr (Sum.inl (225, 31)),
    Sum.inr (Sum.inl (139, 31)),
    Sum.inr (Sum.inl (139, 19)),
    Sum.inr (Sum.inl (225, 13)),
    Sum.inr (Sum.inl (155, 11)),
    Sum.inr (Sum.inl (72, 15)),
    Sum.inr (Sum.inl (72, 3)),
    Sum.inr (Sum.inl (155, 9)),
    Sum.inr (Sum.inl (55, 7)),
    Sum.inr (Sum.inl (177, 23)),
    Sum.inr (Sum.inl (177, 20)),
    Sum.inr (Sum.inl (55, 5)),
    Sum.inr (Sum.inl (155, 24)),
    Sum.inr (Sum.inl (72, 2)),
    Sum.inr (Sum.inl (72, 14)),
    Sum.inr (Sum.inl (155, 26)),
    Sum.inr (Sum.inl (55, 62)),
    Sum.inr (Sum.inl (177, 47)),
    Sum.inr (Sum.inl (177, 44)),
    Sum.inr (Sum.inl (55, 60)),
    Sum.inr (Sum.inl (124, 25)),
    Sum.inr (Sum.inl (78, 13)),
    Sum.inr (Sum.inl (78, 1)),
    Sum.inr (Sum.inl (124, 17)),
    Sum.inr (Sum.inl (225, 54)),
    Sum.inr (Sum.inl (139, 60)),
    Sum.inr (Sum.inl (139, 48)),
    Sum.inr (Sum.inl (225, 36)),
    Sum.inr (Sum.inl (155, 47)),
    Sum.inr (Sum.inl (72, 32)),
    Sum.inr (Sum.inl (72, 44)),
    Sum.inr (Sum.inl (155, 45)),
    Sum.inr (Sum.inl (55, 47)),
    Sum.inr (Sum.inl (177, 63)),
    Sum.inr (Sum.inl (177, 60)),
    Sum.inr (Sum.inl (55, 45)),
    Sum.inr (Sum.inl (124, 13)),
    Sum.inr (Sum.inl (78, 29)),
    Sum.inr (Sum.inl (78, 17)),
    Sum.inr (Sum.inl (124, 5)),
    Sum.inr (Sum.inl (225, 30)),
    Sum.inr (Sum.inl (139, 30)),
    Sum.inr (Sum.inl (139, 18)),
    Sum.inr (Sum.inl (225, 12)),
    Sum.inr (Sum.inr (137, 1)),
    Sum.inr (Sum.inr (343, 1)),
    Sum.inr (Sum.inr (348, 1)),
    Sum.inr (Sum.inr (130, 1)),
    Sum.inr (Sum.inr (66, 1)),
    Sum.inr (Sum.inr (412, 1)),
    Sum.inr (Sum.inr (407, 1)),
    Sum.inr (Sum.inr (73, 1)),
    Sum.inr (Sum.inr (3, 11)),
    Sum.inr (Sum.inr (477, 11)),
    Sum.inr (Sum.inr (470, 11)),
    Sum.inr (Sum.inr (8, 11)),
    Sum.inr (Sum.inr (200, 11)),
    Sum.inr (Sum.inr (278, 11)),
    Sum.inr (Sum.inr (285, 11)),
    Sum.inr (Sum.inr (195, 11)),
    Sum.inr (Sum.inr (195, 1)),
    Sum.inr (Sum.inr (285, 1)),
    Sum.inr (Sum.inr (278, 1)),
    Sum.inr (Sum.inr (200, 1)),
    Sum.inr (Sum.inr (8, 1)),
    Sum.inr (Sum.inr (470, 1)),
    Sum.inr (Sum.inr (477, 1)),
    Sum.inr (Sum.inr (3, 1)),
    Sum.inr (Sum.inr (73, 11)),
    Sum.inr (Sum.inr (407, 11)),
    Sum.inr (Sum.inr (412, 11)),
    Sum.inr (Sum.inr (66, 11)),
    Sum.inr (Sum.inr (130, 11)),
    Sum.inr (Sum.inr (348, 11)),
    Sum.inr (Sum.inr (343, 11)),
    Sum.inr (Sum.inr (137, 11)),
    Sum.inr (Sum.inr (3, 15)),
    Sum.inr (Sum.inr (477, 15)),
    Sum.inr (Sum.inr (470, 15)),
    Sum.inr (Sum.inr (8, 15)),
    Sum.inr (Sum.inr (200, 15)),
    Sum.inr (Sum.inr (278, 15)),
    Sum.inr (Sum.inr (285, 15)),
    Sum.inr (Sum.inr (195, 15)),
    Sum.inr (Sum.inr (137, 22)),
    Sum.inr (Sum.inr (343, 22)),
    Sum.inr (Sum.inr (348, 22)),
    Sum.inr (Sum.inr (130, 22)),
    Sum.inr (Sum.inr (66, 22)),
    Sum.inr (Sum.inr (412, 22)),
    Sum.inr (Sum.inr (407, 22)),
    Sum.inr (Sum.inr (73, 22)),
    Sum.inr (Sum.inr (73, 15)),
    Sum.inr (Sum.inr (407, 15)),
    Sum.inr (Sum.inr (412, 15)),
    Sum.inr (Sum.inr (66, 15)),
    Sum.inr (Sum.inr (130, 15)),
    Sum.inr (Sum.inr (348, 15)),
    Sum.inr (Sum.inr (343, 15)),
    Sum.inr (Sum.inr (137, 15)),
    Sum.inr (Sum.inr (195, 22)),
    Sum.inr (Sum.inr (285, 22)),
    Sum.inr (Sum.inr (278, 22)),
    Sum.inr (Sum.inr (200, 22)),
    Sum.inr (Sum.inr (8, 22)),
    Sum.inr (Sum.inr (470, 22)),
    Sum.inr (Sum.inr (477, 22)),
    Sum.inr (Sum.inr (3, 22)),
    Sum.inr (Sum.inr (137, 8)),
    Sum.inr (Sum.inr (66, 0)),
    Sum.inr (Sum.inr (3, 8)),
    Sum.inr (Sum.inr (200, 0)),
    Sum.inr (Sum.inr (343, 8)),
    Sum.inr (Sum.inr (412, 0)),
    Sum.inr (Sum.inr (477, 8)),
    Sum.inr (Sum.inr (278, 0)),
    Sum.inr (Sum.inr (348, 8)),
    Sum.inr (Sum.inr (407, 0)),
    Sum.inr (Sum.inr (470, 8)),
    Sum.inr (Sum.inr (285, 0)),
    Sum.inr (Sum.inr (130, 8)),
    Sum.inr (Sum.inr (73, 0)),
    Sum.inr (Sum.inr (8, 8)),
    Sum.inr (Sum.inr (195, 0)),
    Sum.inr (Sum.inr (66, 13)),
    Sum.inr (Sum.inr (137, 23)),
    Sum.inr (Sum.inr (200, 13)),
    Sum.inr (Sum.inr (3, 23)),
    Sum.inr (Sum.inr (412, 13)),
    Sum.inr (Sum.inr (343, 23)),
    Sum.inr (Sum.inr (278, 13)),
    Sum.inr (Sum.inr (477, 23))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock046Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨11776 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock046InputMaskData : ℕ :=
  sixthHex% [
    "3a09887a79881a79885a018872898832f18852f1881281881c29885c5988",
    "3c59887c218854a98814d18874d18834a18850a98810d18870d18830a188",
    "1821885851883851887829882328b96ba8b96fa8b92720b923b8b96b30b9",
    "6f30b927b0b960b8b92830b92c30b964b0b96020b928a0b92ca0b96428b9",
    "7688b93e00b93a00b97280b97610b93e90b93a90b97218b93510b97d90b9",
    "7990b93118b93580b97d08b97908b93188b95c88b91400b91000b95880b9",
    "5c10b91490b91090b95818b91f10b95790b95390b91b18b91f80b95708b9",
    "5308b91b88b90920b941a0b945a0b90d28b909b0b94138b94538b90db8b9",
    "4ab0b90238b90638b94eb8b94a28b902a8b906a8b94e20b94b08d44b88d4",
    "0788d40700d44b98d44b10d40710d40790d40998d40910d44510d44590d4",
    "0900d40980d44580d44508d44ba8d44b20d40720d407a0d44b30d44bb0d4",
    "07b0d40738d40930d409b0d445b0d44538d409a0d40928d44528d445a8d4",
    "1ea8d41e20d45220d452a0d41e30d41eb0d452b0d45238d45c30d45cb0d4",
    "10b0d41038d45ca0d45c28d41028d410a8d41e00d41e80d45280d45208d4",
    "1e90d41e18d45218d45298d45c90d45c18d41018d41098d45c08d45c88d4",
    "1088d41000d46d5dcb34edcb581dcb01a5cb140dcb4db5cb2145cb78f5cb",
    "143dcb4d85cb2175cb78c5cb6d65cb34d5cb5825cb019dcb7e3dcb2785cb",
    "4b75cb12c5cb0765cb5ed5cb3225cb6b9dcb0755cb5ee5cb3215cb6badcb",
    "7e05cb27bdcb4b4dcb12fdcb6b3dcb3285cb5e75cb07c5cb1265cb4bd5cb",
    "2725cb7e9dcb1255cb4be5cb2715cb7eadcb6b05cb32bdcb5e4dcb07fdcb",
    "7855cb21e5cb4d15cb14adcb0105cb58bdcb344dcb6dfdcb0135cb588dcb",
    "347dcb6dcdcb786dcb21ddcb4d2dcb1495cb7cf98a6c898a4c898a5cf18a",
    "34798a24018a04018a14718a30798a20018a00018a10718a78f18a68818a",
    "48818a58f98a7c598a6c218a4c218a5c518a34d18a24a18a04a18a14d98a",
    "30d18a20a18a00a18a10d98a78518a68298a48298a58598a03598a13218a",
    "33218a23518a4bd18a5ba18a7ba18a6bd98a"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock046InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock046InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock046OutputMaskData : ℕ :=
  sixthHex% [
    "9adf6df93446887d779ad65cdb4003c9eb28b8a219db4932a37323c09808",
    "b1d139a37a12e2ec4df04766810e57e2e57cd3ec46c1476db00e5cd3e577",
    "e3332880d803f19132e33a19ed4003acdf6d9ddf66ad0008ce4b28fe9446",
    "cf944d8e0b239c0219acdd779ddd7cdc4212ce49328fd65cbed6578e0939",
    "9ca139ac7e579d7e5cdce132ceea128f757cbe75778eaa199ca323dd3c4d",
    "ec3c46dce328bfa8088f7766be776dffe803a0321990ed77a1ed7ce07212",
    "f27932b3e65c82e657b23939a03003e1af6dd0af66e07008833b28b3e446",
    "82e44dc37b23a09323e10c4dd00c46e0d328839808b3476682476dc3d803",
    "d1d139e10e57d00e5c919132839a12c2057cf30577c3da192c0e8b1099ee",
    "5c91ee11468b0f05a042d2c50edac5324da04ad7b10700d44b08d4779fb1",
    "189c9a240bff6803ff25d49a2cae8b6179ee2d71ee11e68b7ee5a04272c5",
    "0e7ac543ada03b37b107a0d44ba8d4067fb1183c9a55ebff19e3ff25749a",
    "5defb11038d45c30d460a7b10fa49a3333ff7f3bff32ec9a4a768b76e1ee",
    "3ae9ee773e8b697da024aac568a2c55435a02c0fb11098d45c90d41147b1",
    "0f049a42d3ff0edbff324c9a4ad68b0701ee4b09ee779e8b189da0240ac5",
    "6802c525d5a02b74fa7c01851e3cfa3809854da8b46b9dcb09a0b45ed5cb",
    "6e039f4836e02a0b9f7d7ee0799fd12eeaae4cd7d16ae2ae2790b401a5cb",
    "6398b434edcb300cfa6779850544fa23718513a7d144d2ae26efd100daae",
    "757b9f534ee031739f6606e023d18505e4fa67d98530acfa344dcb6338b4",
    "0105cb2730b417e6e040939f22aee0049b9f713aae570fd13532ae6247d1",
    "5e75cb0900b46b3dcb4d08b438a9851e9cfa7ca1852bd4fa1b02ae3d37d1",
    "5f0aae087fd10c9ee05beb9f39d6e01fe39fcc721bf84321fc0a1bb97b21",
    "8ded75c89c4fccd575f8e44fbced7ef99c44fdd57ec9e4448c3210b8032a",
    "bc4a10f93b2accd21b89a3218dea1bb9db21fc0d75c83c4fcc757589044f",
    "cd0d7ef93c44fd757eb804448c9210c9e32acdaa10f99b2a810001c4713b",
    "c03801f4093bb1df6f85ee5581a76fc4d655"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock046OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock046OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock046InputNumeratorData : ℕ :=
  sixthHex% [
    "86185f85f7df7df7e17e18617e186186185f86185f85f7df7e186186185f",
    "85f7df7df7e186185f85f7df85f7df7df7e186185f85f7df7df7e17e1861",
    "85f7df7df7e185f8618617e18617e17e17df8617e17e17df7e17df7df85f",
    "8617e17e17df7e17df7df85f7e17df7df85f7df85f85f8617e186186185f",
    "86185f85f7df7df7e17e18617e186186185f86185f85f7df85f7df7df7e1",
    "7e186186185f86185f85f7df85f7df7df7e17df7e17e18617df7e17e1861",
    "7e186186185f86185f85f7df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock046InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock046InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock046OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f8617df85f85f8617df85f8617e185f8617e17df7df85f7df85f85f861",
    "7df85f85f86185f8618617e18617e17e17df7e17df7df85f7e17df7df85f",
    "7df85f85f86185f7df7df7e186185f85f7df86185f85f7df7e186186185f",
    "7df7e17e186185f7df7df7e185f7df7df7e186185f85f7df7e17df8617e1",
    "8617e185f8618617e185f86185f8617df85f8617e185f86185f8617df85f",
    "85f8617df85f7df85f7e17df85f7df86185f7df7e185f7df7df7e185f7df",
    "7e18617df7e186185f7e1861"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock046OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock046OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block046_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock046Input a) =
      generatedSixthXiShortBlock046InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock046Output a) =
      generatedSixthXiShortBlock046OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock046Input a) =
      generatedSixthXiShortBlock046InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock046Output a) =
      generatedSixthXiShortBlock046OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block046_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock046InputMask a) =
      generatedSixthXiShortBlock046OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock046InputMask a)) *
      generatedSixthXiShortBlock046InputNumerator a =
        generatedSixthXiShortBlock046OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block046_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock046Input a
    let y := generatedSixthXiShortBlock046Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block046_cache a
  have hs := generatedSixth_xi_short_block046_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block046_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock046Input a
    let y := generatedSixthXiShortBlock046Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block046_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block046_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock046Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block046_certificate a).1
    (generatedSixth_xi_short_block046_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
