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
def generatedSixthXiShortBlock085Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (15, 47)),
    Sum.inr (Sum.inl (15, 31)),
    Sum.inr (Sum.inl (35, 59)),
    Sum.inr (Sum.inl (15, 63)),
    Sum.inr (Sum.inl (170, 47)),
    Sum.inr (Sum.inl (147, 61)),
    Sum.inr (Sum.inl (204, 0)),
    Sum.inr (Sum.inl (210, 4)),
    Sum.inr (Sum.inr (185, 23)),
    Sum.inr (Sum.inr (248, 1)),
    Sum.inr (Sum.inr (56, 9)),
    Sum.inr (Sum.inr (114, 12)),
    Sum.inr (Sum.inr (423, 18)),
    Sum.inr (Sum.inr (428, 5)),
    Sum.inr (Sum.inr (423, 7)),
    Sum.inr (Sum.inr (423, 6)),
    Sum.inr (Sum.inr (185, 13)),
    Sum.inr (Sum.inr (56, 2)),
    Sum.inr (Sum.inr (114, 20)),
    Sum.inr (Sum.inr (248, 11)),
    Sum.inr (Sum.inr (114, 3)),
    Sum.inr (Sum.inr (185, 8)),
    Sum.inr (Sum.inr (56, 21)),
    Sum.inr (Sum.inr (248, 15)),
    Sum.inr (Sum.inr (428, 16)),
    Sum.inr (Sum.inr (428, 17)),
    Sum.inr (Sum.inr (423, 4)),
    Sum.inr (Sum.inr (428, 19)),
    Sum.inr (Sum.inr (114, 10)),
    Sum.inr (Sum.inr (56, 14)),
    Sum.inr (Sum.inr (248, 22)),
    Sum.inr (Sum.inr (185, 0)),
    Sum.inr (Sum.inr (120, 13)),
    Sum.inr (Sum.inr (57, 11)),
    Sum.inr (Sum.inr (249, 2)),
    Sum.inr (Sum.inr (179, 20)),
    Sum.inr (Sum.inr (358, 18)),
    Sum.inr (Sum.inr (365, 5)),
    Sum.inr (Sum.inr (358, 7)),
    Sum.inr (Sum.inr (358, 6)),
    Sum.inr (Sum.inr (120, 23)),
    Sum.inr (Sum.inr (249, 9)),
    Sum.inr (Sum.inr (179, 12)),
    Sum.inr (Sum.inr (57, 1)),
    Sum.inr (Sum.inr (179, 10)),
    Sum.inr (Sum.inr (120, 0)),
    Sum.inr (Sum.inr (249, 14)),
    Sum.inr (Sum.inr (57, 22)),
    Sum.inr (Sum.inr (365, 16)),
    Sum.inr (Sum.inr (365, 17)),
    Sum.inr (Sum.inr (358, 4)),
    Sum.inr (Sum.inr (365, 19)),
    Sum.inr (Sum.inr (179, 3)),
    Sum.inr (Sum.inr (249, 21)),
    Sum.inr (Sum.inr (57, 15)),
    Sum.inr (Sum.inr (120, 8)),
    Sum.inr (Sum.inr (49, 8)),
    Sum.inr (Sum.inr (112, 15)),
    Sum.inr (Sum.inr (176, 21)),
    Sum.inr (Sum.inr (250, 3)),
    Sum.inr (Sum.inr (303, 18)),
    Sum.inr (Sum.inr (292, 5)),
    Sum.inr (Sum.inr (303, 7)),
    Sum.inr (Sum.inr (303, 6)),
    Sum.inr (Sum.inr (49, 0)),
    Sum.inr (Sum.inr (176, 14)),
    Sum.inr (Sum.inr (250, 10)),
    Sum.inr (Sum.inr (112, 22)),
    Sum.inr (Sum.inr (250, 12)),
    Sum.inr (Sum.inr (49, 23)),
    Sum.inr (Sum.inr (176, 9)),
    Sum.inr (Sum.inr (112, 1)),
    Sum.inr (Sum.inr (292, 16)),
    Sum.inr (Sum.inr (292, 17)),
    Sum.inr (Sum.inr (303, 4)),
    Sum.inr (Sum.inr (292, 19)),
    Sum.inr (Sum.inr (250, 20)),
    Sum.inr (Sum.inr (176, 2)),
    Sum.inr (Sum.inr (112, 11)),
    Sum.inr (Sum.inr (49, 13)),
    Sum.inr (Sum.inr (251, 0)),
    Sum.inr (Sum.inr (186, 22)),
    Sum.inr (Sum.inr (122, 14)),
    Sum.inr (Sum.inr (48, 10)),
    Sum.inr (Sum.inr (485, 18)),
    Sum.inr (Sum.inr (494, 5)),
    Sum.inr (Sum.inr (485, 7)),
    Sum.inr (Sum.inr (485, 6)),
    Sum.inr (Sum.inr (251, 8)),
    Sum.inr (Sum.inr (122, 21)),
    Sum.inr (Sum.inr (48, 3)),
    Sum.inr (Sum.inr (186, 15)),
    Sum.inr (Sum.inr (48, 20)),
    Sum.inr (Sum.inr (251, 13)),
    Sum.inr (Sum.inr (122, 2)),
    Sum.inr (Sum.inr (186, 11)),
    Sum.inr (Sum.inr (494, 16)),
    Sum.inr (Sum.inr (494, 17)),
    Sum.inr (Sum.inr (485, 4)),
    Sum.inr (Sum.inr (494, 19)),
    Sum.inr (Sum.inr (48, 12)),
    Sum.inr (Sum.inr (122, 9)),
    Sum.inr (Sum.inr (186, 1)),
    Sum.inr (Sum.inr (251, 23)),
    Sum.inr (Sum.inl (211, 39)),
    Sum.inr (Sum.inl (205, 46)),
    Sum.inr (Sum.inl (148, 25)),
    Sum.inr (Sum.inl (171, 16)),
    Sum.inr (Sum.inl (36, 54)),
    Sum.inr (Sum.inl (16, 3)),
    Sum.inr (Sum.inl (36, 51)),
    Sum.inr (Sum.inl (36, 63)),
    Sum.inr (Sum.inl (211, 56)),
    Sum.inr (Sum.inl (148, 6)),
    Sum.inr (Sum.inl (171, 15)),
    Sum.inr (Sum.inl (205, 49)),
    Sum.inr (Sum.inl (171, 49)),
    Sum.inr (Sum.inl (211, 6)),
    Sum.inr (Sum.inl (148, 56)),
    Sum.inr (Sum.inl (205, 15)),
    Sum.inr (Sum.inl (16, 28)),
    Sum.inr (Sum.inl (16, 44)),
    Sum.inr (Sum.inl (36, 58)),
    Sum.inr (Sum.inl (16, 51)),
    Sum.inr (Sum.inl (171, 46)),
    Sum.inr (Sum.inl (148, 39)),
    Sum.inr (Sum.inl (205, 16)),
    Sum.inr (Sum.inl (211, 25)),
    Sum.inr (Sum.inl (214, 35)),
    Sum.inr (Sum.inl (208, 50)),
    Sum.inr (Sum.inl (151, 29)),
    Sum.inr (Sum.inl (174, 9)),
    Sum.inr (Sum.inl (39, 41)),
    Sum.inr (Sum.inl (19, 9)),
    Sum.inr (Sum.inl (39, 57)),
    Sum.inr (Sum.inl (39, 6)),
    Sum.inr (Sum.inl (214, 60)),
    Sum.inr (Sum.inl (151, 2)),
    Sum.inr (Sum.inl (174, 22)),
    Sum.inr (Sum.inl (208, 45)),
    Sum.inr (Sum.inl (174, 38)),
    Sum.inr (Sum.inl (214, 12)),
    Sum.inr (Sum.inl (151, 50)),
    Sum.inr (Sum.inl (208, 29)),
    Sum.inr (Sum.inl (19, 22)),
    Sum.inr (Sum.inl (19, 38)),
    Sum.inr (Sum.inl (39, 22)),
    Sum.inr (Sum.inl (19, 57)),
    Sum.inr (Sum.inl (174, 57)),
    Sum.inr (Sum.inl (151, 45)),
    Sum.inr (Sum.inl (208, 2)),
    Sum.inr (Sum.inl (214, 19)),
    Sum.inr (Sum.inl (212, 38)),
    Sum.inr (Sum.inl (206, 35)),
    Sum.inr (Sum.inl (149, 39)),
    Sum.inr (Sum.inl (172, 34)),
    Sum.inr (Sum.inl (37, 54)),
    Sum.inr (Sum.inl (17, 48)),
    Sum.inr (Sum.inl (37, 51)),
    Sum.inr (Sum.inl (37, 63)),
    Sum.inr (Sum.inl (212, 35)),
    Sum.inr (Sum.inl (149, 34)),
    Sum.inr (Sum.inl (172, 39)),
    Sum.inr (Sum.inl (206, 38)),
    Sum.inr (Sum.inl (172, 43)),
    Sum.inr (Sum.inl (212, 47)),
    Sum.inr (Sum.inl (149, 46)),
    Sum.inr (Sum.inl (206, 42)),
    Sum.inr (Sum.inl (17, 58)),
    Sum.inr (Sum.inl (17, 57)),
    Sum.inr (Sum.inl (37, 58)),
    Sum.inr (Sum.inl (17, 51)),
    Sum.inr (Sum.inl (172, 46)),
    Sum.inr (Sum.inl (149, 43)),
    Sum.inr (Sum.inl (206, 47)),
    Sum.inr (Sum.inl (212, 42)),
    Sum.inr (Sum.inl (188, 3)),
    Sum.inr (Sum.inl (187, 6)),
    Sum.inr (Sum.inl (143, 61)),
    Sum.inr (Sum.inl (166, 56)),
    Sum.inr (Sum.inl (31, 6)),
    Sum.inr (Sum.inl (11, 0)),
    Sum.inr (Sum.inl (31, 3)),
    Sum.inr (Sum.inl (31, 15)),
    Sum.inr (Sum.inl (188, 6)),
    Sum.inr (Sum.inl (143, 56)),
    Sum.inr (Sum.inl (166, 61)),
    Sum.inr (Sum.inl (187, 3)),
    Sum.inr (Sum.inl (166, 3)),
    Sum.inr (Sum.inl (188, 56)),
    Sum.inr (Sum.inl (143, 6)),
    Sum.inr (Sum.inl (187, 61)),
    Sum.inr (Sum.inl (11, 31)),
    Sum.inr (Sum.inl (11, 47)),
    Sum.inr (Sum.inl (31, 10)),
    Sum.inr (Sum.inl (11, 48)),
    Sum.inr (Sum.inl (166, 6)),
    Sum.inr (Sum.inl (143, 3)),
    Sum.inr (Sum.inl (187, 56)),
    Sum.inr (Sum.inl (188, 61)),
    Sum.inr (Sum.inr (510, 8)),
    Sum.inr (Sum.inr (447, 11)),
    Sum.inr (Sum.inr (383, 9)),
    Sum.inr (Sum.inr (309, 10)),
    Sum.inr (Sum.inr (224, 4)),
    Sum.inr (Sum.inr (235, 5)),
    Sum.inr (Sum.inr (224, 6)),
    Sum.inr (Sum.inr (224, 7)),
    Sum.inr (Sum.inr (510, 0)),
    Sum.inr (Sum.inr (383, 2)),
    Sum.inr (Sum.inr (309, 3)),
    Sum.inr (Sum.inr (447, 1)),
    Sum.inr (Sum.inr (309, 20)),
    Sum.inr (Sum.inr (510, 23)),
    Sum.inr (Sum.inr (383, 21)),
    Sum.inr (Sum.inr (447, 22)),
    Sum.inr (Sum.inr (235, 16)),
    Sum.inr (Sum.inr (235, 17)),
    Sum.inr (Sum.inr (224, 18)),
    Sum.inr (Sum.inr (235, 19)),
    Sum.inr (Sum.inr (309, 12)),
    Sum.inr (Sum.inr (383, 14)),
    Sum.inr (Sum.inr (447, 15)),
    Sum.inr (Sum.inr (510, 13)),
    Sum.inr (Sum.inr (500, 0)),
    Sum.inr (Sum.inr (437, 1)),
    Sum.inr (Sum.inr (373, 2)),
    Sum.inr (Sum.inr (319, 3)),
    Sum.inr (Sum.inr (234, 4)),
    Sum.inr (Sum.inr (225, 5)),
    Sum.inr (Sum.inr (234, 6)),
    Sum.inr (Sum.inr (234, 7)),
    Sum.inr (Sum.inr (500, 8)),
    Sum.inr (Sum.inr (373, 9)),
    Sum.inr (Sum.inr (319, 10)),
    Sum.inr (Sum.inr (437, 11)),
    Sum.inr (Sum.inr (319, 12)),
    Sum.inr (Sum.inr (500, 13)),
    Sum.inr (Sum.inr (373, 14)),
    Sum.inr (Sum.inr (437, 15)),
    Sum.inr (Sum.inr (225, 16)),
    Sum.inr (Sum.inr (225, 17)),
    Sum.inr (Sum.inr (234, 18)),
    Sum.inr (Sum.inr (225, 19)),
    Sum.inr (Sum.inr (319, 20)),
    Sum.inr (Sum.inr (373, 21)),
    Sum.inr (Sum.inr (437, 22)),
    Sum.inr (Sum.inr (500, 23)),
    Sum.inr (Sum.inr (508, 23)),
    Sum.inr (Sum.inr (445, 22)),
    Sum.inr (Sum.inr (381, 21)),
    Sum.inr (Sum.inr (311, 20)),
    Sum.inr (Sum.inr (226, 4)),
    Sum.inr (Sum.inr (233, 5)),
    Sum.inr (Sum.inr (226, 6)),
    Sum.inr (Sum.inr (226, 7))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock085Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨21760 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock085InputMaskData : ℕ :=
  sixthHex% [
    "df1446d71446db1c46931446a3e44683e446b3e446d3ec46e29445d49c45",
    "cf9c45b99c45de5445c05c45e75445b95445c63c45ec3c45d33445b93c45",
    "fa0c45f80c45fb0c45b90445f51c45fd1c45f11445b91c4589ec45a9ec45",
    "99ec45f9e445a29444949c448f9c44f99c449e5444805c44a75444f95444",
    "863c44ac3c44933444f93c44ba0444b80444bb0444f90c44b51c44bd1c44",
    "b11444f91c44c9e444e9e444d9e444b9ec44f19443c79c43dc9c43aa9c43",
    "cd5c43d35443f45c43aa5c43d53443ff3443c03c43aa3443e90c43eb0c43",
    "e80c43aa0443e61c43ee1c43e21443aa1c439aec43baec438aec43eae443",
    "b19442879c429c9c42ea9c428d5c42935442b45c42ea5c42953442bf3442",
    "803c42ea3442a90442ab0442a80442ea0c42a61c42ae1c42a21442ea1c42",
    "dae442fae442cae442aaec429b9c41ad9441b69441c09441a75441b95c41",
    "9e5441c05441bf3441953441aa3c41c03441830441810441820441c00c41",
    "8c1441841441881c41c01441f0ec41d0ec41e0ec4180e4419b9440ad9c40",
    "b69c40c09c40a75c40b954409e5c40c05c40bf3c40953c40aa3440c03c40",
    "830440810440820440c00c408c1c40841c40881440c01c40f0ec40d0ec40",
    "e0ec4080e4409b842fad8c2fb6842fc0842fa7442fb94c2f9e442fc0442f",
    "bf242f952c2faa242fc0242f83142f811c2f82142fc0142f8c042f84042f",
    "88042fc00c2ff0fc2fd0fc2fe0fc2f80f42fda8c2eec842ef78c2e818c2e",
    "e64c2ef8442edf4c2e814c2efe2c2ed4242eeb2c2e812c2ec2142ec01c2e",
    "c3142e81142ecd0c2ec50c2ec90c2e81042eb1fc2e91fc2ea1fc2ec1f42e",
    "ce8c2df8842de38c2d958c2df24c2dec442dcb4c2d954c2dea242dc02c2d",
    "ff242d95242dd61c2dd4142dd71c2d951c2dd90c2dd10c2ddd0c2d95042d",
    "a5fc2d85fc2db5fc2dd5f42dcf8c2cf9842ce28c2c948c2cf34c2ced442c",
    "ca4c2c944c2ceb242cc12c2cfe242c94242cd7142cd51c2cd6142c94142c",
    "d80c2cd00c2cdc0c2c94042ca4f42c84f42cb4f42cd4fc2ce28c2bd4842b",
    "cf8c2bb98c2bde442bc04c2be7442bb9442b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock085InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock085InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock085OutputMaskData : ℕ :=
  sixthHex% [
    "ca4b92c243928a0b998643928aacf78ee5cda876eda87fdcf577d4a376e5",
    "aeedc5fcacffe33b91b97b9ada3b91843b91b1dee58d4dc5c4dfd4fc0cff",
    "8deee5bd3cff9a75c5aee7d48c339a843b9acc7391c03b9accd4ffc89dc5",
    "ee0ee5ee07d483dfded5deefd845cf8a04f595939bcfd390ac939bf2939b",
    "c776effbe5cfb277de8aa4f58a06efbad4f59d9dcfa90fdefa9b90f29390",
    "badb9bb69390cb3cf5cf75cfe9e6efe9efde7964432f657222fe5270bf68",
    "1e680644280d2768067968064c8d72701e52398c43015f6801fd72312f68",
    "16665222f44300200d08280d4060064c280d40c768448e52621d72621443",
    "0fcc4959cd7854565806176268c00c32800751c00c0fc00c3a257806b658",
    "4f244977f76206157836c762118e58251c497688077e800736c80c3a8007",
    "472f6243665865f57865fc4949b4411fb570122e50406f6a2eb80474f80f",
    "17b80449b8040d1d70318e50781c4140cf6a312d7001ff6a26b650122441",
    "30f00f38f80f70b0047cf80f01576a051e50238d702384413b5c406d5d71",
    "60c65132876b5c500506100e6550053b50057ff5714366510af44032276b",
    "32857102576b251e51118c4042180e4a100e0258050e100e02ff6b06b651",
    "202571202c40a8fbfbfefaca8221ead060d0beb7bee4f7b587b7bed9b7be",
    "9d12cad0c1ea9953fbd0c0d0a122cae0b0d0b6b9eaf36bfba0ffb5a8f7b5",
    "91ffbe9db7b59158d09511eab382cab38bfbb888d1ee89e09252c0c013fa",
    "aec494f4849f97c494c9c4948d61e0c0b2c08920d1c0b3fac011e08183fa",
    "d78ac09258d1b08c9fb8849f818c948dc49ff06bfaf422c0d2b1e0d2b8d1",
    "a0f9e8f6f8d98a23f9d862c3b6b5adecf5a68fb5add1b5ade450d9a983f9",
    "e011e8a982c3a920d9e8b2c3bebbf9fb69e8a8fda6a0f5a699fdad95b5a6",
    "e81ac3ec53f9cac0d9cac9e8b4cac9e2cbf89e10d8cc51e2a2868cf8c687",
    "9b868cc5868cf063f8bdb0d8f422c9bdb1e2cc53f88dc1e2dbc8d89e1ac9",
    "bcce87b4c6878dce8c8186878d69e28920d8afb3f8afbac914386e42395f",
    "3ee27f6ca34573342b2974204a342b14342b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock085OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock085OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock085InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock085InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock085InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock085OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e185f85f7df7df6df8e385f7e17e185f7e185f85f7e18617df96175d",
    "7df8617df7df85f7e17e17e17e17df6e18e37e17df7e17df86185f7df7e1",
    "7e18616e18e37df7e18617e186185f7df85f85f86195f75d7e17df85f861",
    "7df7e17df7e185f7df95f75d7df7e17df85f7df7e17df85f86185f95f75d",
    "85f8617df7e185f7df7df85f8617e195f75d86185f85f7df85f7df7df7e1",
    "7df7e16e18e385f86186185f7e18617df85f8617e195f75d7df7e185f7df",
    "85f7df86185f85f85f96175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock085OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock085OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block085_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock085Input a) =
      generatedSixthXiShortBlock085InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock085Output a) =
      generatedSixthXiShortBlock085OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock085Input a) =
      generatedSixthXiShortBlock085InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock085Output a) =
      generatedSixthXiShortBlock085OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block085_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock085InputMask a) =
      generatedSixthXiShortBlock085OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock085InputMask a)) *
      generatedSixthXiShortBlock085InputNumerator a =
        generatedSixthXiShortBlock085OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block085_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock085Input a
    let y := generatedSixthXiShortBlock085Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block085_cache a
  have hs := generatedSixth_xi_short_block085_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block085_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock085Input a
    let y := generatedSixthXiShortBlock085Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block085_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block085_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock085Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block085_certificate a).1
    (generatedSixth_xi_short_block085_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
