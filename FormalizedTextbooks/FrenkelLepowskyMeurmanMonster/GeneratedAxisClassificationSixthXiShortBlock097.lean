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
def generatedSixthXiShortBlock097Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (6, 29)),
    Sum.inr (Sum.inl (6, 45)),
    Sum.inr (Sum.inl (26, 53)),
    Sum.inr (Sum.inl (6, 13)),
    Sum.inr (Sum.inl (128, 60)),
    Sum.inr (Sum.inl (126, 13)),
    Sum.inr (Sum.inl (132, 18)),
    Sum.inr (Sum.inl (133, 13)),
    Sum.inr (Sum.inr (249, 13)),
    Sum.inr (Sum.inr (184, 11)),
    Sum.inr (Sum.inr (120, 2)),
    Sum.inr (Sum.inr (50, 20)),
    Sum.inr (Sum.inr (487, 18)),
    Sum.inr (Sum.inr (492, 5)),
    Sum.inr (Sum.inr (487, 7)),
    Sum.inr (Sum.inr (487, 6)),
    Sum.inr (Sum.inr (249, 23)),
    Sum.inr (Sum.inr (120, 9)),
    Sum.inr (Sum.inr (50, 12)),
    Sum.inr (Sum.inr (184, 1)),
    Sum.inr (Sum.inr (50, 10)),
    Sum.inr (Sum.inr (249, 0)),
    Sum.inr (Sum.inr (120, 14)),
    Sum.inr (Sum.inr (184, 22)),
    Sum.inr (Sum.inr (492, 16)),
    Sum.inr (Sum.inr (492, 17)),
    Sum.inr (Sum.inr (487, 4)),
    Sum.inr (Sum.inr (492, 19)),
    Sum.inr (Sum.inr (50, 3)),
    Sum.inr (Sum.inr (120, 21)),
    Sum.inr (Sum.inr (184, 15)),
    Sum.inr (Sum.inr (249, 8)),
    Sum.inr (Sum.inr (56, 23)),
    Sum.inr (Sum.inr (121, 1)),
    Sum.inr (Sum.inr (185, 9)),
    Sum.inr (Sum.inr (243, 12)),
    Sum.inr (Sum.inr (294, 18)),
    Sum.inr (Sum.inr (301, 5)),
    Sum.inr (Sum.inr (294, 7)),
    Sum.inr (Sum.inr (294, 6)),
    Sum.inr (Sum.inr (56, 13)),
    Sum.inr (Sum.inr (185, 2)),
    Sum.inr (Sum.inr (243, 20)),
    Sum.inr (Sum.inr (121, 11)),
    Sum.inr (Sum.inr (243, 3)),
    Sum.inr (Sum.inr (56, 8)),
    Sum.inr (Sum.inr (185, 21)),
    Sum.inr (Sum.inr (121, 15)),
    Sum.inr (Sum.inr (301, 16)),
    Sum.inr (Sum.inr (301, 17)),
    Sum.inr (Sum.inr (294, 4)),
    Sum.inr (Sum.inr (301, 19)),
    Sum.inr (Sum.inr (243, 10)),
    Sum.inr (Sum.inr (185, 14)),
    Sum.inr (Sum.inr (121, 22)),
    Sum.inr (Sum.inr (56, 0)),
    Sum.inr (Sum.inr (122, 0)),
    Sum.inr (Sum.inr (59, 22)),
    Sum.inr (Sum.inr (251, 14)),
    Sum.inr (Sum.inr (177, 10)),
    Sum.inr (Sum.inr (356, 18)),
    Sum.inr (Sum.inr (367, 5)),
    Sum.inr (Sum.inr (356, 7)),
    Sum.inr (Sum.inr (356, 6)),
    Sum.inr (Sum.inr (122, 8)),
    Sum.inr (Sum.inr (251, 21)),
    Sum.inr (Sum.inr (177, 3)),
    Sum.inr (Sum.inr (59, 15)),
    Sum.inr (Sum.inr (177, 20)),
    Sum.inr (Sum.inr (122, 13)),
    Sum.inr (Sum.inr (251, 2)),
    Sum.inr (Sum.inr (59, 11)),
    Sum.inr (Sum.inr (367, 16)),
    Sum.inr (Sum.inr (367, 17)),
    Sum.inr (Sum.inr (356, 4)),
    Sum.inr (Sum.inr (367, 19)),
    Sum.inr (Sum.inr (177, 12)),
    Sum.inr (Sum.inr (251, 9)),
    Sum.inr (Sum.inr (59, 1)),
    Sum.inr (Sum.inr (122, 23)),
    Sum.inr (Sum.inr (176, 8)),
    Sum.inr (Sum.inr (241, 15)),
    Sum.inr (Sum.inr (49, 21)),
    Sum.inr (Sum.inr (123, 3)),
    Sum.inr (Sum.inr (430, 18)),
    Sum.inr (Sum.inr (421, 5)),
    Sum.inr (Sum.inr (430, 7)),
    Sum.inr (Sum.inr (430, 6)),
    Sum.inr (Sum.inr (176, 0)),
    Sum.inr (Sum.inr (49, 14)),
    Sum.inr (Sum.inr (123, 10)),
    Sum.inr (Sum.inr (241, 22)),
    Sum.inr (Sum.inr (123, 12)),
    Sum.inr (Sum.inr (176, 23)),
    Sum.inr (Sum.inr (49, 9)),
    Sum.inr (Sum.inr (241, 1)),
    Sum.inr (Sum.inr (421, 16)),
    Sum.inr (Sum.inr (421, 17)),
    Sum.inr (Sum.inr (430, 4)),
    Sum.inr (Sum.inr (421, 19)),
    Sum.inr (Sum.inr (123, 20)),
    Sum.inr (Sum.inr (49, 2)),
    Sum.inr (Sum.inr (241, 11)),
    Sum.inr (Sum.inr (176, 13)),
    Sum.inr (Sum.inl (214, 46)),
    Sum.inr (Sum.inl (208, 49)),
    Sum.inr (Sum.inl (151, 19)),
    Sum.inr (Sum.inl (174, 12)),
    Sum.inr (Sum.inl (39, 44)),
    Sum.inr (Sum.inl (19, 12)),
    Sum.inr (Sum.inl (39, 60)),
    Sum.inr (Sum.inl (39, 3)),
    Sum.inr (Sum.inl (214, 49)),
    Sum.inr (Sum.inl (151, 12)),
    Sum.inr (Sum.inl (174, 19)),
    Sum.inr (Sum.inl (208, 46)),
    Sum.inr (Sum.inl (174, 35)),
    Sum.inr (Sum.inl (214, 1)),
    Sum.inr (Sum.inl (151, 60)),
    Sum.inr (Sum.inl (208, 30)),
    Sum.inr (Sum.inl (19, 19)),
    Sum.inr (Sum.inl (19, 35)),
    Sum.inr (Sum.inl (39, 19)),
    Sum.inr (Sum.inl (19, 60)),
    Sum.inr (Sum.inl (174, 60)),
    Sum.inr (Sum.inl (151, 35)),
    Sum.inr (Sum.inl (208, 1)),
    Sum.inr (Sum.inl (214, 30)),
    Sum.inr (Sum.inl (211, 61)),
    Sum.inr (Sum.inl (205, 34)),
    Sum.inr (Sum.inl (148, 3)),
    Sum.inr (Sum.inl (171, 28)),
    Sum.inr (Sum.inl (36, 6)),
    Sum.inr (Sum.inl (16, 0)),
    Sum.inr (Sum.inl (36, 3)),
    Sum.inr (Sum.inl (36, 15)),
    Sum.inr (Sum.inl (211, 34)),
    Sum.inr (Sum.inl (148, 28)),
    Sum.inr (Sum.inl (171, 3)),
    Sum.inr (Sum.inl (205, 61)),
    Sum.inr (Sum.inl (171, 61)),
    Sum.inr (Sum.inl (211, 28)),
    Sum.inr (Sum.inl (148, 34)),
    Sum.inr (Sum.inl (205, 3)),
    Sum.inr (Sum.inl (16, 31)),
    Sum.inr (Sum.inl (16, 47)),
    Sum.inr (Sum.inl (36, 10)),
    Sum.inr (Sum.inl (16, 48)),
    Sum.inr (Sum.inl (171, 34)),
    Sum.inr (Sum.inl (148, 61)),
    Sum.inr (Sum.inl (205, 28)),
    Sum.inr (Sum.inl (211, 3)),
    Sum.inr (Sum.inl (188, 41)),
    Sum.inr (Sum.inl (187, 54)),
    Sum.inr (Sum.inl (143, 23)),
    Sum.inr (Sum.inl (166, 32)),
    Sum.inr (Sum.inl (31, 38)),
    Sum.inr (Sum.inl (11, 6)),
    Sum.inr (Sum.inl (31, 35)),
    Sum.inr (Sum.inl (31, 47)),
    Sum.inr (Sum.inl (188, 44)),
    Sum.inr (Sum.inl (143, 18)),
    Sum.inr (Sum.inl (166, 37)),
    Sum.inr (Sum.inl (187, 51)),
    Sum.inr (Sum.inl (166, 27)),
    Sum.inr (Sum.inl (188, 18)),
    Sum.inr (Sum.inl (143, 44)),
    Sum.inr (Sum.inl (187, 13)),
    Sum.inr (Sum.inl (11, 25)),
    Sum.inr (Sum.inl (11, 41)),
    Sum.inr (Sum.inl (31, 42)),
    Sum.inr (Sum.inl (11, 54)),
    Sum.inr (Sum.inl (166, 30)),
    Sum.inr (Sum.inl (143, 41)),
    Sum.inr (Sum.inl (187, 8)),
    Sum.inr (Sum.inl (188, 23)),
    Sum.inr (Sum.inl (212, 43)),
    Sum.inr (Sum.inl (206, 28)),
    Sum.inr (Sum.inl (149, 21)),
    Sum.inr (Sum.inl (172, 61)),
    Sum.inr (Sum.inl (37, 41)),
    Sum.inr (Sum.inl (17, 47)),
    Sum.inr (Sum.inl (37, 44)),
    Sum.inr (Sum.inl (37, 32)),
    Sum.inr (Sum.inl (212, 46)),
    Sum.inr (Sum.inl (149, 16)),
    Sum.inr (Sum.inl (172, 56)),
    Sum.inr (Sum.inl (206, 25)),
    Sum.inr (Sum.inl (172, 52)),
    Sum.inr (Sum.inl (212, 34)),
    Sum.inr (Sum.inl (149, 28)),
    Sum.inr (Sum.inl (206, 21)),
    Sum.inr (Sum.inl (17, 37)),
    Sum.inr (Sum.inl (17, 38)),
    Sum.inr (Sum.inl (37, 37)),
    Sum.inr (Sum.inl (17, 44)),
    Sum.inr (Sum.inl (172, 49)),
    Sum.inr (Sum.inl (149, 25)),
    Sum.inr (Sum.inl (206, 16)),
    Sum.inr (Sum.inl (212, 39)),
    Sum.inr (Sum.inr (373, 0)),
    Sum.inr (Sum.inr (308, 1)),
    Sum.inr (Sum.inr (500, 2)),
    Sum.inr (Sum.inr (446, 3)),
    Sum.inr (Sum.inr (107, 4)),
    Sum.inr (Sum.inr (96, 5)),
    Sum.inr (Sum.inr (107, 6)),
    Sum.inr (Sum.inr (107, 7)),
    Sum.inr (Sum.inr (373, 8)),
    Sum.inr (Sum.inr (500, 9)),
    Sum.inr (Sum.inr (446, 10)),
    Sum.inr (Sum.inr (308, 11)),
    Sum.inr (Sum.inr (446, 12)),
    Sum.inr (Sum.inr (373, 13)),
    Sum.inr (Sum.inr (500, 14)),
    Sum.inr (Sum.inr (308, 15)),
    Sum.inr (Sum.inr (96, 16)),
    Sum.inr (Sum.inr (96, 17)),
    Sum.inr (Sum.inr (107, 18)),
    Sum.inr (Sum.inr (96, 19)),
    Sum.inr (Sum.inr (446, 20)),
    Sum.inr (Sum.inr (500, 21)),
    Sum.inr (Sum.inr (308, 22)),
    Sum.inr (Sum.inr (373, 23)),
    Sum.inr (Sum.inr (383, 8)),
    Sum.inr (Sum.inr (318, 11)),
    Sum.inr (Sum.inr (510, 9)),
    Sum.inr (Sum.inr (436, 10)),
    Sum.inr (Sum.inr (97, 4)),
    Sum.inr (Sum.inr (106, 5)),
    Sum.inr (Sum.inr (97, 6)),
    Sum.inr (Sum.inr (97, 7)),
    Sum.inr (Sum.inr (383, 0)),
    Sum.inr (Sum.inr (510, 2)),
    Sum.inr (Sum.inr (436, 3)),
    Sum.inr (Sum.inr (318, 1)),
    Sum.inr (Sum.inr (436, 20)),
    Sum.inr (Sum.inr (383, 23)),
    Sum.inr (Sum.inr (510, 21)),
    Sum.inr (Sum.inr (318, 22)),
    Sum.inr (Sum.inr (106, 16)),
    Sum.inr (Sum.inr (106, 17)),
    Sum.inr (Sum.inr (97, 18)),
    Sum.inr (Sum.inr (106, 19)),
    Sum.inr (Sum.inr (436, 12)),
    Sum.inr (Sum.inr (510, 14)),
    Sum.inr (Sum.inr (318, 15)),
    Sum.inr (Sum.inr (383, 13)),
    Sum.inr (Sum.inr (380, 13)),
    Sum.inr (Sum.inr (317, 15)),
    Sum.inr (Sum.inr (509, 14)),
    Sum.inr (Sum.inr (439, 12)),
    Sum.inr (Sum.inr (98, 4)),
    Sum.inr (Sum.inr (105, 5)),
    Sum.inr (Sum.inr (98, 6)),
    Sum.inr (Sum.inr (98, 7))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock097Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨24832 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock097InputMaskData : ℕ :=
  sixthHex% [
    "9ff65697f6569bfe56d3f656e30e56c30656f30e56930e569f7655a97655",
    "b27e55c47655a3be55bdb6559abe55c4be55bbd65591de55aed655c4d655",
    "87ee5585ee5586e655c4ee5588f65580f6558cfe55c4f655f40e55d40655",
    "e40e55840e55cd7654fb7654e07e54967654f1be54efb654c8be5496be54",
    "e9d654c3de54fcd65496d654d5e654d7e654d4ee5496e654daf654d2f654",
    "defe5496f654a60654860e54b60654d60654b376538576539e7e53e87653",
    "8fb65391be53b6b653e8b65397de53bdd65382de53e8de53abee53a9ee53",
    "aae653e8ee53a4f653acf653a0fe53e8f653d80e53f80653c80e53a80e53",
    "e17652d77652cc7e52ba7652ddb652c3be52e4b652bab652c5de52efd652",
    "d0de52bade52f9e652fbe652f8ee52bae652f6f652fef652f2fe52baf652",
    "8a0652aa0e529a0652fa0652f67651c07651db7e51ad7651cab651d4be51",
    "f3b651adb651d2d651f8de51c7d651add651eeee51ecee51efe651adee51",
    "e1f651e9f651e5fe51adf6519d0651bd0e518d0651ed0651e47e50d27e50",
    "c97650bf7e50d8be50c6b650e1be50bfbe50c0de50ead650d5de50bfde50",
    "fcee50feee50fde650bfee50f3fe50fbfe50f7f650bffe508f0650af0e50",
    "9f0650ff0650d3fe3fe5fe3ffefe3f88f63fef363ff13e3fd6363f88363f",
    "f7563fdd563fe25e3f88563fcb6e3fc9663fca663f88663fc4763fcc763f",
    "c0763f887e3fb8863f988e3fa8863fc8863f80fe3eb6fe3eadfe3edbf63e",
    "bc363ea23e3e85363edb363ea4563e8e563eb15e3edb563e98663e9a6e3e",
    "996e3edb6e3e97763e9f763e93763edb7e3eeb8e3ecb863efb8e3e9b8e3e",
    "a9fe3d9ffe3d84fe3df2f63d95363d8b3e3dac363df2363d8d5e3da75e3d",
    "98563df25e3db16e3db3663db0663df2663dbe763db6763dba763df27e3d",
    "c28e3de2863dd28e3db28e3dbaf63c8cf63c97f63ce1fe3c863e3c98363c",
    "bf3e3ce13e3c9e563cb4563c8b5e3ce1563ca26e3ca0663ca3663ce1663c",
    "ad7e3ca57e3ca97e3ce1763cd18e3cf1863cc18e3ca18e3cbafe3b8cfe3b",
    "97fe3be1f63b863e3b98363bbf3e3be13e3b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock097InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock097InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock097OutputMaskData : ℕ :=
  sixthHex% [
    "d07182d879829031899c7982e1d6e794dfddc30cfdb245cce74dcfc00cfe",
    "bcd7de9fd6e480418ada0181b9418ae7418ad2a4fe9f77ded6e5cf9f76e4",
    "9fd4feaf06e4f90fdecd9dcfef4981e74181af098aa34181deeee4abe7de",
    "fc34fe8d7dcf83edc5a4acf4d877d4fb76eee4e180bea18bdde18083e180",
    "b604f4fbd7d4b245c5fbd6ee8a34f4bae6eeecefd4d87dc58be98b83e18b",
    "cba980c7e18bcb0eeebe07d4e9d4f4989dc5538c4974cd780816582b1762",
    "45c00c1f80077cc00c22c00c1725785af6581364495af7622b15781bc762",
    "4dce58795c495b88075380071bc80c1780076a2f621f265848f57839bc49",
    "372c43106d726cb6524fb7682160067b200d1860064660067385723e5652",
    "77c4433e57683ef5720e2768582e526cbc433f280d37200d7f680673200d",
    "7fcf680ac6525d15722c5c430814402f5571538e51708f6b1e580544180e",
    "2758057958053dfd71702e5139bc40702f6b708d71405f6b16565122c440",
    "00100e08180e4050054c180e40f76b35fe51622d7113644068f4414fb570",
    "336e50106f6a7eb80424f80f47b80419b8045d1d7010ce50595c4110cf6a",
    "612d7051ff6a07f65033644160f00f68f80f20b0042cf80f51576a245e50",
    "738d7002c441e882c0cfc3f1c258d1e159eb8f8e85d5ce8eb68e85e88e85",
    "ac2bf190b8d1d92ac0e1f9ebe15bf1a0c9eb8780d1c252c091c68e99ce8e",
    "a0c685ac8e8ed121eba428d1f3fbf182b2c09bb9eabcf8dbb163fb9262c1",
    "fcb5afa6f5a4c5b5af9bb5afdf10dbe383fbaa11ea92c2c1e320dba2b2c1",
    "85fbfbc029eae2fda4eaf5a4d3fdafdfb5a4d35ac1a653fbf180db80c9ea",
    "8bc8d8ac89e9a112c98213f3ecc49db68496d5c49d8bc49dbe21e982b2c9",
    "cb20d8f3f3f38211e9c383f3e4cac9a118d8f28c96fa8496c38c9dcfc496",
    "c32bf3b622c9e1f1e990b8d8fcb3f9dbf2c8d669e8f568d29bbfbcc1ffb7",
    "a2bfbcfcbfbcc95ac8f5c9e8bc5bf98488d2842ac8c5b8d2e2f1e8a723f9",
    "85f7b78dffb7b4f7bcb8bfb7c510d2b019e8e7cac89683f907db4f209a7e",
    "2d015e0e006411970a4bd70128970a76970a"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock097OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock097OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock097InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock097InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock097InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock097OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f7e185f7df8616df8e38617df8618617e185f85f85f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17e18616e18e37df7e18617e186185f7df85f",
    "85f86195f75d85f86185f8617df7e186185f85f7df95f75d7df7e17df85f",
    "7df7e17df85f7e17df6e18e385f8617e17df86185f86185f7df85f6e18e3",
    "7df7e17e18617e186186185f7df7e16e18e37e17df86185f7e18618617e1",
    "8617e195f75d7df7e185f7df85f7df86185f7df7e16e18e385f86186185f",
    "7e18617df85f7e185f6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock097OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock097OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block097_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock097Input a) =
      generatedSixthXiShortBlock097InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock097Output a) =
      generatedSixthXiShortBlock097OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock097Input a) =
      generatedSixthXiShortBlock097InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock097Output a) =
      generatedSixthXiShortBlock097OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block097_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock097InputMask a) =
      generatedSixthXiShortBlock097OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock097InputMask a)) *
      generatedSixthXiShortBlock097InputNumerator a =
        generatedSixthXiShortBlock097OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block097_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock097Input a
    let y := generatedSixthXiShortBlock097Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block097_cache a
  have hs := generatedSixth_xi_short_block097_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block097_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock097Input a
    let y := generatedSixthXiShortBlock097Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block097_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block097_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock097Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block097_certificate a).1
    (generatedSixth_xi_short_block097_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
