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
def generatedSixthXiShortBlock084Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (133, 17)),
    Sum.inr (Sum.inl (132, 48)),
    Sum.inr (Sum.inl (126, 16)),
    Sum.inr (Sum.inl (128, 28)),
    Sum.inr (Sum.inl (26, 24)),
    Sum.inr (Sum.inl (6, 52)),
    Sum.inr (Sum.inl (26, 16)),
    Sum.inr (Sum.inl (26, 28)),
    Sum.inr (Sum.inl (133, 62)),
    Sum.inr (Sum.inl (126, 49)),
    Sum.inr (Sum.inl (128, 12)),
    Sum.inr (Sum.inl (132, 17)),
    Sum.inr (Sum.inl (128, 20)),
    Sum.inr (Sum.inl (133, 0)),
    Sum.inr (Sum.inl (126, 17)),
    Sum.inr (Sum.inl (132, 47)),
    Sum.inr (Sum.inl (6, 20)),
    Sum.inr (Sum.inl (6, 36)),
    Sum.inr (Sum.inl (26, 20)),
    Sum.inr (Sum.inl (6, 4)),
    Sum.inr (Sum.inl (128, 4)),
    Sum.inr (Sum.inl (126, 48)),
    Sum.inr (Sum.inl (132, 14)),
    Sum.inr (Sum.inl (133, 47)),
    Sum.inr (Sum.inl (88, 3)),
    Sum.inr (Sum.inl (87, 34)),
    Sum.inr (Sum.inl (81, 31)),
    Sum.inr (Sum.inl (83, 19)),
    Sum.inr (Sum.inl (23, 9)),
    Sum.inr (Sum.inl (3, 49)),
    Sum.inr (Sum.inl (23, 1)),
    Sum.inr (Sum.inl (23, 13)),
    Sum.inr (Sum.inl (88, 18)),
    Sum.inr (Sum.inl (81, 0)),
    Sum.inr (Sum.inl (83, 1)),
    Sum.inr (Sum.inl (87, 61)),
    Sum.inr (Sum.inl (83, 17)),
    Sum.inr (Sum.inl (88, 44)),
    Sum.inr (Sum.inl (81, 36)),
    Sum.inr (Sum.inl (87, 3)),
    Sum.inr (Sum.inl (3, 17)),
    Sum.inr (Sum.inl (3, 33)),
    Sum.inr (Sum.inl (23, 5)),
    Sum.inr (Sum.inl (3, 1)),
    Sum.inr (Sum.inl (83, 3)),
    Sum.inr (Sum.inl (81, 59)),
    Sum.inr (Sum.inl (87, 28)),
    Sum.inr (Sum.inl (88, 61)),
    Sum.inr (Sum.inl (196, 16)),
    Sum.inr (Sum.inl (195, 16)),
    Sum.inr (Sum.inl (144, 18)),
    Sum.inr (Sum.inl (167, 0)),
    Sum.inr (Sum.inl (32, 40)),
    Sum.inr (Sum.inl (12, 56)),
    Sum.inr (Sum.inl (32, 32)),
    Sum.inr (Sum.inl (32, 44)),
    Sum.inr (Sum.inl (196, 1)),
    Sum.inr (Sum.inl (144, 50)),
    Sum.inr (Sum.inl (167, 34)),
    Sum.inr (Sum.inl (195, 48)),
    Sum.inr (Sum.inl (167, 32)),
    Sum.inr (Sum.inl (196, 46)),
    Sum.inr (Sum.inl (144, 48)),
    Sum.inr (Sum.inl (195, 24)),
    Sum.inr (Sum.inl (12, 24)),
    Sum.inr (Sum.inl (12, 40)),
    Sum.inr (Sum.inl (32, 36)),
    Sum.inr (Sum.inl (12, 8)),
    Sum.inr (Sum.inl (167, 2)),
    Sum.inr (Sum.inl (144, 16)),
    Sum.inr (Sum.inl (195, 56)),
    Sum.inr (Sum.inl (196, 63)),
    Sum.inr (Sum.inr (240, 0)),
    Sum.inr (Sum.inr (177, 22)),
    Sum.inr (Sum.inr (113, 14)),
    Sum.inr (Sum.inr (59, 10)),
    Sum.inr (Sum.inr (494, 18)),
    Sum.inr (Sum.inr (485, 5)),
    Sum.inr (Sum.inr (494, 7)),
    Sum.inr (Sum.inr (494, 6)),
    Sum.inr (Sum.inr (240, 8)),
    Sum.inr (Sum.inr (113, 21)),
    Sum.inr (Sum.inr (59, 3)),
    Sum.inr (Sum.inr (177, 15)),
    Sum.inr (Sum.inr (59, 20)),
    Sum.inr (Sum.inr (240, 13)),
    Sum.inr (Sum.inr (113, 2)),
    Sum.inr (Sum.inr (177, 11)),
    Sum.inr (Sum.inr (485, 16)),
    Sum.inr (Sum.inr (485, 17)),
    Sum.inr (Sum.inr (494, 4)),
    Sum.inr (Sum.inr (485, 19)),
    Sum.inr (Sum.inr (59, 12)),
    Sum.inr (Sum.inr (113, 9)),
    Sum.inr (Sum.inr (177, 1)),
    Sum.inr (Sum.inr (240, 23)),
    Sum.inr (Sum.inr (58, 8)),
    Sum.inr (Sum.inr (123, 15)),
    Sum.inr (Sum.inr (187, 21)),
    Sum.inr (Sum.inr (241, 3)),
    Sum.inr (Sum.inr (292, 18)),
    Sum.inr (Sum.inr (303, 5)),
    Sum.inr (Sum.inr (292, 7)),
    Sum.inr (Sum.inr (292, 6)),
    Sum.inr (Sum.inr (58, 0)),
    Sum.inr (Sum.inr (187, 14)),
    Sum.inr (Sum.inr (241, 10)),
    Sum.inr (Sum.inr (123, 22)),
    Sum.inr (Sum.inr (241, 12)),
    Sum.inr (Sum.inr (58, 23)),
    Sum.inr (Sum.inr (187, 9)),
    Sum.inr (Sum.inr (123, 1)),
    Sum.inr (Sum.inr (303, 16)),
    Sum.inr (Sum.inr (303, 17)),
    Sum.inr (Sum.inr (292, 4)),
    Sum.inr (Sum.inr (303, 19)),
    Sum.inr (Sum.inr (241, 20)),
    Sum.inr (Sum.inr (187, 2)),
    Sum.inr (Sum.inr (123, 11)),
    Sum.inr (Sum.inr (58, 13)),
    Sum.inr (Sum.inr (115, 13)),
    Sum.inr (Sum.inr (50, 11)),
    Sum.inr (Sum.inr (242, 2)),
    Sum.inr (Sum.inr (184, 20)),
    Sum.inr (Sum.inr (365, 18)),
    Sum.inr (Sum.inr (358, 5)),
    Sum.inr (Sum.inr (365, 7)),
    Sum.inr (Sum.inr (365, 6)),
    Sum.inr (Sum.inr (115, 23)),
    Sum.inr (Sum.inr (242, 9)),
    Sum.inr (Sum.inr (184, 12)),
    Sum.inr (Sum.inr (50, 1)),
    Sum.inr (Sum.inr (184, 10)),
    Sum.inr (Sum.inr (115, 0)),
    Sum.inr (Sum.inr (242, 14)),
    Sum.inr (Sum.inr (50, 22)),
    Sum.inr (Sum.inr (358, 16)),
    Sum.inr (Sum.inr (358, 17)),
    Sum.inr (Sum.inr (365, 4)),
    Sum.inr (Sum.inr (358, 19)),
    Sum.inr (Sum.inr (184, 3)),
    Sum.inr (Sum.inr (242, 21)),
    Sum.inr (Sum.inr (50, 15)),
    Sum.inr (Sum.inr (115, 8)),
    Sum.inr (Sum.inr (178, 23)),
    Sum.inr (Sum.inr (243, 1)),
    Sum.inr (Sum.inr (51, 9)),
    Sum.inr (Sum.inr (121, 12)),
    Sum.inr (Sum.inr (428, 18)),
    Sum.inr (Sum.inr (423, 5)),
    Sum.inr (Sum.inr (428, 7)),
    Sum.inr (Sum.inr (428, 6)),
    Sum.inr (Sum.inr (178, 13)),
    Sum.inr (Sum.inr (51, 2)),
    Sum.inr (Sum.inr (121, 20)),
    Sum.inr (Sum.inr (243, 11)),
    Sum.inr (Sum.inr (121, 3)),
    Sum.inr (Sum.inr (178, 8)),
    Sum.inr (Sum.inr (51, 21)),
    Sum.inr (Sum.inr (243, 15)),
    Sum.inr (Sum.inr (423, 16)),
    Sum.inr (Sum.inr (423, 17)),
    Sum.inr (Sum.inr (428, 4)),
    Sum.inr (Sum.inr (423, 19)),
    Sum.inr (Sum.inr (121, 10)),
    Sum.inr (Sum.inr (51, 14)),
    Sum.inr (Sum.inr (243, 22)),
    Sum.inr (Sum.inr (178, 0)),
    Sum.inr (Sum.inl (196, 28)),
    Sum.inr (Sum.inl (195, 19)),
    Sum.inr (Sum.inl (144, 30)),
    Sum.inr (Sum.inl (167, 12)),
    Sum.inr (Sum.inl (32, 38)),
    Sum.inr (Sum.inl (12, 10)),
    Sum.inr (Sum.inl (32, 46)),
    Sum.inr (Sum.inl (32, 34)),
    Sum.inr (Sum.inl (196, 13)),
    Sum.inr (Sum.inl (144, 62)),
    Sum.inr (Sum.inl (167, 46)),
    Sum.inr (Sum.inl (195, 51)),
    Sum.inr (Sum.inl (167, 44)),
    Sum.inr (Sum.inl (196, 34)),
    Sum.inr (Sum.inl (144, 60)),
    Sum.inr (Sum.inl (195, 27)),
    Sum.inr (Sum.inl (12, 42)),
    Sum.inr (Sum.inl (12, 26)),
    Sum.inr (Sum.inl (32, 42)),
    Sum.inr (Sum.inl (12, 58)),
    Sum.inr (Sum.inl (167, 14)),
    Sum.inr (Sum.inl (144, 28)),
    Sum.inr (Sum.inl (195, 59)),
    Sum.inr (Sum.inl (196, 51)),
    Sum.inr (Sum.inl (88, 15)),
    Sum.inr (Sum.inl (87, 46)),
    Sum.inr (Sum.inl (81, 28)),
    Sum.inr (Sum.inl (83, 31)),
    Sum.inr (Sum.inl (23, 7)),
    Sum.inr (Sum.inl (3, 3)),
    Sum.inr (Sum.inl (23, 15)),
    Sum.inr (Sum.inl (23, 3)),
    Sum.inr (Sum.inl (88, 30)),
    Sum.inr (Sum.inl (81, 3)),
    Sum.inr (Sum.inl (83, 13)),
    Sum.inr (Sum.inl (87, 49)),
    Sum.inr (Sum.inl (83, 29)),
    Sum.inr (Sum.inl (88, 32)),
    Sum.inr (Sum.inl (81, 39)),
    Sum.inr (Sum.inl (87, 15)),
    Sum.inr (Sum.inl (3, 35)),
    Sum.inr (Sum.inl (3, 19)),
    Sum.inr (Sum.inl (23, 11)),
    Sum.inr (Sum.inl (3, 51)),
    Sum.inr (Sum.inl (83, 15)),
    Sum.inr (Sum.inl (81, 56)),
    Sum.inr (Sum.inl (87, 16)),
    Sum.inr (Sum.inl (88, 49)),
    Sum.inr (Sum.inl (133, 29)),
    Sum.inr (Sum.inl (132, 60)),
    Sum.inr (Sum.inl (126, 28)),
    Sum.inr (Sum.inl (128, 31)),
    Sum.inr (Sum.inl (26, 22)),
    Sum.inr (Sum.inl (6, 6)),
    Sum.inr (Sum.inl (26, 30)),
    Sum.inr (Sum.inl (26, 18)),
    Sum.inr (Sum.inl (133, 50)),
    Sum.inr (Sum.inl (126, 61)),
    Sum.inr (Sum.inl (128, 15)),
    Sum.inr (Sum.inl (132, 29)),
    Sum.inr (Sum.inl (128, 23)),
    Sum.inr (Sum.inl (133, 12)),
    Sum.inr (Sum.inl (126, 29)),
    Sum.inr (Sum.inl (132, 35)),
    Sum.inr (Sum.inl (6, 38)),
    Sum.inr (Sum.inl (6, 22)),
    Sum.inr (Sum.inl (26, 26)),
    Sum.inr (Sum.inl (6, 54)),
    Sum.inr (Sum.inl (128, 7)),
    Sum.inr (Sum.inl (126, 60)),
    Sum.inr (Sum.inl (132, 2)),
    Sum.inr (Sum.inl (133, 35)),
    Sum.inr (Sum.inl (210, 16)),
    Sum.inr (Sum.inl (204, 31)),
    Sum.inr (Sum.inl (147, 63)),
    Sum.inr (Sum.inl (170, 45)),
    Sum.inr (Sum.inl (35, 55)),
    Sum.inr (Sum.inl (15, 15)),
    Sum.inr (Sum.inl (35, 63)),
    Sum.inr (Sum.inl (35, 51)),
    Sum.inr (Sum.inl (210, 63)),
    Sum.inr (Sum.inl (147, 45)),
    Sum.inr (Sum.inl (170, 61)),
    Sum.inr (Sum.inl (204, 61)),
    Sum.inr (Sum.inl (170, 63)),
    Sum.inr (Sum.inl (210, 43)),
    Sum.inr (Sum.inl (147, 47)),
    Sum.inr (Sum.inl (204, 34))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock084Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨21504 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock084InputMaskData : ℕ :=
  sixthHex% [
    "c62c2bec242bd32c2bb92c2bfa1c2bf8142bfb1c2bb91c2bf50c2bfd0c2b",
    "f10c2bb9042b89fc2ba9fc2b99fc2bf9f42be38c2ad5842ace8c2ab88c2a",
    "df442ac14c2ae6442ab8442ac72c2aed242ad22c2ab82c2afb142af91c2a",
    "fa142ab8142af40c2afc0c2af00c2ab8042a88f42aa8f42a98f42af8fc2a",
    "f78c29c18429da8c29ac8c29cb4429d54c29f24429ac4429d32429f92c29",
    "c62429ac2429ef1c29ed1429ee1c29ac1c29e00c29e80c29e40c29ac0429",
    "9cf429bcf4298cf429ecfc29b68428808c289b8428ed84288a4c28944428",
    "b34c28ed4c28922c28b82428872c28ed2c28ae1c28ac1428af1c28ed1c28",
    "a10428a90428a50428ed0c28ddf428fdf428cdf428adfc28f68427c08c27",
    "db8427ad8427ca4c27d44427f34c27ad4c27d22c27f82427c72c27ad2c27",
    "ee1c27ec1427ef1c27ad1c27e10c27e90c27e50c27ad04279dfc27bdfc27",
    "8dfc27edf427f78426c18c26da8426ac8426cb4c26d54426f24c26ac4c26",
    "d32c26f92426c62c26ac2c26ef1426ed1c26ee1426ac1426e00c26e80c26",
    "e40c26ac04269cf426bcf4268cf426ecfc26e38425d58c25ce8425b88425",
    "df4c25c14425e64c25b84c25c72425ed2c25d22425b82425fb1c25f91425",
    "fa1c25b81c25f40c25fc0c25f00c25b8042588f425a8f42598f425f8fc25",
    "a28c249484248f8c24f98c249e4424804c24a74424f94424862c24ac2424",
    "932c24f92c24ba1c24b81424bb1c24f91c24b50424bd0424b10424f90c24",
    "c9f424e9f424d9f424b9fc24cf8423f98c23e28423948423f34423ed4c23",
    "ca4423944423eb2c23c12423fe2c23942c23d71c23d51423d61c23941c23",
    "d80c23d00c23dc0c23940423a4f42384f423b4f423d4fc238e8c22b88422",
    "a38c22d58c22b24c22ac44228b4c22d54c22aa2422802c22bf2422d52422",
    "961c22941422971c22d51c229904229104229d0422d50c22e5f422c5f422",
    "f5f42295fc229a8c21ac8421b78c21c18c21a64c21b844219f4c21c14c21",
    "be2c21942421ab2c21c12c21821421801c21831421c114218d0421850421",
    "890421c10c21f1f421d1f421e1f42181fc21"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock084InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock084InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock084OutputMaskData : ℕ :=
  sixthHex% [
    "21d15f6c027f25906e6c03451de15f5c73450a7a7f4fa86e1c3c20143420",
    "2d3c2b2174205cdb4558927f7e015f7e086e000b4f560a7e2ad15e789064",
    "67070a3d47015e070a00070a35e27e78315e31a34f78306478927e390064",
    "6f095e2adb4f080f01000701390f0a35470139a8643de15e1b727e1b7b4f",
    "187a764e7b4732a06760e15d7f76332536384676331876335cd347110067",
    "58927611015d11a34750315d06386743ea76107e38187638217e332d3638",
    "21d95d259067030347030a7608095c5e086d22d34d7092776f0519354512",
    "5605190805194ca06d01734d48e15c01727770906d310277670b4d22d95c",
    "000d12080512310d193d451240ea7744a34d62306d62395cf882c2ae83f3",
    "d258d38019e99f8e87c5ce8ca68e87f88e87bc2bf3f1f8d3b86ac2f1f9e9",
    "801bf3c189e99780d3d252c281c68c89ce8cb0c687bc8e8cc121e9c568d3",
    "e3fbf3e3f2c2ecb1e3bab0d2c66bf2942ac88bbda6d1fdadb2bda6ecbda6",
    "a818d2e5cbf2ac59e3e5cac8e568d2a4fac8f2f3f2b721e395f5ad9dfdad",
    "a4f5a6a8bdada452c8a01bf28688d28681e3f4c0daa2c1ebde1acb8c5bf1",
    "93cc9fc98c94aacc9ff4cc9fc129eb8cfacbc568da8cfbf18c59ebcdcbf1",
    "9bc2cbde10da8d8494858c94bc849fb0cc94bc23f1b86acb9ef9eb9ef0da",
    "e4b3f0b2b2c1ce69e19c28db83bfb5d9ffbebabfb5e4bfb5d15ac19c89e1",
    "d51bf09c88dbed6ac1acf8dbfaf1e1bf23f09df7be95ffbeacf7b5a0bfbe",
    "dd10dbd959e1ffcac1ffc3f040015c16006d6adb4d389a77564d190c0d12",
    "6f4d19314d1904a86d497b4d00e95c497a7738986d790a772f034d6ad15c",
    "394512314d12084519040d1208e2770cab4d2a386d2a315c507276067347",
    "7aa86728e95d463e331c7e387f3e33213e3314db47590867109a7659095d",
    "59ab4718395d4e30670be276293638213e38183633147e3869d15d6d9867",
    "4b0b474b027648034f1e027e62d95e3098645e4f0a040f01674f0a394f0a",
    "7dea7e30395e79ab4f303864309a7e71086427015e62d34f314701394f01",
    "00470a0c0f0171a06475e95e537a7e53734f"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock084OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock084OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock084InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock084InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock084InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock084OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17df8617df7df7e17e17e185f6df8e37df8617e17e186186185f7e1",
    "85f85f96175d7e185f7df8617df7df85f85f7e185f6df8e38617df7e17e1",
    "8618617e185f7df85f6e18e386185f7e18617e18617df7e186185f95f75d",
    "7e17df7df7e185f7df8617e17df85f6e18e37df7e17e18617e186186185f",
    "7df7e16e18e37e17df86185f7e18618617e185f7e196175d7df86185f85f",
    "7df7df85f7e17e17e16df8e385f7e18617df8618617e17e185f7e196175d",
    "8617df85f85f7df7df7e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock084OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock084OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block084_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock084Input a) =
      generatedSixthXiShortBlock084InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock084Output a) =
      generatedSixthXiShortBlock084OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock084Input a) =
      generatedSixthXiShortBlock084InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock084Output a) =
      generatedSixthXiShortBlock084OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block084_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock084InputMask a) =
      generatedSixthXiShortBlock084OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock084InputMask a)) *
      generatedSixthXiShortBlock084InputNumerator a =
        generatedSixthXiShortBlock084OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block084_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock084Input a
    let y := generatedSixthXiShortBlock084Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block084_cache a
  have hs := generatedSixth_xi_short_block084_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block084_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock084Input a
    let y := generatedSixthXiShortBlock084Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block084_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block084_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock084Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block084_certificate a).1
    (generatedSixth_xi_short_block084_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
