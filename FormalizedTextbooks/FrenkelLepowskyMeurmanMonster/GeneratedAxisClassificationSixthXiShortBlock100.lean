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
def generatedSixthXiShortBlock100Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (267, 16)),
    Sum.inr (Sum.inr (267, 17)),
    Sum.inr (Sum.inr (256, 6)),
    Sum.inr (Sum.inr (267, 19)),
    Sum.inr (Sum.inr (213, 12)),
    Sum.inr (Sum.inr (159, 2)),
    Sum.inr (Sum.inr (95, 22)),
    Sum.inr (Sum.inr (30, 8)),
    Sum.inr (Sum.inl (213, 51)),
    Sum.inr (Sum.inl (207, 19)),
    Sum.inr (Sum.inl (150, 52)),
    Sum.inr (Sum.inl (173, 17)),
    Sum.inr (Sum.inl (38, 49)),
    Sum.inr (Sum.inl (18, 61)),
    Sum.inr (Sum.inl (38, 57)),
    Sum.inr (Sum.inl (38, 59)),
    Sum.inr (Sum.inl (213, 44)),
    Sum.inr (Sum.inl (150, 20)),
    Sum.inr (Sum.inl (173, 51)),
    Sum.inr (Sum.inl (207, 50)),
    Sum.inr (Sum.inl (173, 49)),
    Sum.inr (Sum.inl (213, 18)),
    Sum.inr (Sum.inl (150, 60)),
    Sum.inr (Sum.inl (207, 45)),
    Sum.inr (Sum.inl (18, 29)),
    Sum.inr (Sum.inl (18, 45)),
    Sum.inr (Sum.inl (38, 51)),
    Sum.inr (Sum.inl (18, 13)),
    Sum.inr (Sum.inl (173, 19)),
    Sum.inr (Sum.inl (150, 28)),
    Sum.inr (Sum.inl (207, 12)),
    Sum.inr (Sum.inl (213, 13)),
    Sum.inr (Sum.inl (158, 59)),
    Sum.inr (Sum.inl (157, 33)),
    Sum.inr (Sum.inl (140, 3)),
    Sum.inr (Sum.inl (153, 35)),
    Sum.inr (Sum.inl (28, 1)),
    Sum.inr (Sum.inl (8, 49)),
    Sum.inr (Sum.inl (28, 9)),
    Sum.inr (Sum.inl (28, 11)),
    Sum.inr (Sum.inl (158, 20)),
    Sum.inr (Sum.inl (140, 44)),
    Sum.inr (Sum.inl (153, 1)),
    Sum.inr (Sum.inl (157, 3)),
    Sum.inr (Sum.inl (153, 33)),
    Sum.inr (Sum.inl (158, 0)),
    Sum.inr (Sum.inl (140, 17)),
    Sum.inr (Sum.inl (157, 62)),
    Sum.inr (Sum.inl (8, 17)),
    Sum.inr (Sum.inl (8, 33)),
    Sum.inr (Sum.inl (28, 3)),
    Sum.inr (Sum.inl (8, 1)),
    Sum.inr (Sum.inl (153, 3)),
    Sum.inr (Sum.inl (140, 62)),
    Sum.inr (Sum.inl (157, 28)),
    Sum.inr (Sum.inl (158, 47)),
    Sum.inr (Sum.inl (53, 47)),
    Sum.inr (Sum.inl (52, 48)),
    Sum.inr (Sum.inl (46, 17)),
    Sum.inr (Sum.inl (48, 52)),
    Sum.inr (Sum.inl (21, 32)),
    Sum.inr (Sum.inl (1, 56)),
    Sum.inr (Sum.inl (21, 40)),
    Sum.inr (Sum.inl (21, 42)),
    Sum.inr (Sum.inl (53, 62)),
    Sum.inr (Sum.inl (46, 0)),
    Sum.inr (Sum.inl (48, 36)),
    Sum.inr (Sum.inl (52, 16)),
    Sum.inr (Sum.inl (48, 48)),
    Sum.inr (Sum.inl (53, 46)),
    Sum.inr (Sum.inl (46, 1)),
    Sum.inr (Sum.inl (52, 17)),
    Sum.inr (Sum.inl (1, 24)),
    Sum.inr (Sum.inl (1, 40)),
    Sum.inr (Sum.inl (21, 34)),
    Sum.inr (Sum.inl (1, 8)),
    Sum.inr (Sum.inl (48, 32)),
    Sum.inr (Sum.inl (46, 16)),
    Sum.inr (Sum.inl (52, 49)),
    Sum.inr (Sum.inl (53, 63)),
    Sum.inr (Sum.inl (119, 33)),
    Sum.inr (Sum.inl (118, 59)),
    Sum.inr (Sum.inl (112, 31)),
    Sum.inr (Sum.inl (114, 0)),
    Sum.inr (Sum.inl (25, 16)),
    Sum.inr (Sum.inl (5, 52)),
    Sum.inr (Sum.inl (25, 24)),
    Sum.inr (Sum.inl (25, 26)),
    Sum.inr (Sum.inl (119, 48)),
    Sum.inr (Sum.inl (112, 13)),
    Sum.inr (Sum.inl (114, 16)),
    Sum.inr (Sum.inl (118, 36)),
    Sum.inr (Sum.inl (114, 18)),
    Sum.inr (Sum.inl (119, 14)),
    Sum.inr (Sum.inl (112, 34)),
    Sum.inr (Sum.inl (118, 12)),
    Sum.inr (Sum.inl (5, 20)),
    Sum.inr (Sum.inl (5, 36)),
    Sum.inr (Sum.inl (25, 18)),
    Sum.inr (Sum.inl (5, 4)),
    Sum.inr (Sum.inl (114, 2)),
    Sum.inr (Sum.inl (112, 48)),
    Sum.inr (Sum.inl (118, 19)),
    Sum.inr (Sum.inl (119, 31)),
    Sum.inr (Sum.inr (197, 23)),
    Sum.inr (Sum.inr (132, 15)),
    Sum.inr (Sum.inr (68, 2)),
    Sum.inr (Sum.inr (14, 10)),
    Sum.inr (Sum.inr (475, 6)),
    Sum.inr (Sum.inr (464, 5)),
    Sum.inr (Sum.inr (475, 4)),
    Sum.inr (Sum.inr (475, 18)),
    Sum.inr (Sum.inr (197, 13)),
    Sum.inr (Sum.inr (68, 9)),
    Sum.inr (Sum.inr (14, 3)),
    Sum.inr (Sum.inr (132, 22)),
    Sum.inr (Sum.inr (14, 20)),
    Sum.inr (Sum.inr (197, 8)),
    Sum.inr (Sum.inr (68, 14)),
    Sum.inr (Sum.inr (132, 1)),
    Sum.inr (Sum.inr (464, 16)),
    Sum.inr (Sum.inr (464, 17)),
    Sum.inr (Sum.inr (475, 7)),
    Sum.inr (Sum.inr (464, 19)),
    Sum.inr (Sum.inr (14, 12)),
    Sum.inr (Sum.inr (68, 21)),
    Sum.inr (Sum.inr (132, 11)),
    Sum.inr (Sum.inr (197, 0)),
    Sum.inr (Sum.inr (142, 13)),
    Sum.inr (Sum.inr (207, 22)),
    Sum.inr (Sum.inr (15, 9)),
    Sum.inr (Sum.inr (69, 3)),
    Sum.inr (Sum.inr (400, 6)),
    Sum.inr (Sum.inr (411, 5)),
    Sum.inr (Sum.inr (400, 4)),
    Sum.inr (Sum.inr (400, 18)),
    Sum.inr (Sum.inr (142, 23)),
    Sum.inr (Sum.inr (15, 2)),
    Sum.inr (Sum.inr (69, 10)),
    Sum.inr (Sum.inr (207, 15)),
    Sum.inr (Sum.inr (69, 12)),
    Sum.inr (Sum.inr (142, 0)),
    Sum.inr (Sum.inr (15, 21)),
    Sum.inr (Sum.inr (207, 11)),
    Sum.inr (Sum.inr (411, 16)),
    Sum.inr (Sum.inr (411, 17)),
    Sum.inr (Sum.inr (400, 7)),
    Sum.inr (Sum.inr (411, 19)),
    Sum.inr (Sum.inr (69, 20)),
    Sum.inr (Sum.inr (15, 14)),
    Sum.inr (Sum.inr (207, 1)),
    Sum.inr (Sum.inr (142, 8)),
    Sum.inr (Sum.inr (7, 8)),
    Sum.inr (Sum.inr (70, 1)),
    Sum.inr (Sum.inr (134, 14)),
    Sum.inr (Sum.inr (204, 20)),
    Sum.inr (Sum.inr (281, 6)),
    Sum.inr (Sum.inr (274, 5)),
    Sum.inr (Sum.inr (281, 4)),
    Sum.inr (Sum.inr (281, 18)),
    Sum.inr (Sum.inr (7, 0)),
    Sum.inr (Sum.inr (134, 21)),
    Sum.inr (Sum.inr (204, 12)),
    Sum.inr (Sum.inr (70, 11)),
    Sum.inr (Sum.inr (204, 10)),
    Sum.inr (Sum.inr (7, 23)),
    Sum.inr (Sum.inr (134, 2)),
    Sum.inr (Sum.inr (70, 15)),
    Sum.inr (Sum.inr (274, 16)),
    Sum.inr (Sum.inr (274, 17)),
    Sum.inr (Sum.inr (281, 7)),
    Sum.inr (Sum.inr (274, 19)),
    Sum.inr (Sum.inr (204, 3)),
    Sum.inr (Sum.inr (134, 9)),
    Sum.inr (Sum.inr (70, 22)),
    Sum.inr (Sum.inr (7, 13)),
    Sum.inr (Sum.inr (71, 0)),
    Sum.inr (Sum.inr (6, 11)),
    Sum.inr (Sum.inr (198, 21)),
    Sum.inr (Sum.inr (140, 12)),
    Sum.inr (Sum.inr (345, 6)),
    Sum.inr (Sum.inr (338, 5)),
    Sum.inr (Sum.inr (345, 4)),
    Sum.inr (Sum.inr (345, 18)),
    Sum.inr (Sum.inr (71, 8)),
    Sum.inr (Sum.inr (198, 14)),
    Sum.inr (Sum.inr (140, 20)),
    Sum.inr (Sum.inr (6, 1)),
    Sum.inr (Sum.inr (140, 3)),
    Sum.inr (Sum.inr (71, 13)),
    Sum.inr (Sum.inr (198, 9)),
    Sum.inr (Sum.inr (6, 22)),
    Sum.inr (Sum.inr (338, 16)),
    Sum.inr (Sum.inr (338, 17)),
    Sum.inr (Sum.inr (345, 7)),
    Sum.inr (Sum.inr (338, 19)),
    Sum.inr (Sum.inr (140, 10)),
    Sum.inr (Sum.inr (198, 2)),
    Sum.inr (Sum.inr (6, 15)),
    Sum.inr (Sum.inr (71, 23)),
    Sum.inr (Sum.inl (215, 24)),
    Sum.inr (Sum.inl (209, 40)),
    Sum.inr (Sum.inl (152, 6)),
    Sum.inr (Sum.inl (175, 26)),
    Sum.inr (Sum.inl (40, 8)),
    Sum.inr (Sum.inl (20, 50)),
    Sum.inr (Sum.inl (40, 2)),
    Sum.inr (Sum.inl (40, 0)),
    Sum.inr (Sum.inl (215, 9)),
    Sum.inr (Sum.inl (152, 22)),
    Sum.inr (Sum.inl (175, 10)),
    Sum.inr (Sum.inl (209, 9)),
    Sum.inr (Sum.inl (175, 8)),
    Sum.inr (Sum.inl (215, 25)),
    Sum.inr (Sum.inl (152, 2)),
    Sum.inr (Sum.inl (209, 8)),
    Sum.inr (Sum.inl (20, 18)),
    Sum.inr (Sum.inl (20, 34)),
    Sum.inr (Sum.inl (40, 10)),
    Sum.inr (Sum.inl (20, 2)),
    Sum.inr (Sum.inl (175, 24)),
    Sum.inr (Sum.inl (152, 18)),
    Sum.inr (Sum.inl (209, 41)),
    Sum.inr (Sum.inl (215, 8)),
    Sum.inr (Sum.inl (71, 43)),
    Sum.inr (Sum.inl (70, 27)),
    Sum.inr (Sum.inl (64, 42)),
    Sum.inr (Sum.inl (66, 6)),
    Sum.inr (Sum.inl (22, 25)),
    Sum.inr (Sum.inl (2, 55)),
    Sum.inr (Sum.inl (22, 19)),
    Sum.inr (Sum.inl (22, 17)),
    Sum.inr (Sum.inl (71, 58)),
    Sum.inr (Sum.inl (64, 10)),
    Sum.inr (Sum.inl (66, 22)),
    Sum.inr (Sum.inl (70, 58)),
    Sum.inr (Sum.inl (66, 14)),
    Sum.inr (Sum.inl (71, 4)),
    Sum.inr (Sum.inl (64, 11)),
    Sum.inr (Sum.inl (70, 37)),
    Sum.inr (Sum.inl (2, 23)),
    Sum.inr (Sum.inl (2, 39)),
    Sum.inr (Sum.inl (22, 27)),
    Sum.inr (Sum.inl (2, 7)),
    Sum.inr (Sum.inl (66, 30)),
    Sum.inr (Sum.inl (64, 43)),
    Sum.inr (Sum.inl (70, 4)),
    Sum.inr (Sum.inl (71, 21)),
    Sum.inr (Sum.inl (179, 25)),
    Sum.inr (Sum.inl (178, 57)),
    Sum.inr (Sum.inl (142, 39)),
    Sum.inr (Sum.inl (165, 24)),
    Sum.inr (Sum.inl (30, 39)),
    Sum.inr (Sum.inl (10, 9)),
    Sum.inr (Sum.inl (30, 45)),
    Sum.inr (Sum.inl (30, 47))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock100Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨25600 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock100InputMaskData : ℕ :=
  sixthHex% [
    "bcfee6b4f6e6b8f6e6f0f6e6c00ee6e006e6d00ee6b00ee6957ee5a376e5",
    "b876e5ce76e5a9bee5b7b6e590bee5cebee5b1dee59bd6e5a4d6e5ced6e5",
    "8deee58fe6e58ceee5ceeee582fee58af6e586f6e5cef6e5fe0ee5de06e5",
    "ee0ee58e0ee5c47ee4f276e4e976e49f76e4f8bee4e6b6e4c1bee49fbee4",
    "e0dee4cad6e4f5d6e49fd6e4dce6e4deeee4dde6e49fe6e4d3fee4dbf6e4",
    "d7f6e49ff6e4af06e48f0ee4bf06e4df06e4937ee3a576e3be76e3c876e3",
    "afb6e3b1bee396b6e3c8b6e3b7d6e39ddee3a2dee3c8dee38beee389e6e3",
    "8aeee3c8eee384fee38cf6e380f6e3c8f6e3f80ee3d806e3e80ee3880ee3",
    "c27ee2f476e2ef76e29976e2feb6e2e0bee2c7b6e299b6e2e6d6e2ccdee2",
    "f3dee299dee2dae6e2d8eee2dbe6e299e6e2d5fee2ddf6e2d1f6e299f6e2",
    "a906e2890ee2b906e2d906e2fc7ee1ca76e1d176e1a776e1c0b6e1debee1",
    "f9b6e1a7b6e1d8dee1f2d6e1cdd6e1a7d6e1e4eee1e6e6e1e5eee1a7eee1",
    "ebfee1e3f6e1eff6e1a7f6e19706e1b70ee18706e1e706e1ed76e0db7ee0",
    "c07ee0b67ee0d1bee0cfb6e0e8bee0b6bee0c9d6e0e3dee0dcdee0b6dee0",
    "f5eee0f7e6e0f4eee0b6eee0faf6e0f2fee0fefee0b6fee08606e0a60ee0",
    "9606e0f606e0de4e8fe8468ff34e8f854e8fe28e8ffc868fdb8e8f858e8f",
    "fae68fd0e68fefe68f85ee8fc6d68fc4d68fc7d68f85de8fc9c68fc1ce8f",
    "cdc68f85c68fb53e8f95368fa53e8fc53e8f8e468eb84e8ea3468ed5468e",
    "b2868eac8e8e8b868ed5868eaaee8e80ee8ebfee8ed5e68e96d68e94d68e",
    "97d68ed5de8e99ce8e91c68e9dce8ed5ce8ee53e8ec5368ef53e8e953e8e",
    "8e468db84e8da3468dd5468db2868dac8e8d8b868dd5868daae68d80e68d",
    "bfe68dd5ee8d96de8d94de8d97de8dd5d68d99ce8d91c68d9dce8dd5ce8d",
    "e53e8dc5368df53e8d953e8d9e468ca84e8cb3468cc5468ca2868cbc8e8c",
    "9b868cc5868cbae68c90e68cafe68cc5ee8c86d68c84d68c87d68cc5de8c",
    "89ce8c81c68c8dce8cc5ce8cf5368cd53e8ce5368c85368cb74e8b81468b",
    "9a4e8bec4e8b8b868b958e8bb2868bec868b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock100InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock100InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock100OutputMaskData : ℕ :=
  sixthHex% [
    "d0dc67445c64d4dcd3045c64deaa338e3996f30b91e798821eb9177eaa07",
    "a71802830ba37a7d46de7df0ea7d450a7d41402a059d1806103912890ba2",
    "832a069a0ba3fa9807a7b9129efdf50a7df69afd414a7df6908ba1c01804",
    "bd2a03a9b916202a13403903998b06bd98a744ee42e0eef4d4ee4134ee45",
    "7eb901a38b022eaa16b798a1a9b905b098a0d00b048d2a16a06ef134eef2",
    "a46e4574eef5ba18a2ea8b0797b900832a1a9b937ffb806f22326a0621cc",
    "eb57294f579f7b572a9b572ed1006a0c326981137d1821ca06006e1f21cb",
    "7fb26f22937a1bd79d8f579e1fd729cf579e15a1c945326c38006b2c937e",
    "a5007bc5136b1ca16e38b2c8d5c42d71c49b45c42ea5c42aef936e32a16d",
    "bf807926b2c92c936d35b2c855216c08007e254499b1c49a21442df1c49d",
    "3f32ca6fa16f12936806007ceb21e98b32f95280fc76935a9be5bf3fe509",
    "0be5bcebe5bfb5b2fb6880f8e5a1ec7c935c76b2f86f935d0f00f95221ec",
    "6b650bffe5086f65bfbfe50f7113582180fd5cb2fa4821e891b25df1a14d",
    "2813480c00eee1760b4576bd71760891760bcf214f12134c9f32580600ef",
    "18214b0100ee61934a3cb25811f6bf8576bc15f60bc576bc1f80eb4f134e",
    "32214926b255611e10010d07ccbf02e8aca405da41a1daf795da4275da41",
    "2b8d02e2bf016f9e12e2aca2e88d01e5aca3913f00d81e12f55af561daf1",
    "e55a4635daf1ef2ca6bfbf03c28d04d61e17323f12522c059f9e00bb8da6",
    "56fb43f2fbf5c6fb4026fb4378ac00b19e033cbf10b18da7afac04a28da6",
    "d61e059f3f10a67bf732fbf3b67b4466fbf4a80da3f89e0685ac01913f17",
    "888d92e89e85252c80013f26ec49c34849757c49c09c49c4d61e871f2c84",
    "920d971f3f20011e830c3f2178ac82318d901cc9778849730cc9c4dc4974",
    "12bf23422c863f1e812b8d959fac20ffbf37320d32161e94fb68715f68c7",
    "6b68728b6876c13f35080d36852c25081e95023f360f1e947b8d3732ac22",
    "0be8c59f68c11be876cb68c1119e96410d333c3f3428ac2b9486eef495f9",
    "3927fc1d345de442b840420e7442bb9442b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock100OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock100OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock100InputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock100InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock100InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock100OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f7e17e17df7df6df8e385f7e17e185f7e185f85f7e18617df96175d",
    "7df8617df7df85f7e17e17e185f86195f75d85f86185f8617df7e186185f",
    "85f7df95f75d86185f7df85f7df7e18617e17e17df6e18e385f8617e17df",
    "86185f86185f85f7df95f75d7df7e17df85f7df7e17df85f86185f95f75d",
    "85f8617df7e185f7df7df85f8617e195f75d86185f85f7df85f7df7df7e1",
    "86185f95f75d7e17df7df7e185f7df8617e18617e195f75d7df7e185f7df",
    "85f7df86185f7e17e16df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock100OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock100OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block100_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock100Input a) =
      generatedSixthXiShortBlock100InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock100Output a) =
      generatedSixthXiShortBlock100OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock100Input a) =
      generatedSixthXiShortBlock100InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock100Output a) =
      generatedSixthXiShortBlock100OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block100_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock100InputMask a) =
      generatedSixthXiShortBlock100OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock100InputMask a)) *
      generatedSixthXiShortBlock100InputNumerator a =
        generatedSixthXiShortBlock100OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block100_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock100Input a
    let y := generatedSixthXiShortBlock100Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block100_cache a
  have hs := generatedSixth_xi_short_block100_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block100_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock100Input a
    let y := generatedSixthXiShortBlock100Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block100_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block100_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock100Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block100_certificate a).1
    (generatedSixth_xi_short_block100_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
