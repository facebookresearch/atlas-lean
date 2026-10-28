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
def generatedSixthXiShortBlock094Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (459, 16)),
    Sum.inr (Sum.inr (459, 17)),
    Sum.inr (Sum.inr (448, 6)),
    Sum.inr (Sum.inr (459, 19)),
    Sum.inr (Sum.inr (21, 12)),
    Sum.inr (Sum.inr (95, 2)),
    Sum.inr (Sum.inr (159, 22)),
    Sum.inr (Sum.inr (222, 8)),
    Sum.inr (Sum.inl (213, 49)),
    Sum.inr (Sum.inl (207, 15)),
    Sum.inr (Sum.inl (150, 35)),
    Sum.inr (Sum.inl (173, 47)),
    Sum.inr (Sum.inl (38, 15)),
    Sum.inr (Sum.inl (18, 3)),
    Sum.inr (Sum.inl (38, 7)),
    Sum.inr (Sum.inl (38, 5)),
    Sum.inr (Sum.inl (213, 46)),
    Sum.inr (Sum.inl (150, 3)),
    Sum.inr (Sum.inl (173, 13)),
    Sum.inr (Sum.inl (207, 46)),
    Sum.inr (Sum.inl (173, 15)),
    Sum.inr (Sum.inl (213, 16)),
    Sum.inr (Sum.inl (150, 43)),
    Sum.inr (Sum.inl (207, 49)),
    Sum.inr (Sum.inl (18, 35)),
    Sum.inr (Sum.inl (18, 19)),
    Sum.inr (Sum.inl (38, 13)),
    Sum.inr (Sum.inl (18, 51)),
    Sum.inr (Sum.inl (173, 45)),
    Sum.inr (Sum.inl (150, 11)),
    Sum.inr (Sum.inl (207, 16)),
    Sum.inr (Sum.inl (213, 15)),
    Sum.inr (Sum.inl (158, 19)),
    Sum.inr (Sum.inl (157, 44)),
    Sum.inr (Sum.inl (140, 14)),
    Sum.inr (Sum.inl (153, 12)),
    Sum.inr (Sum.inl (28, 49)),
    Sum.inr (Sum.inl (8, 61)),
    Sum.inr (Sum.inl (28, 57)),
    Sum.inr (Sum.inl (28, 59)),
    Sum.inr (Sum.inl (158, 60)),
    Sum.inr (Sum.inl (140, 33)),
    Sum.inr (Sum.inl (153, 46)),
    Sum.inr (Sum.inl (157, 14)),
    Sum.inr (Sum.inl (153, 14)),
    Sum.inr (Sum.inl (158, 40)),
    Sum.inr (Sum.inl (140, 28)),
    Sum.inr (Sum.inl (157, 51)),
    Sum.inr (Sum.inl (8, 29)),
    Sum.inr (Sum.inl (8, 45)),
    Sum.inr (Sum.inl (28, 51)),
    Sum.inr (Sum.inl (8, 13)),
    Sum.inr (Sum.inl (153, 44)),
    Sum.inr (Sum.inl (140, 51)),
    Sum.inr (Sum.inl (157, 17)),
    Sum.inr (Sum.inl (158, 7)),
    Sum.inr (Sum.inl (53, 48)),
    Sum.inr (Sum.inl (52, 1)),
    Sum.inr (Sum.inl (46, 32)),
    Sum.inr (Sum.inl (48, 28)),
    Sum.inr (Sum.inl (21, 16)),
    Sum.inr (Sum.inl (1, 52)),
    Sum.inr (Sum.inl (21, 24)),
    Sum.inr (Sum.inl (21, 26)),
    Sum.inr (Sum.inl (53, 33)),
    Sum.inr (Sum.inl (46, 49)),
    Sum.inr (Sum.inl (48, 12)),
    Sum.inr (Sum.inl (52, 33)),
    Sum.inr (Sum.inl (48, 24)),
    Sum.inr (Sum.inl (53, 49)),
    Sum.inr (Sum.inl (46, 48)),
    Sum.inr (Sum.inl (52, 32)),
    Sum.inr (Sum.inl (1, 20)),
    Sum.inr (Sum.inl (1, 36)),
    Sum.inr (Sum.inl (21, 18)),
    Sum.inr (Sum.inl (1, 4)),
    Sum.inr (Sum.inl (48, 8)),
    Sum.inr (Sum.inl (46, 33)),
    Sum.inr (Sum.inl (52, 0)),
    Sum.inr (Sum.inl (53, 32)),
    Sum.inr (Sum.inl (119, 35)),
    Sum.inr (Sum.inl (118, 44)),
    Sum.inr (Sum.inl (112, 51)),
    Sum.inr (Sum.inl (114, 62)),
    Sum.inr (Sum.inl (25, 46)),
    Sum.inr (Sum.inl (5, 10)),
    Sum.inr (Sum.inl (25, 38)),
    Sum.inr (Sum.inl (25, 36)),
    Sum.inr (Sum.inl (119, 50)),
    Sum.inr (Sum.inl (112, 33)),
    Sum.inr (Sum.inl (114, 46)),
    Sum.inr (Sum.inl (118, 51)),
    Sum.inr (Sum.inl (114, 44)),
    Sum.inr (Sum.inl (119, 12)),
    Sum.inr (Sum.inl (112, 14)),
    Sum.inr (Sum.inl (118, 27)),
    Sum.inr (Sum.inl (5, 42)),
    Sum.inr (Sum.inl (5, 26)),
    Sum.inr (Sum.inl (25, 44)),
    Sum.inr (Sum.inl (5, 58)),
    Sum.inr (Sum.inl (114, 60)),
    Sum.inr (Sum.inl (112, 28)),
    Sum.inr (Sum.inl (118, 4)),
    Sum.inr (Sum.inl (119, 29)),
    Sum.inr (Sum.inr (5, 23)),
    Sum.inr (Sum.inr (68, 15)),
    Sum.inr (Sum.inr (132, 2)),
    Sum.inr (Sum.inr (206, 10)),
    Sum.inr (Sum.inr (283, 6)),
    Sum.inr (Sum.inr (272, 5)),
    Sum.inr (Sum.inr (283, 4)),
    Sum.inr (Sum.inr (283, 18)),
    Sum.inr (Sum.inr (5, 13)),
    Sum.inr (Sum.inr (132, 9)),
    Sum.inr (Sum.inr (206, 3)),
    Sum.inr (Sum.inr (68, 22)),
    Sum.inr (Sum.inr (206, 20)),
    Sum.inr (Sum.inr (5, 8)),
    Sum.inr (Sum.inr (132, 14)),
    Sum.inr (Sum.inr (68, 1)),
    Sum.inr (Sum.inr (272, 16)),
    Sum.inr (Sum.inr (272, 17)),
    Sum.inr (Sum.inr (283, 7)),
    Sum.inr (Sum.inr (272, 19)),
    Sum.inr (Sum.inr (206, 12)),
    Sum.inr (Sum.inr (132, 21)),
    Sum.inr (Sum.inr (68, 11)),
    Sum.inr (Sum.inr (5, 0)),
    Sum.inr (Sum.inr (78, 13)),
    Sum.inr (Sum.inr (15, 22)),
    Sum.inr (Sum.inr (207, 9)),
    Sum.inr (Sum.inr (133, 3)),
    Sum.inr (Sum.inr (336, 6)),
    Sum.inr (Sum.inr (347, 5)),
    Sum.inr (Sum.inr (336, 4)),
    Sum.inr (Sum.inr (336, 18)),
    Sum.inr (Sum.inr (78, 23)),
    Sum.inr (Sum.inr (207, 2)),
    Sum.inr (Sum.inr (133, 10)),
    Sum.inr (Sum.inr (15, 15)),
    Sum.inr (Sum.inr (133, 12)),
    Sum.inr (Sum.inr (78, 0)),
    Sum.inr (Sum.inr (207, 21)),
    Sum.inr (Sum.inr (15, 11)),
    Sum.inr (Sum.inr (347, 16)),
    Sum.inr (Sum.inr (347, 17)),
    Sum.inr (Sum.inr (336, 7)),
    Sum.inr (Sum.inr (347, 19)),
    Sum.inr (Sum.inr (133, 20)),
    Sum.inr (Sum.inr (207, 14)),
    Sum.inr (Sum.inr (15, 1)),
    Sum.inr (Sum.inr (78, 8)),
    Sum.inr (Sum.inr (199, 8)),
    Sum.inr (Sum.inr (134, 1)),
    Sum.inr (Sum.inr (70, 14)),
    Sum.inr (Sum.inr (12, 20)),
    Sum.inr (Sum.inr (473, 6)),
    Sum.inr (Sum.inr (466, 5)),
    Sum.inr (Sum.inr (473, 4)),
    Sum.inr (Sum.inr (473, 18)),
    Sum.inr (Sum.inr (199, 0)),
    Sum.inr (Sum.inr (70, 21)),
    Sum.inr (Sum.inr (12, 12)),
    Sum.inr (Sum.inr (134, 11)),
    Sum.inr (Sum.inr (12, 10)),
    Sum.inr (Sum.inr (199, 23)),
    Sum.inr (Sum.inr (70, 2)),
    Sum.inr (Sum.inr (134, 15)),
    Sum.inr (Sum.inr (466, 16)),
    Sum.inr (Sum.inr (466, 17)),
    Sum.inr (Sum.inr (473, 7)),
    Sum.inr (Sum.inr (466, 19)),
    Sum.inr (Sum.inr (12, 3)),
    Sum.inr (Sum.inr (70, 9)),
    Sum.inr (Sum.inr (134, 22)),
    Sum.inr (Sum.inr (199, 13)),
    Sum.inr (Sum.inr (135, 0)),
    Sum.inr (Sum.inr (198, 11)),
    Sum.inr (Sum.inr (6, 21)),
    Sum.inr (Sum.inr (76, 12)),
    Sum.inr (Sum.inr (409, 6)),
    Sum.inr (Sum.inr (402, 5)),
    Sum.inr (Sum.inr (409, 4)),
    Sum.inr (Sum.inr (409, 18)),
    Sum.inr (Sum.inr (135, 8)),
    Sum.inr (Sum.inr (6, 14)),
    Sum.inr (Sum.inr (76, 20)),
    Sum.inr (Sum.inr (198, 1)),
    Sum.inr (Sum.inr (76, 3)),
    Sum.inr (Sum.inr (135, 13)),
    Sum.inr (Sum.inr (6, 9)),
    Sum.inr (Sum.inr (198, 22)),
    Sum.inr (Sum.inr (402, 16)),
    Sum.inr (Sum.inr (402, 17)),
    Sum.inr (Sum.inr (409, 7)),
    Sum.inr (Sum.inr (402, 19)),
    Sum.inr (Sum.inr (76, 10)),
    Sum.inr (Sum.inr (6, 2)),
    Sum.inr (Sum.inr (198, 15)),
    Sum.inr (Sum.inr (135, 23)),
    Sum.inr (Sum.inl (215, 37)),
    Sum.inr (Sum.inl (209, 11)),
    Sum.inr (Sum.inl (152, 50)),
    Sum.inr (Sum.inl (175, 59)),
    Sum.inr (Sum.inl (40, 41)),
    Sum.inr (Sum.inl (20, 59)),
    Sum.inr (Sum.inl (40, 35)),
    Sum.inr (Sum.inl (40, 33)),
    Sum.inr (Sum.inl (215, 52)),
    Sum.inr (Sum.inl (152, 34)),
    Sum.inr (Sum.inl (175, 43)),
    Sum.inr (Sum.inl (209, 42)),
    Sum.inr (Sum.inl (175, 41)),
    Sum.inr (Sum.inl (215, 36)),
    Sum.inr (Sum.inl (152, 54)),
    Sum.inr (Sum.inl (209, 43)),
    Sum.inr (Sum.inl (20, 27)),
    Sum.inr (Sum.inl (20, 43)),
    Sum.inr (Sum.inl (40, 43)),
    Sum.inr (Sum.inl (20, 11)),
    Sum.inr (Sum.inl (175, 57)),
    Sum.inr (Sum.inl (152, 38)),
    Sum.inr (Sum.inl (209, 10)),
    Sum.inr (Sum.inl (215, 53)),
    Sum.inr (Sum.inl (71, 11)),
    Sum.inr (Sum.inl (70, 21)),
    Sum.inr (Sum.inl (64, 52)),
    Sum.inr (Sum.inl (66, 61)),
    Sum.inr (Sum.inl (22, 54)),
    Sum.inr (Sum.inl (2, 12)),
    Sum.inr (Sum.inl (22, 60)),
    Sum.inr (Sum.inl (22, 62)),
    Sum.inr (Sum.inl (71, 26)),
    Sum.inr (Sum.inl (64, 20)),
    Sum.inr (Sum.inl (66, 45)),
    Sum.inr (Sum.inl (70, 52)),
    Sum.inr (Sum.inl (66, 53)),
    Sum.inr (Sum.inl (71, 36)),
    Sum.inr (Sum.inl (64, 21)),
    Sum.inr (Sum.inl (70, 43)),
    Sum.inr (Sum.inl (2, 44)),
    Sum.inr (Sum.inl (2, 28)),
    Sum.inr (Sum.inl (22, 52)),
    Sum.inr (Sum.inl (2, 60)),
    Sum.inr (Sum.inl (66, 37)),
    Sum.inr (Sum.inl (64, 53)),
    Sum.inr (Sum.inl (70, 10)),
    Sum.inr (Sum.inl (71, 53)),
    Sum.inr (Sum.inl (179, 59)),
    Sum.inr (Sum.inl (178, 62)),
    Sum.inr (Sum.inl (142, 59)),
    Sum.inr (Sum.inl (165, 38)),
    Sum.inr (Sum.inl (30, 6)),
    Sum.inr (Sum.inl (10, 0)),
    Sum.inr (Sum.inl (30, 12)),
    Sum.inr (Sum.inl (30, 14))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock094Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨24064 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock094InputMaskData : ℕ :=
  sixthHex% [
    "8165c6896dc6856dc6cd6dc6fd95c6dd95c6ed9dc68d95c683edc5b5edc5",
    "aeedc5d8e5c5bf2dc5a125c5862dc5d82dc5a745c58d4dc5b245c5d845c5",
    "9b75c59975c59a75c5d87dc5946dc59c65c59065c5d865c5e89dc5c89dc5",
    "f895c5989dc5e3e5c4d5e5c4cee5c4b8edc4df25c4c12dc4e625c4b825c4",
    "c74dc4ed45c4d24dc4b84dc4fb75c4f975c4fa75c4b87dc4f465c4fc6dc4",
    "f06dc4b86dc4889dc4a89dc49895c4f89dc4afedc399edc382edc3f4e5c3",
    "9325c38d2dc3aa25c3f425c38b4dc3a145c39e4dc3f44dc3b775c3b575c3",
    "b675c3f47dc3b86dc3b065c3bc65c3f465c3c49dc3e49dc3d495c3b49dc3",
    "cfe5c2f9e5c2e2e5c294edc2f32dc2ed25c2ca2dc2942dc2eb45c2c14dc2",
    "fe45c29445c2d775c2d575c2d675c2947dc2d865c2d06dc2dc6dc2946dc2",
    "a49dc2849dc2b495c2d49dc2daedc1ecedc1f7edc181e5c1e625c1f82dc1",
    "df25c18125c1fe45c1d44dc1eb45c18145c1c275c1c075c1c375c1817dc1",
    "cd6dc1c565c1c965c18165c1b195c19195c1a19dc1c195c1faedc0ccedc0",
    "d7edc0a1e5c0c625c0d82dc0ff25c0a125c0de45c0f44dc0cb45c0a145c0",
    "e27dc0e07dc0e37dc0a175c0ed6dc0e565c0e965c0a165c0919dc0b19dc0",
    "8195c0e19dc0c075aff675afed7daf9b75affcb5afe2bdafc5b5af9bb5af",
    "e4d5afced5aff1ddaf9bd5afd8e5afdaedafd9e5af9be5afd7fdafdff5af",
    "d3fdaf9bfdafab05af8b05afbb0dafdb05afa175ae9775ae8c7daefa75ae",
    "9db5ae83bdaea4b5aefab5ae85d5aeafd5ae90ddaefad5aeb9edaebbe5ae",
    "b8edaefaedaeb6fdaebef5aeb2fdaefafdaeca0daeea0daeda05aeba0dae",
    "8a75adbc75ada77dadd175adb6b5ada8bdad8fb5add1b5adaeddad84ddad",
    "bbd5add1ddad92e5ad90edad93e5add1e5ad9dfdad95f5ad99fdadd1fdad",
    "e10dadc10dadf105ad910dadab7dac9d7dac8675acf07dac97bdac89b5ac",
    "aebdacf0bdac8fd5aca5d5ac9addacf0d5acb3e5acb1edacb2e5acf0e5ac",
    "bcf5acb4fdacb8f5acf0f5acc00dace00dacd005acb00dac9975abaf75ab",
    "b47dabc275aba5bdabbbb5ab9cbdabc2bdab"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock094InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock094InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock094OutputMaskData : ℕ :=
  sixthHex% [
    "78d5c6019dc63895cd459dc63832a33c7b996ba8b96ba1880e7b91293aa0",
    "24a18007a0ba1837d44277df2137d47f37d44ad2a00701804e93910700ba",
    "76e2a04630ba61798055eb91067fdf7f37df463fd43b37df4698ba42d180",
    "1502a0150b910ddaa12a9b902700b004018a1b96e441d6ef2296e47c96e4",
    "49739004a0b04d32a104a18a04039034d18a1398b0270aa105deef7c96ef",
    "459ee43896ef34798a3030b067e39067eaa1baba179dfb26906006b3613c",
    "ddb65287f659e4b652bab6528f5326c280068b1217c2813cc22326f2f13c",
    "d5b806e12a17b2be59cbf659f2fe528ff659f2593cf61006a1c326a1ca17",
    "b91b279e5a1693c136b0c00cde1762845769e71762b917628cf216c12136",
    "88b327c1200cb0c21680100ca7593693cb27b11f69c85769f15f628c5769",
    "80b80c84f136d32216d32b27c7b13ee0f00fed6b2fce6a15a0bd7bfafd70",
    "99bd7bc7bd7b83180fcecb2f87593ececa15bf280f8ffa15a8b32f9c213e",
    "cfb570b6fd708ff57bf2fd70fe1215fa5b2fad880fad813ec05005e71134",
    "ea8a14c98b2ea75c40fd1c4b9e5c40c05c4084f934c92a1480b805c92b2e",
    "c98934f95b2ede1214ea8005c8544bb11c4b881440f51c4b88b32e8cfa14",
    "db2934db20050069e12728d05bf3f078f2ca1625a44c65af2f25a47125a4",
    "3580d00913f04081e17852ca09b0d04822ca1e2bf05bf9e1792daf0065af",
    "482da43525af488aca4cc3f01b10d01b19e16513f14252c03e89e01d88da",
    "735fb4291fbf4a5fb4145fb450fac06c69e025fbf11d28da1d8ac05c18da",
    "0a11e04fc3f11c57bf651fbf2d57b4505fbf5cb0da58f9e00f2ac00f23f1",
    "45b0d962f1e81e2ac83d2bf253fc9c09bc976afc9c34fc9c0119e83d8ac8",
    "7418d94ccbf24c69e80dfbf25bf2c81e20d93cf49745bc970df49c70fc97",
    "7c13f2785ac82f89e82f80d9248ac203cbf37f10d35c11e932c68768868c",
    "0bc68755c6876023f35cb0d31522c22df1e95c13f31d81e94b88d30e5ac2",
    "5dce8c24868c6cce8711c68c6c69e96820d33ff3f33ffac2c9a34eeee27f",
    "92395fb13865aeaf0bf4ef0097af0bc9af0b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock094OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock094OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock094InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock094InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock094InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock094OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e185f85f86186196175d7e185f85f7e185f7e17e185f8617df96175d",
    "7df8617df7df85f7e17e17e185f86195f75d85f86185f8617df7e186185f",
    "7e18616e18e37df7e18617e186185f7df85f85f86195f75d7e17df85f861",
    "7df7e17df7e185f7df95f75d7df7e17df85f7df7e17df85f7df7e16e18e3",
    "7e17df86185f7e18618617e18617e195f75d86185f85f7df85f7df7df7e1",
    "7df7e16e18e385f86186185f7e18617df85f8617e195f75d7df7e185f7df",
    "85f7df86185f85f85f96175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock094OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock094OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block094_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock094Input a) =
      generatedSixthXiShortBlock094InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock094Output a) =
      generatedSixthXiShortBlock094OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock094Input a) =
      generatedSixthXiShortBlock094InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock094Output a) =
      generatedSixthXiShortBlock094OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block094_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock094InputMask a) =
      generatedSixthXiShortBlock094OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock094InputMask a)) *
      generatedSixthXiShortBlock094InputNumerator a =
        generatedSixthXiShortBlock094OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block094_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock094Input a
    let y := generatedSixthXiShortBlock094Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block094_cache a
  have hs := generatedSixth_xi_short_block094_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block094_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock094Input a
    let y := generatedSixthXiShortBlock094Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block094_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block094_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock094Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block094_certificate a).1
    (generatedSixth_xi_short_block094_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
