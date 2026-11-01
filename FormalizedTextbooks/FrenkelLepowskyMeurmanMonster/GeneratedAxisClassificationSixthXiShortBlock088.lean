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
def generatedSixthXiShortBlock088Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (257, 16)),
    Sum.inr (Sum.inr (257, 17)),
    Sum.inr (Sum.inr (266, 6)),
    Sum.inr (Sum.inr (257, 19)),
    Sum.inr (Sum.inr (223, 20)),
    Sum.inr (Sum.inr (149, 9)),
    Sum.inr (Sum.inr (85, 15)),
    Sum.inr (Sum.inr (20, 0)),
    Sum.inr (Sum.inl (158, 24)),
    Sum.inr (Sum.inl (157, 48)),
    Sum.inr (Sum.inl (140, 47)),
    Sum.inr (Sum.inl (153, 50)),
    Sum.inr (Sum.inl (28, 16)),
    Sum.inr (Sum.inl (8, 52)),
    Sum.inr (Sum.inl (28, 24)),
    Sum.inr (Sum.inl (28, 26)),
    Sum.inr (Sum.inl (158, 55)),
    Sum.inr (Sum.inl (140, 0)),
    Sum.inr (Sum.inl (153, 16)),
    Sum.inr (Sum.inl (157, 18)),
    Sum.inr (Sum.inl (153, 48)),
    Sum.inr (Sum.inl (158, 35)),
    Sum.inr (Sum.inl (140, 61)),
    Sum.inr (Sum.inl (157, 47)),
    Sum.inr (Sum.inl (8, 20)),
    Sum.inr (Sum.inl (8, 36)),
    Sum.inr (Sum.inl (28, 18)),
    Sum.inr (Sum.inl (8, 4)),
    Sum.inr (Sum.inl (153, 18)),
    Sum.inr (Sum.inl (140, 18)),
    Sum.inr (Sum.inl (157, 13)),
    Sum.inr (Sum.inl (158, 12)),
    Sum.inr (Sum.inl (213, 47)),
    Sum.inr (Sum.inl (207, 1)),
    Sum.inr (Sum.inl (150, 24)),
    Sum.inr (Sum.inl (173, 0)),
    Sum.inr (Sum.inl (38, 32)),
    Sum.inr (Sum.inl (18, 56)),
    Sum.inr (Sum.inl (38, 40)),
    Sum.inr (Sum.inl (38, 42)),
    Sum.inr (Sum.inl (213, 48)),
    Sum.inr (Sum.inl (150, 56)),
    Sum.inr (Sum.inl (173, 34)),
    Sum.inr (Sum.inl (207, 32)),
    Sum.inr (Sum.inl (173, 32)),
    Sum.inr (Sum.inl (213, 14)),
    Sum.inr (Sum.inl (150, 16)),
    Sum.inr (Sum.inl (207, 63)),
    Sum.inr (Sum.inl (18, 24)),
    Sum.inr (Sum.inl (18, 40)),
    Sum.inr (Sum.inl (38, 34)),
    Sum.inr (Sum.inl (18, 8)),
    Sum.inr (Sum.inl (173, 2)),
    Sum.inr (Sum.inl (150, 48)),
    Sum.inr (Sum.inl (207, 30)),
    Sum.inr (Sum.inl (213, 17)),
    Sum.inr (Sum.inl (119, 15)),
    Sum.inr (Sum.inl (118, 43)),
    Sum.inr (Sum.inl (112, 50)),
    Sum.inr (Sum.inl (114, 31)),
    Sum.inr (Sum.inl (25, 15)),
    Sum.inr (Sum.inl (5, 3)),
    Sum.inr (Sum.inl (25, 7)),
    Sum.inr (Sum.inl (25, 5)),
    Sum.inr (Sum.inl (119, 30)),
    Sum.inr (Sum.inl (112, 32)),
    Sum.inr (Sum.inl (114, 15)),
    Sum.inr (Sum.inl (118, 52)),
    Sum.inr (Sum.inl (114, 13)),
    Sum.inr (Sum.inl (119, 32)),
    Sum.inr (Sum.inl (112, 15)),
    Sum.inr (Sum.inl (118, 28)),
    Sum.inr (Sum.inl (5, 35)),
    Sum.inr (Sum.inl (5, 19)),
    Sum.inr (Sum.inl (25, 13)),
    Sum.inr (Sum.inl (5, 51)),
    Sum.inr (Sum.inl (114, 29)),
    Sum.inr (Sum.inl (112, 29)),
    Sum.inr (Sum.inl (118, 3)),
    Sum.inr (Sum.inl (119, 49)),
    Sum.inr (Sum.inl (53, 1)),
    Sum.inr (Sum.inl (52, 31)),
    Sum.inr (Sum.inl (46, 63)),
    Sum.inr (Sum.inl (48, 43)),
    Sum.inr (Sum.inl (21, 63)),
    Sum.inr (Sum.inl (1, 15)),
    Sum.inr (Sum.inl (21, 55)),
    Sum.inr (Sum.inl (21, 53)),
    Sum.inr (Sum.inl (53, 16)),
    Sum.inr (Sum.inl (46, 46)),
    Sum.inr (Sum.inl (48, 59)),
    Sum.inr (Sum.inl (52, 63)),
    Sum.inr (Sum.inl (48, 47)),
    Sum.inr (Sum.inl (53, 0)),
    Sum.inr (Sum.inl (46, 47)),
    Sum.inr (Sum.inl (52, 62)),
    Sum.inr (Sum.inl (1, 47)),
    Sum.inr (Sum.inl (1, 31)),
    Sum.inr (Sum.inl (21, 61)),
    Sum.inr (Sum.inl (1, 63)),
    Sum.inr (Sum.inl (48, 63)),
    Sum.inr (Sum.inl (46, 62)),
    Sum.inr (Sum.inl (52, 30)),
    Sum.inr (Sum.inl (53, 17)),
    Sum.inr (Sum.inr (15, 13)),
    Sum.inr (Sum.inr (78, 22)),
    Sum.inr (Sum.inr (142, 9)),
    Sum.inr (Sum.inr (196, 3)),
    Sum.inr (Sum.inr (273, 6)),
    Sum.inr (Sum.inr (282, 5)),
    Sum.inr (Sum.inr (273, 4)),
    Sum.inr (Sum.inr (273, 18)),
    Sum.inr (Sum.inr (15, 23)),
    Sum.inr (Sum.inr (142, 2)),
    Sum.inr (Sum.inr (196, 10)),
    Sum.inr (Sum.inr (78, 15)),
    Sum.inr (Sum.inr (196, 12)),
    Sum.inr (Sum.inr (15, 0)),
    Sum.inr (Sum.inr (142, 21)),
    Sum.inr (Sum.inr (78, 11)),
    Sum.inr (Sum.inr (282, 16)),
    Sum.inr (Sum.inr (282, 17)),
    Sum.inr (Sum.inr (273, 7)),
    Sum.inr (Sum.inr (282, 19)),
    Sum.inr (Sum.inr (196, 20)),
    Sum.inr (Sum.inr (142, 14)),
    Sum.inr (Sum.inr (78, 1)),
    Sum.inr (Sum.inr (15, 8)),
    Sum.inr (Sum.inr (68, 23)),
    Sum.inr (Sum.inr (5, 15)),
    Sum.inr (Sum.inr (197, 2)),
    Sum.inr (Sum.inr (143, 10)),
    Sum.inr (Sum.inr (346, 6)),
    Sum.inr (Sum.inr (337, 5)),
    Sum.inr (Sum.inr (346, 4)),
    Sum.inr (Sum.inr (346, 18)),
    Sum.inr (Sum.inr (68, 13)),
    Sum.inr (Sum.inr (197, 9)),
    Sum.inr (Sum.inr (143, 3)),
    Sum.inr (Sum.inr (5, 22)),
    Sum.inr (Sum.inr (143, 20)),
    Sum.inr (Sum.inr (68, 8)),
    Sum.inr (Sum.inr (197, 14)),
    Sum.inr (Sum.inr (5, 1)),
    Sum.inr (Sum.inr (337, 16)),
    Sum.inr (Sum.inr (337, 17)),
    Sum.inr (Sum.inr (346, 7)),
    Sum.inr (Sum.inr (337, 19)),
    Sum.inr (Sum.inr (143, 12)),
    Sum.inr (Sum.inr (197, 21)),
    Sum.inr (Sum.inr (5, 11)),
    Sum.inr (Sum.inr (68, 0)),
    Sum.inr (Sum.inr (198, 0)),
    Sum.inr (Sum.inr (135, 11)),
    Sum.inr (Sum.inr (71, 21)),
    Sum.inr (Sum.inr (13, 12)),
    Sum.inr (Sum.inr (472, 6)),
    Sum.inr (Sum.inr (467, 5)),
    Sum.inr (Sum.inr (472, 4)),
    Sum.inr (Sum.inr (472, 18)),
    Sum.inr (Sum.inr (198, 8)),
    Sum.inr (Sum.inr (71, 14)),
    Sum.inr (Sum.inr (13, 20)),
    Sum.inr (Sum.inr (135, 1)),
    Sum.inr (Sum.inr (13, 3)),
    Sum.inr (Sum.inr (198, 13)),
    Sum.inr (Sum.inr (71, 9)),
    Sum.inr (Sum.inr (135, 22)),
    Sum.inr (Sum.inr (467, 16)),
    Sum.inr (Sum.inr (467, 17)),
    Sum.inr (Sum.inr (472, 7)),
    Sum.inr (Sum.inr (467, 19)),
    Sum.inr (Sum.inr (13, 10)),
    Sum.inr (Sum.inr (71, 2)),
    Sum.inr (Sum.inr (135, 15)),
    Sum.inr (Sum.inr (198, 23)),
    Sum.inr (Sum.inr (134, 8)),
    Sum.inr (Sum.inr (199, 1)),
    Sum.inr (Sum.inr (7, 14)),
    Sum.inr (Sum.inr (77, 20)),
    Sum.inr (Sum.inr (408, 6)),
    Sum.inr (Sum.inr (403, 5)),
    Sum.inr (Sum.inr (408, 4)),
    Sum.inr (Sum.inr (408, 18)),
    Sum.inr (Sum.inr (134, 0)),
    Sum.inr (Sum.inr (7, 21)),
    Sum.inr (Sum.inr (77, 12)),
    Sum.inr (Sum.inr (199, 11)),
    Sum.inr (Sum.inr (77, 10)),
    Sum.inr (Sum.inr (134, 23)),
    Sum.inr (Sum.inr (7, 2)),
    Sum.inr (Sum.inr (199, 15)),
    Sum.inr (Sum.inr (403, 16)),
    Sum.inr (Sum.inr (403, 17)),
    Sum.inr (Sum.inr (408, 7)),
    Sum.inr (Sum.inr (403, 19)),
    Sum.inr (Sum.inr (77, 3)),
    Sum.inr (Sum.inr (7, 9)),
    Sum.inr (Sum.inr (199, 22)),
    Sum.inr (Sum.inr (134, 13)),
    Sum.inr (Sum.inl (71, 37)),
    Sum.inr (Sum.inl (70, 11)),
    Sum.inr (Sum.inl (64, 27)),
    Sum.inr (Sum.inl (66, 34)),
    Sum.inr (Sum.inl (22, 41)),
    Sum.inr (Sum.inl (2, 59)),
    Sum.inr (Sum.inl (22, 35)),
    Sum.inr (Sum.inl (22, 33)),
    Sum.inr (Sum.inl (71, 52)),
    Sum.inr (Sum.inl (64, 59)),
    Sum.inr (Sum.inl (66, 50)),
    Sum.inr (Sum.inl (70, 42)),
    Sum.inr (Sum.inl (66, 42)),
    Sum.inr (Sum.inl (71, 10)),
    Sum.inr (Sum.inl (64, 58)),
    Sum.inr (Sum.inl (70, 53)),
    Sum.inr (Sum.inl (2, 27)),
    Sum.inr (Sum.inl (2, 43)),
    Sum.inr (Sum.inl (22, 43)),
    Sum.inr (Sum.inl (2, 11)),
    Sum.inr (Sum.inl (66, 58)),
    Sum.inr (Sum.inl (64, 26)),
    Sum.inr (Sum.inl (70, 20)),
    Sum.inr (Sum.inl (71, 27)),
    Sum.inr (Sum.inl (215, 11)),
    Sum.inr (Sum.inl (209, 21)),
    Sum.inr (Sum.inl (152, 45)),
    Sum.inr (Sum.inl (175, 36)),
    Sum.inr (Sum.inl (40, 54)),
    Sum.inr (Sum.inl (20, 12)),
    Sum.inr (Sum.inl (40, 60)),
    Sum.inr (Sum.inl (40, 62)),
    Sum.inr (Sum.inl (215, 26)),
    Sum.inr (Sum.inl (152, 61)),
    Sum.inr (Sum.inl (175, 52)),
    Sum.inr (Sum.inl (209, 52)),
    Sum.inr (Sum.inl (175, 54)),
    Sum.inr (Sum.inl (215, 10)),
    Sum.inr (Sum.inl (152, 41)),
    Sum.inr (Sum.inl (209, 53)),
    Sum.inr (Sum.inl (20, 44)),
    Sum.inr (Sum.inl (20, 28)),
    Sum.inr (Sum.inl (40, 52)),
    Sum.inr (Sum.inl (20, 60)),
    Sum.inr (Sum.inl (175, 38)),
    Sum.inr (Sum.inl (152, 57)),
    Sum.inr (Sum.inl (209, 20)),
    Sum.inr (Sum.inl (215, 27)),
    Sum.inr (Sum.inl (104, 34)),
    Sum.inr (Sum.inl (103, 40)),
    Sum.inr (Sum.inl (97, 55)),
    Sum.inr (Sum.inl (99, 26)),
    Sum.inr (Sum.inl (24, 8)),
    Sum.inr (Sum.inl (4, 50)),
    Sum.inr (Sum.inl (24, 2)),
    Sum.inr (Sum.inl (24, 0))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock088Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨22528 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock088InputMaskData : ℕ :=
  sixthHex% [
    "c524f6cd2cf6c12cf6892cf6b9dcf699dcf6a9dcf6c9d4f6d1a4f5e7a4f5",
    "fcacf58aa4f5ed6cf5f364f5d46cf58a6cf5f50cf5df0cf5e00cf58a04f5",
    "c934f5cb3cf5c83cf58a3cf5c62cf5ce24f5c224f58a24f5bad4f59ad4f5",
    "aad4f5cadcf592acf4a4acf4bfa4f4c9acf4ae64f4b06cf49764f4c964f4",
    "b604f49c04f4a304f4c90cf48a34f4883cf48b3cf4c93cf48524f48d2cf4",
    "812cf4c92cf4f9d4f4d9d4f4e9d4f489dcf4e8acf3deacf3c5a4f3b3acf3",
    "d46cf3ca64f3ed6cf3b36cf3cc0cf3e60cf3d90cf3b304f3f03cf3f234f3",
    "f134f3b334f3ff24f3f72cf3fb2cf3b32cf383dcf3a3dcf393dcf3f3d4f3",
    "aba4f29da4f286acf2f0a4f29764f2896cf2ae64f2f064f28f04f2a504f2",
    "9a04f2f00cf2b33cf2b134f2b234f2f034f2bc2cf2b424f2b824f2f024f2",
    "c0dcf2e0dcf2d0dcf2b0d4f2a8acf19eacf185a4f1f3acf1946cf18a64f1",
    "ad6cf1f36cf18c04f1a604f19904f1f30cf1b03cf1b234f1b134f1f334f1",
    "bf24f1b72cf1bb2cf1f32cf1c3d4f1e3d4f1d3d4f1b3dcf1abacf09dacf0",
    "86a4f0f0acf0976cf08964f0ae6cf0f06cf08f04f0a504f09a04f0f00cf0",
    "b334f0b13cf0b23cf0f03cf0bc24f0b42cf0b82cf0f02cf0c0dcf0e0dcf0",
    "d0dcf0b0d4f0af049f99049f82049ff40c9f93cc9f8dc49faacc9ff4cc9f",
    "8ba49fa1ac9f9eac9ff4ac9fb79c9fb59c9fb6949ff49c9fb8849fb08c9f",
    "bc849ff4849fc4749fe4749fd4749fb47c9fed0c9edb0c9ec00c9eb6049e",
    "d1c49ecfcc9ee8c49eb6c49ec9ac9ee3a49edca49eb6a49ef59c9ef79c9e",
    "f4949eb69c9efa8c9ef2849efe8c9eb68c9e86749ea6749e96749ef67c9e",
    "d00c9de60c9dfd0c9d8b049decc49df2cc9dd5c49d8bc49df4a49ddeac9d",
    "e1ac9d8bac9dc8949dca949dc99c9d8b949dc78c9dcf849dc38c9d8b8c9d",
    "bb749d9b749dab749dcb7c9dd20c9ce40c9cff0c9c89049ceec49cf0cc9c",
    "d7c49c89c49cf6a49cdcac9ce3ac9c89ac9cca9c9cc89c9ccb949c899c9c",
    "c58c9ccd849cc18c9c898c9cb97c9c997c9ca97c9cc9749cd60c9be00c9b",
    "fb0c9b8d049beacc9bf4c49bd3cc9b8dcc9b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock088InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock088InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock088OutputMaskData : ℕ :=
  sixthHex% [
    "7cdcfd0594fd3c9cf64194fd4d7b984932a26fa1826fa8b3583aa17f7b90",
    "03a0b020a18a3f36e46576ef0636e45836e41c93902000b018d2a120018a",
    "51e39010718a3738b072eaa1217eef5836ef613ee41c36ef10d98a1490b0",
    "320390320aa1789b915fdaa02301800000ba1f97d445d7df2697d47897d4",
    "3c32a000a18038739100a0ba0002a04190ba66d980230b9101dfdf7897df",
    "419fd43c97df4138ba45718063e2a063eb9199fa16bebb27c26007e1613d",
    "8fb653d5f658b6b653e8b653ac1327908007a8521690813d902327d1b13d",
    "f6f807b32a16e0be5899f658a0fe53ddf658d1193dd55007f3c327f3ca16",
    "b95b269e1a17e2c137c1c00daf1763f55768961763c817638cb217b02137",
    "88f326b0200dc1c21780500da71937e2cb26c01f68b95768805f63fd5768",
    "80f80d84b137a22217a22b26e4f934c3b805bf63259c621ff2b571a8f57a",
    "cbb57195b571a050059cc325a411349cc21fed2005acb21f8bfb25ce2934",
    "9dbd7ae4f57addfd71a0f57add5a1fd91325ff8005ff8934c0180fe7593e",
    "9b821eb88324d6544a8c1441ef544ab1544a84b13eb8221e80f00fb82324",
    "b8813ef91324de5a1e9b880fb95c41c01441f91c4a84144188fb248cb21e",
    "aa213eaa280f0cc3f12b82c02619e00518da6bcfb4318fbf52cfb40ccfb4",
    "392ac074f9e04c2bf105b8da745ac04488da1281e02613f104c7bf7d8fbf",
    "35c7b448cfbf4420da4069e066fac066f3f13bf9e11cb8d01123f03222ca",
    "5cf5a406b5af65f5a43bf5a40e10d043c3f07b11e13282ca3220d002f2ca",
    "54fbf06069e133fdaf4ab5af02fda47ff5af025aca0613f02080d02089e1",
    "3852c21f13f31288d33189e95f5e87051e8c665e87385e877cfbf33128d3",
    "09fac24069e940cbf37019e92610d31282c230568c491e8c0156877c5e8c",
    "01f1e905b8d3232bf32322c20b28d92c69e821f2c802f3f26c249c366497",
    "55249c0b249c4f81e80252c83a80d97313f202f1e83223f2642ac850b8d9",
    "032c977a6497322c9c4f249743cbf24782c86111e86118d9b00064974155",
    "9ada75b9db4fa64c21fc0c2a9f4c21c14c21"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock088OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock088OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock088InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock088InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock088InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock088OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e185f7e17df8616df8e38617df8618617e185f85f85f86186196175d",
    "7e185f85f7e185f7e17e185f85f7df95f75d86185f7df85f7df7e18617e1",
    "85f86195f75d85f86185f8617df7e186185f85f7df95f75d7df7e17df85f",
    "7df7e17df85f7e17df6e18e385f8617e17df86185f86185f8617e195f75d",
    "86185f85f7df85f7df7df7e17df7e16e18e37e17df86185f7e18618617e1",
    "7df85f6e18e386185f7e18617e18617df7e186185f95f75d7e17df7df7e1",
    "85f7df8617e185f7e196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock088OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock088OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block088_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock088Input a) =
      generatedSixthXiShortBlock088InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock088Output a) =
      generatedSixthXiShortBlock088OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock088Input a) =
      generatedSixthXiShortBlock088InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock088Output a) =
      generatedSixthXiShortBlock088OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block088_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock088InputMask a) =
      generatedSixthXiShortBlock088OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock088InputMask a)) *
      generatedSixthXiShortBlock088InputNumerator a =
        generatedSixthXiShortBlock088OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block088_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock088Input a
    let y := generatedSixthXiShortBlock088Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block088_cache a
  have hs := generatedSixth_xi_short_block088_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block088_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock088Input a
    let y := generatedSixthXiShortBlock088Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block088_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block088_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock088Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block088_certificate a).1
    (generatedSixth_xi_short_block088_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
