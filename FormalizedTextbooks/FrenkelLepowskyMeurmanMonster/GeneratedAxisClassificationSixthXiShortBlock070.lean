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
def generatedSixthXiShortBlock070Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (2, 38)),
    Sum.inr (Sum.inl (2, 22)),
    Sum.inr (Sum.inl (22, 30)),
    Sum.inr (Sum.inl (2, 54)),
    Sum.inr (Sum.inl (66, 7)),
    Sum.inr (Sum.inl (64, 45)),
    Sum.inr (Sum.inl (70, 2)),
    Sum.inr (Sum.inl (71, 19)),
    Sum.inr (Sum.inr (473, 8)),
    Sum.inr (Sum.inr (408, 1)),
    Sum.inr (Sum.inr (344, 14)),
    Sum.inr (Sum.inr (274, 20)),
    Sum.inr (Sum.inr (199, 6)),
    Sum.inr (Sum.inr (204, 5)),
    Sum.inr (Sum.inr (199, 4)),
    Sum.inr (Sum.inr (199, 18)),
    Sum.inr (Sum.inr (473, 0)),
    Sum.inr (Sum.inr (344, 21)),
    Sum.inr (Sum.inr (274, 12)),
    Sum.inr (Sum.inr (408, 11)),
    Sum.inr (Sum.inr (274, 10)),
    Sum.inr (Sum.inr (473, 23)),
    Sum.inr (Sum.inr (344, 2)),
    Sum.inr (Sum.inr (408, 15)),
    Sum.inr (Sum.inr (204, 16)),
    Sum.inr (Sum.inr (204, 17)),
    Sum.inr (Sum.inr (199, 7)),
    Sum.inr (Sum.inr (204, 19)),
    Sum.inr (Sum.inr (274, 3)),
    Sum.inr (Sum.inr (344, 9)),
    Sum.inr (Sum.inr (408, 22)),
    Sum.inr (Sum.inr (473, 13)),
    Sum.inr (Sum.inr (409, 0)),
    Sum.inr (Sum.inr (472, 11)),
    Sum.inr (Sum.inr (280, 21)),
    Sum.inr (Sum.inr (338, 12)),
    Sum.inr (Sum.inr (135, 6)),
    Sum.inr (Sum.inr (140, 5)),
    Sum.inr (Sum.inr (135, 4)),
    Sum.inr (Sum.inr (135, 18)),
    Sum.inr (Sum.inr (409, 8)),
    Sum.inr (Sum.inr (280, 14)),
    Sum.inr (Sum.inr (338, 20)),
    Sum.inr (Sum.inr (472, 1)),
    Sum.inr (Sum.inr (338, 3)),
    Sum.inr (Sum.inr (409, 13)),
    Sum.inr (Sum.inr (280, 9)),
    Sum.inr (Sum.inr (472, 22)),
    Sum.inr (Sum.inr (140, 16)),
    Sum.inr (Sum.inr (140, 17)),
    Sum.inr (Sum.inr (135, 7)),
    Sum.inr (Sum.inr (140, 19)),
    Sum.inr (Sum.inr (338, 10)),
    Sum.inr (Sum.inr (280, 2)),
    Sum.inr (Sum.inr (472, 15)),
    Sum.inr (Sum.inr (409, 23)),
    Sum.inr (Sum.inr (283, 23)),
    Sum.inr (Sum.inr (346, 15)),
    Sum.inr (Sum.inr (410, 2)),
    Sum.inr (Sum.inr (464, 10)),
    Sum.inr (Sum.inr (5, 6)),
    Sum.inr (Sum.inr (14, 5)),
    Sum.inr (Sum.inr (5, 4)),
    Sum.inr (Sum.inr (5, 18)),
    Sum.inr (Sum.inr (283, 13)),
    Sum.inr (Sum.inr (410, 9)),
    Sum.inr (Sum.inr (464, 3)),
    Sum.inr (Sum.inr (346, 22)),
    Sum.inr (Sum.inr (464, 20)),
    Sum.inr (Sum.inr (283, 8)),
    Sum.inr (Sum.inr (410, 14)),
    Sum.inr (Sum.inr (346, 1)),
    Sum.inr (Sum.inr (14, 16)),
    Sum.inr (Sum.inr (14, 17)),
    Sum.inr (Sum.inr (5, 7)),
    Sum.inr (Sum.inr (14, 19)),
    Sum.inr (Sum.inr (464, 12)),
    Sum.inr (Sum.inr (410, 21)),
    Sum.inr (Sum.inr (346, 11)),
    Sum.inr (Sum.inr (283, 0)),
    Sum.inr (Sum.inr (336, 13)),
    Sum.inr (Sum.inr (273, 22)),
    Sum.inr (Sum.inr (465, 9)),
    Sum.inr (Sum.inr (411, 3)),
    Sum.inr (Sum.inr (78, 6)),
    Sum.inr (Sum.inr (69, 5)),
    Sum.inr (Sum.inr (78, 4)),
    Sum.inr (Sum.inr (78, 18)),
    Sum.inr (Sum.inr (336, 23)),
    Sum.inr (Sum.inr (465, 2)),
    Sum.inr (Sum.inr (411, 10)),
    Sum.inr (Sum.inr (273, 15)),
    Sum.inr (Sum.inr (411, 12)),
    Sum.inr (Sum.inr (336, 0)),
    Sum.inr (Sum.inr (465, 21)),
    Sum.inr (Sum.inr (273, 11)),
    Sum.inr (Sum.inr (69, 16)),
    Sum.inr (Sum.inr (69, 17)),
    Sum.inr (Sum.inr (78, 7)),
    Sum.inr (Sum.inr (69, 19)),
    Sum.inr (Sum.inr (411, 20)),
    Sum.inr (Sum.inr (465, 14)),
    Sum.inr (Sum.inr (273, 1)),
    Sum.inr (Sum.inr (336, 8)),
    Sum.inr (Sum.inl (53, 41)),
    Sum.inr (Sum.inl (52, 54)),
    Sum.inr (Sum.inl (46, 23)),
    Sum.inr (Sum.inl (48, 33)),
    Sum.inr (Sum.inl (21, 37)),
    Sum.inr (Sum.inl (1, 9)),
    Sum.inr (Sum.inl (21, 45)),
    Sum.inr (Sum.inl (21, 47)),
    Sum.inr (Sum.inl (53, 56)),
    Sum.inr (Sum.inl (46, 6)),
    Sum.inr (Sum.inl (48, 49)),
    Sum.inr (Sum.inl (52, 22)),
    Sum.inr (Sum.inl (48, 37)),
    Sum.inr (Sum.inl (53, 40)),
    Sum.inr (Sum.inl (46, 7)),
    Sum.inr (Sum.inl (52, 23)),
    Sum.inr (Sum.inl (1, 41)),
    Sum.inr (Sum.inl (1, 25)),
    Sum.inr (Sum.inl (21, 39)),
    Sum.inr (Sum.inl (1, 57)),
    Sum.inr (Sum.inl (48, 53)),
    Sum.inr (Sum.inl (46, 22)),
    Sum.inr (Sum.inl (52, 55)),
    Sum.inr (Sum.inl (53, 57)),
    Sum.inr (Sum.inl (119, 5)),
    Sum.inr (Sum.inl (118, 62)),
    Sum.inr (Sum.inl (112, 59)),
    Sum.inr (Sum.inl (114, 22)),
    Sum.inr (Sum.inl (25, 4)),
    Sum.inr (Sum.inl (5, 0)),
    Sum.inr (Sum.inl (25, 12)),
    Sum.inr (Sum.inl (25, 14)),
    Sum.inr (Sum.inl (119, 20)),
    Sum.inr (Sum.inl (112, 41)),
    Sum.inr (Sum.inl (114, 6)),
    Sum.inr (Sum.inl (118, 33)),
    Sum.inr (Sum.inl (114, 4)),
    Sum.inr (Sum.inl (119, 42)),
    Sum.inr (Sum.inl (112, 6)),
    Sum.inr (Sum.inl (118, 9)),
    Sum.inr (Sum.inl (5, 32)),
    Sum.inr (Sum.inl (5, 16)),
    Sum.inr (Sum.inl (25, 6)),
    Sum.inr (Sum.inl (5, 48)),
    Sum.inr (Sum.inl (114, 20)),
    Sum.inr (Sum.inl (112, 20)),
    Sum.inr (Sum.inl (118, 22)),
    Sum.inr (Sum.inl (119, 59)),
    Sum.inr (Sum.inl (213, 39)),
    Sum.inr (Sum.inl (207, 23)),
    Sum.inr (Sum.inl (150, 37)),
    Sum.inr (Sum.inl (173, 55)),
    Sum.inr (Sum.inl (38, 21)),
    Sum.inr (Sum.inl (18, 5)),
    Sum.inr (Sum.inl (38, 29)),
    Sum.inr (Sum.inl (38, 31)),
    Sum.inr (Sum.inl (213, 56)),
    Sum.inr (Sum.inl (150, 5)),
    Sum.inr (Sum.inl (173, 21)),
    Sum.inr (Sum.inl (207, 54)),
    Sum.inr (Sum.inl (173, 23)),
    Sum.inr (Sum.inl (213, 6)),
    Sum.inr (Sum.inl (150, 45)),
    Sum.inr (Sum.inl (207, 41)),
    Sum.inr (Sum.inl (18, 37)),
    Sum.inr (Sum.inl (18, 21)),
    Sum.inr (Sum.inl (38, 23)),
    Sum.inr (Sum.inl (18, 53)),
    Sum.inr (Sum.inl (173, 53)),
    Sum.inr (Sum.inl (150, 13)),
    Sum.inr (Sum.inl (207, 8)),
    Sum.inr (Sum.inl (213, 25)),
    Sum.inr (Sum.inl (158, 58)),
    Sum.inr (Sum.inl (157, 37)),
    Sum.inr (Sum.inl (140, 7)),
    Sum.inr (Sum.inl (153, 5)),
    Sum.inr (Sum.inl (28, 58)),
    Sum.inr (Sum.inl (8, 62)),
    Sum.inr (Sum.inl (28, 50)),
    Sum.inr (Sum.inl (28, 48)),
    Sum.inr (Sum.inl (158, 21)),
    Sum.inr (Sum.inl (140, 40)),
    Sum.inr (Sum.inl (153, 39)),
    Sum.inr (Sum.inl (157, 7)),
    Sum.inr (Sum.inl (153, 7)),
    Sum.inr (Sum.inl (158, 1)),
    Sum.inr (Sum.inl (140, 21)),
    Sum.inr (Sum.inl (157, 58)),
    Sum.inr (Sum.inl (8, 30)),
    Sum.inr (Sum.inl (8, 46)),
    Sum.inr (Sum.inl (28, 56)),
    Sum.inr (Sum.inl (8, 14)),
    Sum.inr (Sum.inl (153, 37)),
    Sum.inr (Sum.inl (140, 58)),
    Sum.inr (Sum.inl (157, 24)),
    Sum.inr (Sum.inl (158, 46)),
    Sum.inr (Sum.inr (331, 23)),
    Sum.inr (Sum.inr (266, 11)),
    Sum.inr (Sum.inr (458, 14)),
    Sum.inr (Sum.inr (384, 3)),
    Sum.inr (Sum.inr (85, 7)),
    Sum.inr (Sum.inr (94, 5)),
    Sum.inr (Sum.inr (85, 18)),
    Sum.inr (Sum.inr (85, 4)),
    Sum.inr (Sum.inr (331, 13)),
    Sum.inr (Sum.inr (458, 21)),
    Sum.inr (Sum.inr (384, 10)),
    Sum.inr (Sum.inr (266, 1)),
    Sum.inr (Sum.inr (384, 12)),
    Sum.inr (Sum.inr (331, 8)),
    Sum.inr (Sum.inr (458, 2)),
    Sum.inr (Sum.inr (266, 22)),
    Sum.inr (Sum.inr (94, 16)),
    Sum.inr (Sum.inr (94, 17)),
    Sum.inr (Sum.inr (85, 6)),
    Sum.inr (Sum.inr (94, 19)),
    Sum.inr (Sum.inr (384, 20)),
    Sum.inr (Sum.inr (458, 9)),
    Sum.inr (Sum.inr (266, 15)),
    Sum.inr (Sum.inr (331, 0)),
    Sum.inr (Sum.inr (448, 13)),
    Sum.inr (Sum.inr (385, 1)),
    Sum.inr (Sum.inr (321, 21)),
    Sum.inr (Sum.inr (267, 10)),
    Sum.inr (Sum.inr (222, 7)),
    Sum.inr (Sum.inr (213, 5)),
    Sum.inr (Sum.inr (222, 18)),
    Sum.inr (Sum.inr (222, 4)),
    Sum.inr (Sum.inr (448, 23)),
    Sum.inr (Sum.inr (321, 14)),
    Sum.inr (Sum.inr (267, 3)),
    Sum.inr (Sum.inr (385, 11)),
    Sum.inr (Sum.inr (267, 20)),
    Sum.inr (Sum.inr (448, 0)),
    Sum.inr (Sum.inr (321, 9)),
    Sum.inr (Sum.inr (385, 15)),
    Sum.inr (Sum.inr (213, 16)),
    Sum.inr (Sum.inr (213, 17)),
    Sum.inr (Sum.inr (222, 6)),
    Sum.inr (Sum.inr (213, 19)),
    Sum.inr (Sum.inr (267, 12)),
    Sum.inr (Sum.inr (321, 2)),
    Sum.inr (Sum.inr (385, 22)),
    Sum.inr (Sum.inr (448, 8)),
    Sum.inr (Sum.inr (259, 8)),
    Sum.inr (Sum.inr (322, 22)),
    Sum.inr (Sum.inr (386, 2)),
    Sum.inr (Sum.inr (456, 12)),
    Sum.inr (Sum.inr (29, 7)),
    Sum.inr (Sum.inr (22, 5)),
    Sum.inr (Sum.inr (29, 18)),
    Sum.inr (Sum.inr (29, 4))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock070Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨17920 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock070InputMaskData : ℕ :=
  sixthHex% [
    "a1f1e6a9f9e6a5f9e6edf1e6dd09e6fd09e6cd01e6ad01e6b741e58149e5",
    "9a41e5ec49e58b81e59581e5b281e5ec81e593e9e5b9e9e586e9e5ece9e5",
    "afd9e5add1e5aed9e5ecd1e5a0c9e5a8c1e5a4c1e5ecc9e5dc31e5fc31e5",
    "cc39e5ac39e5d6a9e4e0a1e4fba9e48da1e4ea69e4f469e4d369e48d69e4",
    "f201e4d801e4e701e48d01e4ce39e4cc31e4cf39e48d31e4c121e4c929e4",
    "c529e48d21e4bdd1e49dd1e4add9e4cdd9e4b721e38129e39a21e3ec29e3",
    "8be9e395e9e3b2e9e3ece9e39381e3b981e38681e3ec81e3afb9e3adb1e3",
    "aeb9e3ecb1e3a0a9e3a8a1e3a4a1e3eca9e3dc51e3fc51e3cc59e3ac59e3",
    "d6c9e2e0c1e2fbc9e28dc1e2ea01e2f401e2d301e28d01e2f269e2d869e2",
    "e769e28d69e2ce59e2cc51e2cf59e28d51e2c141e2c949e2c549e28d41e2",
    "bdb1e29db1e2adb9e2cdb9e2d7f1e1e1f9e1faf1e18cf9e1eb39e1f539e1",
    "d239e18c39e1f359e1d959e1e659e18c59e1cf69e1cd61e1ce69e18c61e1",
    "c079e1c871e1c471e18c79e1bc89e19c89e1ac81e1cc81e1f619e0c011e0",
    "db19e0ad11e0cad1e0d4d1e0f3d1e0add1e0d2b1e0f8b1e0c7b1e0adb1e0",
    "ee89e0ec81e0ef89e0ad81e0e191e0e999e0e599e0ad91e09d69e0bd69e0",
    "8d61e0ed61e0fcd98fcad18fd1d18fa7d98fc0198fde198ff9198fa7198f",
    "d8798ff2718fcd718fa7798fe4498fe6498fe5498fa7498feb598fe3518f",
    "ef598fa7518f97a98fb7a98f87a18fe7a18f9c398eaa318eb1318ec7398e",
    "a0f98ebef98e99f98ec7f98eb8998e92918ead918ec7998e84a18e86a18e",
    "85a18ec7a18e8bb98e83b18e8fb98ec7b18ef7418ed7418ee7498e87498e",
    "a3018d95098d8e098df8018d9fc18d81c18da6c18df8c18d87a98dada18d",
    "92a18df8a98dbb918db9918dba918df8918db4818dbc898db0818df8898d",
    "c8798de8798dd8718db8718d83e18cb5e98caee98cd8e18cbf218ca1218c",
    "86218cd8218ca7498c8d418cb2418cd8498c9b798c99798c9a798cd8798c",
    "94618c9c698c90618cd8698ce8918cc8918cf8998c98998c9c698baa618b",
    "b1618bc7698ba0a18bbea18b99a18bc7a18b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock070InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock070InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock070OutputMaskData : ℕ :=
  sixthHex% [
    "87686dfe206dc72866cb606db6cf08b28632e55512941c23b0f700e6f631",
    "9a2d11b92c2ba6bb458dbb4e9fbb45c1bb45f45e31c8cd11f01f00b98c2b",
    "c86e3189fc2bdff511eb6700c9b34eb0fb4e89f34585bb4ef8142bfc5d11",
    "ab8e31dac700912d1bc72c2abbf70a98f63087615eac6155be615ee0615e",
    "d5842ae9170ad1c51b98563098f42ad966308f6f0abbfd1be86955912155",
    "a8295ea46155a88e30acc70afb142a8a5d1b3000d96601e81adac839dbf2",
    "570c9c7c0c976e0c9c300c9c05e9e8397ac801a8d9483bf24899e8090bf2",
    "5f02c86b90d9494497300c9709049c054c9778e3f27caac82b79e85a30d9",
    "11dac247dbf33b00d31801e976d6875dd68c4fd68711d6872433f318a0d3",
    "2072c269e1e91803f35991e90f98d33b0ac2689e8c11d68c28de8724968c",
    "2879e92c30d37be3f30aaac25f01e10900d075dbf056daca380da4130daf",
    "010da45f0da41ba8d0273bf01fe9e1567aca2798d0660aca3003f00491e1",
    "2645af5f0daf6605a46a4daf66a2ca62ebf03538d04471e10bdbf15ddac0",
    "2101e00200da6cd7b447d7bf55d7b40bd7b44f72c073e1e04b33f102a0da",
    "0202c04390da1599e0210bf1729fbf0bd7bf32dfb43e97bf4338da4771e0",
    "10a2c061ebf1b6ed70e0ec41ed7761ce765ba0a1358ba13e99a135c7a135",
    "830441ced761f60570ced65bbf34418fe65ba8af61ed7d70bee93ec7a13e",
    "8fe93583a13efe0e5bfa4761ad9441dcdd70f1ec4ba7ed7aaa765a897760",
    "e7a00ecca005dea00e80a00ec4057a89d65ab1044b89d76089757ab9a760",
    "9eee5adb3c4bf9e80580a005c8e80ec4a005c84f60cc065a9bd57aea9c4b",
    "907e59c67f68cbe448e8e57286321cad3217bf321ce1321cd4d768990448",
    "a1d65999057299a768a975728e3c48cbee59987a17e13217a97a1ca53217",
    "a9dd72ad9448fa47688b0e59a27f69f47e58f9e578dae442b4332c9f3327",
    "8d332cd3332ce6d658ab057893d769ab0442dae658ea3442cd7d7888af69",
    "aa7b27d333279b7b2c973327ea9c42eed578b90658c84f69591b910f1aa0",
    "0281802180ba3e17d41517df0717d45917d4"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock070OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock070OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock070InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e3"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock070InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock070InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock070OutputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df85f7e17e17e16df8e37e185f8617df86186185f85f7e185f6df8e3",
    "7df8617e17e186186185f7e17df7e16e18e385f86186185f7e18617df85f",
    "7df85f6e18e386185f7e18617e18617df7e17df7e16e18e37e17df86185f",
    "7e18618617e18617e195f75d86185f85f7df85f7df7df7e17e17df6e18e3",
    "85f8617e17df86185f86185f85f7df95f75d7df7e17df85f7df7e17df85f",
    "7e17df6e18e37e17df7e17df86185f7df7e185f7df95f75d86185f7df85f",
    "7df7e18617e186186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock070OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock070OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block070_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock070Input a) =
      generatedSixthXiShortBlock070InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock070Output a) =
      generatedSixthXiShortBlock070OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock070Input a) =
      generatedSixthXiShortBlock070InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock070Output a) =
      generatedSixthXiShortBlock070OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block070_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock070InputMask a) =
      generatedSixthXiShortBlock070OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock070InputMask a)) *
      generatedSixthXiShortBlock070InputNumerator a =
        generatedSixthXiShortBlock070OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block070_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock070Input a
    let y := generatedSixthXiShortBlock070Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block070_cache a
  have hs := generatedSixth_xi_short_block070_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block070_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock070Input a
    let y := generatedSixthXiShortBlock070Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block070_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block070_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock070Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block070_certificate a).1
    (generatedSixth_xi_short_block070_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
