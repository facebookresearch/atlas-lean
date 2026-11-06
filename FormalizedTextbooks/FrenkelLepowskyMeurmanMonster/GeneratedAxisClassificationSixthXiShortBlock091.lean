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
def generatedSixthXiShortBlock091Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (6, 42)),
    Sum.inr (Sum.inl (6, 26)),
    Sum.inr (Sum.inl (26, 42)),
    Sum.inr (Sum.inl (6, 58)),
    Sum.inr (Sum.inl (128, 35)),
    Sum.inr (Sum.inl (126, 19)),
    Sum.inr (Sum.inl (132, 12)),
    Sum.inr (Sum.inl (133, 45)),
    Sum.inr (Sum.inr (57, 13)),
    Sum.inr (Sum.inr (120, 11)),
    Sum.inr (Sum.inr (184, 2)),
    Sum.inr (Sum.inr (242, 20)),
    Sum.inr (Sum.inr (295, 18)),
    Sum.inr (Sum.inr (300, 5)),
    Sum.inr (Sum.inr (295, 7)),
    Sum.inr (Sum.inr (295, 6)),
    Sum.inr (Sum.inr (57, 23)),
    Sum.inr (Sum.inr (184, 9)),
    Sum.inr (Sum.inr (242, 12)),
    Sum.inr (Sum.inr (120, 1)),
    Sum.inr (Sum.inr (242, 10)),
    Sum.inr (Sum.inr (57, 0)),
    Sum.inr (Sum.inr (184, 14)),
    Sum.inr (Sum.inr (120, 22)),
    Sum.inr (Sum.inr (300, 16)),
    Sum.inr (Sum.inr (300, 17)),
    Sum.inr (Sum.inr (295, 4)),
    Sum.inr (Sum.inr (300, 19)),
    Sum.inr (Sum.inr (242, 3)),
    Sum.inr (Sum.inr (184, 21)),
    Sum.inr (Sum.inr (120, 15)),
    Sum.inr (Sum.inr (57, 8)),
    Sum.inr (Sum.inr (248, 23)),
    Sum.inr (Sum.inr (185, 1)),
    Sum.inr (Sum.inr (121, 9)),
    Sum.inr (Sum.inr (51, 12)),
    Sum.inr (Sum.inr (486, 18)),
    Sum.inr (Sum.inr (493, 5)),
    Sum.inr (Sum.inr (486, 7)),
    Sum.inr (Sum.inr (486, 6)),
    Sum.inr (Sum.inr (248, 13)),
    Sum.inr (Sum.inr (121, 2)),
    Sum.inr (Sum.inr (51, 20)),
    Sum.inr (Sum.inr (185, 11)),
    Sum.inr (Sum.inr (51, 3)),
    Sum.inr (Sum.inr (248, 8)),
    Sum.inr (Sum.inr (121, 21)),
    Sum.inr (Sum.inr (185, 15)),
    Sum.inr (Sum.inr (493, 16)),
    Sum.inr (Sum.inr (493, 17)),
    Sum.inr (Sum.inr (486, 4)),
    Sum.inr (Sum.inr (493, 19)),
    Sum.inr (Sum.inr (51, 10)),
    Sum.inr (Sum.inr (121, 14)),
    Sum.inr (Sum.inr (185, 22)),
    Sum.inr (Sum.inr (248, 0)),
    Sum.inr (Sum.inr (186, 0)),
    Sum.inr (Sum.inr (251, 22)),
    Sum.inr (Sum.inr (59, 14)),
    Sum.inr (Sum.inr (113, 10)),
    Sum.inr (Sum.inr (420, 18)),
    Sum.inr (Sum.inr (431, 5)),
    Sum.inr (Sum.inr (420, 7)),
    Sum.inr (Sum.inr (420, 6)),
    Sum.inr (Sum.inr (186, 8)),
    Sum.inr (Sum.inr (59, 21)),
    Sum.inr (Sum.inr (113, 3)),
    Sum.inr (Sum.inr (251, 15)),
    Sum.inr (Sum.inr (113, 20)),
    Sum.inr (Sum.inr (186, 13)),
    Sum.inr (Sum.inr (59, 2)),
    Sum.inr (Sum.inr (251, 11)),
    Sum.inr (Sum.inr (431, 16)),
    Sum.inr (Sum.inr (431, 17)),
    Sum.inr (Sum.inr (420, 4)),
    Sum.inr (Sum.inr (431, 19)),
    Sum.inr (Sum.inr (113, 12)),
    Sum.inr (Sum.inr (59, 9)),
    Sum.inr (Sum.inr (251, 1)),
    Sum.inr (Sum.inr (186, 23)),
    Sum.inr (Sum.inr (112, 8)),
    Sum.inr (Sum.inr (49, 15)),
    Sum.inr (Sum.inr (241, 21)),
    Sum.inr (Sum.inr (187, 3)),
    Sum.inr (Sum.inr (366, 18)),
    Sum.inr (Sum.inr (357, 5)),
    Sum.inr (Sum.inr (366, 7)),
    Sum.inr (Sum.inr (366, 6)),
    Sum.inr (Sum.inr (112, 0)),
    Sum.inr (Sum.inr (241, 14)),
    Sum.inr (Sum.inr (187, 10)),
    Sum.inr (Sum.inr (49, 22)),
    Sum.inr (Sum.inr (187, 12)),
    Sum.inr (Sum.inr (112, 23)),
    Sum.inr (Sum.inr (241, 9)),
    Sum.inr (Sum.inr (49, 1)),
    Sum.inr (Sum.inr (357, 16)),
    Sum.inr (Sum.inr (357, 17)),
    Sum.inr (Sum.inr (366, 4)),
    Sum.inr (Sum.inr (357, 19)),
    Sum.inr (Sum.inr (187, 20)),
    Sum.inr (Sum.inr (241, 2)),
    Sum.inr (Sum.inr (49, 11)),
    Sum.inr (Sum.inr (112, 13)),
    Sum.inr (Sum.inl (214, 45)),
    Sum.inr (Sum.inl (208, 60)),
    Sum.inr (Sum.inl (151, 30)),
    Sum.inr (Sum.inl (174, 10)),
    Sum.inr (Sum.inl (39, 42)),
    Sum.inr (Sum.inl (19, 10)),
    Sum.inr (Sum.inl (39, 58)),
    Sum.inr (Sum.inl (39, 5)),
    Sum.inr (Sum.inl (214, 50)),
    Sum.inr (Sum.inl (151, 1)),
    Sum.inr (Sum.inl (174, 21)),
    Sum.inr (Sum.inl (208, 35)),
    Sum.inr (Sum.inl (174, 37)),
    Sum.inr (Sum.inl (214, 2)),
    Sum.inr (Sum.inl (151, 49)),
    Sum.inr (Sum.inl (208, 19)),
    Sum.inr (Sum.inl (19, 21)),
    Sum.inr (Sum.inl (19, 37)),
    Sum.inr (Sum.inl (39, 21)),
    Sum.inr (Sum.inl (19, 58)),
    Sum.inr (Sum.inl (174, 58)),
    Sum.inr (Sum.inl (151, 46)),
    Sum.inr (Sum.inl (208, 12)),
    Sum.inr (Sum.inl (214, 29)),
    Sum.inr (Sum.inl (211, 41)),
    Sum.inr (Sum.inl (205, 52)),
    Sum.inr (Sum.inl (148, 13)),
    Sum.inr (Sum.inl (171, 4)),
    Sum.inr (Sum.inl (36, 25)),
    Sum.inr (Sum.inl (16, 10)),
    Sum.inr (Sum.inl (36, 28)),
    Sum.inr (Sum.inl (36, 16)),
    Sum.inr (Sum.inl (211, 54)),
    Sum.inr (Sum.inl (148, 18)),
    Sum.inr (Sum.inl (171, 27)),
    Sum.inr (Sum.inl (205, 43)),
    Sum.inr (Sum.inl (171, 37)),
    Sum.inr (Sum.inl (211, 8)),
    Sum.inr (Sum.inl (148, 44)),
    Sum.inr (Sum.inl (205, 21)),
    Sum.inr (Sum.inl (16, 21)),
    Sum.inr (Sum.inl (16, 37)),
    Sum.inr (Sum.inl (36, 21)),
    Sum.inr (Sum.inl (16, 58)),
    Sum.inr (Sum.inl (171, 58)),
    Sum.inr (Sum.inl (148, 51)),
    Sum.inr (Sum.inl (205, 10)),
    Sum.inr (Sum.inl (211, 23)),
    Sum.inr (Sum.inl (188, 25)),
    Sum.inr (Sum.inl (187, 44)),
    Sum.inr (Sum.inl (143, 13)),
    Sum.inr (Sum.inl (166, 16)),
    Sum.inr (Sum.inl (31, 25)),
    Sum.inr (Sum.inl (11, 10)),
    Sum.inr (Sum.inl (31, 28)),
    Sum.inr (Sum.inl (31, 16)),
    Sum.inr (Sum.inl (188, 28)),
    Sum.inr (Sum.inl (143, 8)),
    Sum.inr (Sum.inl (166, 21)),
    Sum.inr (Sum.inl (187, 41)),
    Sum.inr (Sum.inl (166, 43)),
    Sum.inr (Sum.inl (188, 34)),
    Sum.inr (Sum.inl (143, 54)),
    Sum.inr (Sum.inl (187, 23)),
    Sum.inr (Sum.inl (11, 21)),
    Sum.inr (Sum.inl (11, 37)),
    Sum.inr (Sum.inl (31, 21)),
    Sum.inr (Sum.inl (11, 58)),
    Sum.inr (Sum.inl (166, 46)),
    Sum.inr (Sum.inl (143, 51)),
    Sum.inr (Sum.inl (187, 18)),
    Sum.inr (Sum.inl (188, 39)),
    Sum.inr (Sum.inl (212, 20)),
    Sum.inr (Sum.inl (206, 17)),
    Sum.inr (Sum.inl (149, 24)),
    Sum.inr (Sum.inl (172, 29)),
    Sum.inr (Sum.inl (37, 9)),
    Sum.inr (Sum.inl (17, 15)),
    Sum.inr (Sum.inl (37, 12)),
    Sum.inr (Sum.inl (37, 0)),
    Sum.inr (Sum.inl (212, 17)),
    Sum.inr (Sum.inl (149, 29)),
    Sum.inr (Sum.inl (172, 24)),
    Sum.inr (Sum.inl (206, 20)),
    Sum.inr (Sum.inl (172, 20)),
    Sum.inr (Sum.inl (212, 29)),
    Sum.inr (Sum.inl (149, 17)),
    Sum.inr (Sum.inl (206, 24)),
    Sum.inr (Sum.inl (17, 5)),
    Sum.inr (Sum.inl (17, 6)),
    Sum.inr (Sum.inl (37, 5)),
    Sum.inr (Sum.inl (17, 12)),
    Sum.inr (Sum.inl (172, 17)),
    Sum.inr (Sum.inl (149, 20)),
    Sum.inr (Sum.inl (206, 29)),
    Sum.inr (Sum.inl (212, 24)),
    Sum.inr (Sum.inr (437, 0)),
    Sum.inr (Sum.inr (500, 1)),
    Sum.inr (Sum.inr (308, 2)),
    Sum.inr (Sum.inr (382, 3)),
    Sum.inr (Sum.inr (171, 4)),
    Sum.inr (Sum.inr (160, 5)),
    Sum.inr (Sum.inr (171, 6)),
    Sum.inr (Sum.inr (171, 7)),
    Sum.inr (Sum.inr (437, 8)),
    Sum.inr (Sum.inr (308, 9)),
    Sum.inr (Sum.inr (382, 10)),
    Sum.inr (Sum.inr (500, 11)),
    Sum.inr (Sum.inr (382, 12)),
    Sum.inr (Sum.inr (437, 13)),
    Sum.inr (Sum.inr (308, 14)),
    Sum.inr (Sum.inr (500, 15)),
    Sum.inr (Sum.inr (160, 16)),
    Sum.inr (Sum.inr (160, 17)),
    Sum.inr (Sum.inr (171, 18)),
    Sum.inr (Sum.inr (160, 19)),
    Sum.inr (Sum.inr (382, 20)),
    Sum.inr (Sum.inr (308, 21)),
    Sum.inr (Sum.inr (500, 22)),
    Sum.inr (Sum.inr (437, 23)),
    Sum.inr (Sum.inr (447, 8)),
    Sum.inr (Sum.inr (510, 11)),
    Sum.inr (Sum.inr (318, 9)),
    Sum.inr (Sum.inr (372, 10)),
    Sum.inr (Sum.inr (161, 4)),
    Sum.inr (Sum.inr (170, 5)),
    Sum.inr (Sum.inr (161, 6)),
    Sum.inr (Sum.inr (161, 7)),
    Sum.inr (Sum.inr (447, 0)),
    Sum.inr (Sum.inr (318, 2)),
    Sum.inr (Sum.inr (372, 3)),
    Sum.inr (Sum.inr (510, 1)),
    Sum.inr (Sum.inr (372, 20)),
    Sum.inr (Sum.inr (447, 23)),
    Sum.inr (Sum.inr (318, 21)),
    Sum.inr (Sum.inr (510, 22)),
    Sum.inr (Sum.inr (170, 16)),
    Sum.inr (Sum.inr (170, 17)),
    Sum.inr (Sum.inr (161, 18)),
    Sum.inr (Sum.inr (170, 19)),
    Sum.inr (Sum.inr (372, 12)),
    Sum.inr (Sum.inr (318, 14)),
    Sum.inr (Sum.inr (510, 15)),
    Sum.inr (Sum.inr (447, 13)),
    Sum.inr (Sum.inr (444, 13)),
    Sum.inr (Sum.inr (509, 15)),
    Sum.inr (Sum.inr (317, 14)),
    Sum.inr (Sum.inr (375, 12)),
    Sum.inr (Sum.inr (162, 4)),
    Sum.inr (Sum.inr (169, 5)),
    Sum.inr (Sum.inr (162, 6)),
    Sum.inr (Sum.inr (162, 7))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock091Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨23296 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock091InputMaskData : ℕ :=
  sixthHex% [
    "bcf576b4f576b8fd76f0f576c00d76e00d76d00576b00d76977575a17d75",
    "ba7575cc7575abbd75b5b57592bd75ccbd75b3dd7599d575a6d575ccd575",
    "8fe5758ded758eed75cced7580f57588f57584fd75ccf575fc0d75dc0d75",
    "ec05758c0d75f47574c27d74d97574af7574c8bd74d6b574f1bd74afbd74",
    "d0dd74fad574c5d574afd574eced74eee574ede574afe574e3f574ebf574",
    "e7fd74aff5749f0574bf05748f0d74ef0574917573a77d73bc7573ca7573",
    "adb573b3bd7394b573cab573b5d5739fdd73a0dd73cadd7389e5738bed73",
    "88ed73caed7386f5738ef57382fd73caf573fa0d73da0d73ea05738a0d73",
    "f27572c47d72df7572a97572ceb572d0bd72f7b572a9b572d6d572fcdd72",
    "c3dd72a9dd72eaed72e8e572ebe572a9e572e5f572edf572e1fd72a9f572",
    "990572b90572890d72e90572ce7571f87d71e37571957571f2b571ecbd71",
    "cbb57195b571eadd71c0d571ffd57195d571d6e571d4ed71d7ed7195ed71",
    "d9f571d1f571ddfd7195f571a50571850571b50d71d50571ed7d70db7570",
    "c07d70b67d70d1bd70cfb570e8bd70b6bd70c9d570e3dd70dcdd70b6dd70",
    "f5e570f7ed70f4ed70b6ed70fafd70f2fd70fef570b6fd70860570a60570",
    "960d70f60570d35d1fe5551ffe551f88551fef951ff19d1fd6951f88951f",
    "f7fd1fddfd1fe2fd1f88f51fcbc51fc9c51fcacd1f88c51fc4d51fccd51f",
    "c0d51f88dd1fb8251f98251fa82d1fc8251fb15d1e87551e9c551eea551e",
    "8d951e939d1eb4951eea951e95fd1ebffd1e80fd1eeaf51ea9cd1eabcd1e",
    "a8c51eeacd1ea6d51eaed51ea2d51eeadd1eda2d1efa2d1eca251eaa2d1e",
    "b3551d855d1d9e5d1de85d1d8f9d1d91951db69d1de89d1d97fd1dbdfd1d",
    "82fd1de8f51dabcd1da9cd1daac51de8cd1da4dd1dacdd1da0dd1de8d51d",
    "d8251df8251dc82d1da8251d915d1ca7551cbc551cca551cad951cb39d1c",
    "94951cca951cb5f51c9ff51ca0f51ccafd1c89cd1c8bcd1c88c51ccacd1c",
    "86d51c8ed51c82d51ccadd1cfa251cda251cea2d1c8a251c8a5d1bbc551b",
    "a7551bd1551bb69d1ba8951b8f9d1bd19d1b"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock091InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock091InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock091OutputMaskData : ℕ :=
  sixthHex% [
    "dce2a2d4eaa29ca2a990eaa2ed45c7e90cfdbedfddbed6ecc0d6ef96d7de",
    "ea0cfeb84dc4a7daaafd9aa19edaaac0daaa847fdec9acfef17eefb8edc4",
    "c90fde889dc4afd4feea06efc8d2a1c0daa18892aa84daa1f975c4fd3cfe",
    "aaefdeaae6ef957ee5c37fd4bfa4f4ede5cef272a0a832abcb72a09572a0",
    "d1d7d49c04f4a4d6e5ed45ceede7d4ac75ce8b3cf4ceeee59d7aab9572ab",
    "dd3aa0d172abdd9dced9d4f48e07d48e0ee54884491e8578625e58301f62",
    "5ec80c04880767c80c39c80c7d6d7830be58086c4941ff62415d7800cf62",
    "27865862544940800748880700c00c0c8807712762756e5822bd7822b449",
    "1d2c434b2d7237f65265b7680b600651200d3260066c600628c572651652",
    "5dc44314576865b572242768036e5246bc4315280d1d200d55680659200d",
    "55cf68518652065572065c43091c405f1d7123c65171876b1f500545100e",
    "2650057850054db57100665138b44071276b00c57141576b661e5123cc40",
    "01180e09100e4158054d100e41ff6b45b651126571126c4058f4410ef570",
    "722e50206f6a4eb80414f80f77b80429b8041c5d70518e50695c4120cf6a",
    "206d7061ff6a46b65003644150f00f58f80f10b0041cf80f61576a651e50",
    "32cd7032c441c7b1e091b0d19c2bf1ce6acba0bda5fafdae99bda5c7bda5",
    "f258d1cecbf1f619e0cecacbbf28d18ffacbd9f3f1ed61e0bef5aeb6fdae",
    "8ff5a583bdaefe12cbfa5bf1ad88d1ad81e08582cad383fbde18db8c59e1",
    "e28e8fb8ce84db8e8f858e8fb06bfb8cf8dbb42aca8cf9e18c5bfbbc89e1",
    "ea80dbde12cafcc684f4ce84cdc68fc18e84cd61e1c928db9efbfb9ef2ca",
    "cfbbf899bac99421e9c660d3a8b7bdf2f7b691b7bdcfb7bd8b12c9b781e9",
    "8f53f8b780d3b722c987f0d3d1f9e9e56bf8b6ffb6bef7b687ffbd8bb7b6",
    "8758d38311e9d4c2c9d4cbf889c8d9dfc9e8d252c88013f2eec49cb48497",
    "d7c49c89c49ccd61e8f1f2c8c920d9f1f3f28011e8b0c3f2e6cac8d258d9",
    "f08c97f88497c18c9ccdc497b06bf2b422c8e3f1e8e3f8d90e7b4f587a7e",
    "55e15e07a06418370a42770121370a7f370a"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock091OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock091OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock091InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock091InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock091InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock091OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e185f7e17df8616df8e38617df8618617e185f85f85f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e185f7df95f75d86185f7df85f7df7e18617e1",
    "7e17df6e18e37e17df7e17df86185f7df7e185f7df95f75d7df7e17df85f",
    "7df7e17df85f7e17df6e18e385f8617e17df86185f86185f8617e195f75d",
    "86185f85f7df85f7df7df7e186185f95f75d85f8617df7e185f7df7df85f",
    "7df85f6e18e386185f7e18617e18617df7e186185f95f75d7e17df7df7e1",
    "85f7df8617e185f7e196175d"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock091OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock091OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block091_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock091Input a) =
      generatedSixthXiShortBlock091InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock091Output a) =
      generatedSixthXiShortBlock091OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock091Input a) =
      generatedSixthXiShortBlock091InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock091Output a) =
      generatedSixthXiShortBlock091OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block091_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock091InputMask a) =
      generatedSixthXiShortBlock091OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock091InputMask a)) *
      generatedSixthXiShortBlock091InputNumerator a =
        generatedSixthXiShortBlock091OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block091_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock091Input a
    let y := generatedSixthXiShortBlock091Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block091_cache a
  have hs := generatedSixth_xi_short_block091_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block091_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock091Input a
    let y := generatedSixthXiShortBlock091Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block091_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block091_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock091Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block091_certificate a).1
    (generatedSixth_xi_short_block091_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
