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
def generatedSixthXiShortBlock099Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (158, 23)),
    Sum.inr (Sum.inr (223, 11)),
    Sum.inr (Sum.inr (31, 14)),
    Sum.inr (Sum.inr (85, 3)),
    Sum.inr (Sum.inr (384, 7)),
    Sum.inr (Sum.inr (395, 5)),
    Sum.inr (Sum.inr (384, 18)),
    Sum.inr (Sum.inr (384, 4)),
    Sum.inr (Sum.inr (158, 13)),
    Sum.inr (Sum.inr (31, 21)),
    Sum.inr (Sum.inr (85, 10)),
    Sum.inr (Sum.inr (223, 1)),
    Sum.inr (Sum.inr (85, 12)),
    Sum.inr (Sum.inr (158, 8)),
    Sum.inr (Sum.inr (31, 2)),
    Sum.inr (Sum.inr (223, 22)),
    Sum.inr (Sum.inr (395, 16)),
    Sum.inr (Sum.inr (395, 17)),
    Sum.inr (Sum.inr (384, 6)),
    Sum.inr (Sum.inr (395, 19)),
    Sum.inr (Sum.inr (85, 20)),
    Sum.inr (Sum.inr (31, 9)),
    Sum.inr (Sum.inr (223, 15)),
    Sum.inr (Sum.inr (158, 0)),
    Sum.inr (Sum.inr (86, 0)),
    Sum.inr (Sum.inr (23, 15)),
    Sum.inr (Sum.inr (215, 9)),
    Sum.inr (Sum.inr (157, 20)),
    Sum.inr (Sum.inr (328, 7)),
    Sum.inr (Sum.inr (323, 5)),
    Sum.inr (Sum.inr (328, 18)),
    Sum.inr (Sum.inr (328, 4)),
    Sum.inr (Sum.inr (86, 8)),
    Sum.inr (Sum.inr (215, 2)),
    Sum.inr (Sum.inr (157, 12)),
    Sum.inr (Sum.inr (23, 22)),
    Sum.inr (Sum.inr (157, 10)),
    Sum.inr (Sum.inr (86, 13)),
    Sum.inr (Sum.inr (215, 21)),
    Sum.inr (Sum.inr (23, 1)),
    Sum.inr (Sum.inr (323, 16)),
    Sum.inr (Sum.inr (323, 17)),
    Sum.inr (Sum.inr (328, 6)),
    Sum.inr (Sum.inr (323, 19)),
    Sum.inr (Sum.inr (157, 3)),
    Sum.inr (Sum.inr (215, 14)),
    Sum.inr (Sum.inr (23, 11)),
    Sum.inr (Sum.inr (86, 23)),
    Sum.inr (Sum.inr (214, 8)),
    Sum.inr (Sum.inr (151, 22)),
    Sum.inr (Sum.inr (87, 2)),
    Sum.inr (Sum.inr (29, 12)),
    Sum.inr (Sum.inr (456, 7)),
    Sum.inr (Sum.inr (451, 5)),
    Sum.inr (Sum.inr (456, 18)),
    Sum.inr (Sum.inr (456, 4)),
    Sum.inr (Sum.inr (214, 0)),
    Sum.inr (Sum.inr (87, 9)),
    Sum.inr (Sum.inr (29, 20)),
    Sum.inr (Sum.inr (151, 15)),
    Sum.inr (Sum.inr (29, 3)),
    Sum.inr (Sum.inr (214, 23)),
    Sum.inr (Sum.inr (87, 14)),
    Sum.inr (Sum.inr (151, 11)),
    Sum.inr (Sum.inr (451, 16)),
    Sum.inr (Sum.inr (451, 17)),
    Sum.inr (Sum.inr (456, 6)),
    Sum.inr (Sum.inr (451, 19)),
    Sum.inr (Sum.inr (29, 10)),
    Sum.inr (Sum.inr (87, 21)),
    Sum.inr (Sum.inr (151, 1)),
    Sum.inr (Sum.inr (214, 13)),
    Sum.inr (Sum.inl (119, 45)),
    Sum.inr (Sum.inl (118, 56)),
    Sum.inr (Sum.inl (112, 19)),
    Sum.inr (Sum.inl (114, 12)),
    Sum.inr (Sum.inl (25, 30)),
    Sum.inr (Sum.inl (5, 6)),
    Sum.inr (Sum.inl (25, 22)),
    Sum.inr (Sum.inl (25, 20)),
    Sum.inr (Sum.inl (119, 60)),
    Sum.inr (Sum.inl (112, 1)),
    Sum.inr (Sum.inl (114, 28)),
    Sum.inr (Sum.inl (118, 39)),
    Sum.inr (Sum.inl (114, 30)),
    Sum.inr (Sum.inl (119, 2)),
    Sum.inr (Sum.inl (112, 46)),
    Sum.inr (Sum.inl (118, 15)),
    Sum.inr (Sum.inl (5, 38)),
    Sum.inr (Sum.inl (5, 22)),
    Sum.inr (Sum.inl (25, 28)),
    Sum.inr (Sum.inl (5, 54)),
    Sum.inr (Sum.inl (114, 14)),
    Sum.inr (Sum.inl (112, 60)),
    Sum.inr (Sum.inl (118, 16)),
    Sum.inr (Sum.inl (119, 19)),
    Sum.inr (Sum.inl (53, 35)),
    Sum.inr (Sum.inl (52, 60)),
    Sum.inr (Sum.inl (46, 29)),
    Sum.inr (Sum.inl (48, 55)),
    Sum.inr (Sum.inl (21, 46)),
    Sum.inr (Sum.inl (1, 10)),
    Sum.inr (Sum.inl (21, 38)),
    Sum.inr (Sum.inl (21, 36)),
    Sum.inr (Sum.inl (53, 50)),
    Sum.inr (Sum.inl (46, 12)),
    Sum.inr (Sum.inl (48, 39)),
    Sum.inr (Sum.inl (52, 28)),
    Sum.inr (Sum.inl (48, 51)),
    Sum.inr (Sum.inl (53, 34)),
    Sum.inr (Sum.inl (46, 13)),
    Sum.inr (Sum.inl (52, 29)),
    Sum.inr (Sum.inl (1, 42)),
    Sum.inr (Sum.inl (1, 26)),
    Sum.inr (Sum.inl (21, 44)),
    Sum.inr (Sum.inl (1, 58)),
    Sum.inr (Sum.inl (48, 35)),
    Sum.inr (Sum.inl (46, 28)),
    Sum.inr (Sum.inl (52, 61)),
    Sum.inr (Sum.inl (53, 51)),
    Sum.inr (Sum.inl (158, 56)),
    Sum.inr (Sum.inl (157, 45)),
    Sum.inr (Sum.inl (140, 15)),
    Sum.inr (Sum.inl (153, 47)),
    Sum.inr (Sum.inl (28, 15)),
    Sum.inr (Sum.inl (8, 3)),
    Sum.inr (Sum.inl (28, 7)),
    Sum.inr (Sum.inl (28, 5)),
    Sum.inr (Sum.inl (158, 23)),
    Sum.inr (Sum.inl (140, 32)),
    Sum.inr (Sum.inl (153, 13)),
    Sum.inr (Sum.inl (157, 15)),
    Sum.inr (Sum.inl (153, 45)),
    Sum.inr (Sum.inl (158, 3)),
    Sum.inr (Sum.inl (140, 29)),
    Sum.inr (Sum.inl (157, 50)),
    Sum.inr (Sum.inl (8, 35)),
    Sum.inr (Sum.inl (8, 19)),
    Sum.inr (Sum.inl (28, 13)),
    Sum.inr (Sum.inl (8, 51)),
    Sum.inr (Sum.inl (153, 15)),
    Sum.inr (Sum.inl (140, 50)),
    Sum.inr (Sum.inl (157, 16)),
    Sum.inr (Sum.inl (158, 44)),
    Sum.inr (Sum.inl (213, 63)),
    Sum.inr (Sum.inl (207, 31)),
    Sum.inr (Sum.inl (150, 55)),
    Sum.inr (Sum.inl (173, 29)),
    Sum.inr (Sum.inl (38, 63)),
    Sum.inr (Sum.inl (18, 15)),
    Sum.inr (Sum.inl (38, 55)),
    Sum.inr (Sum.inl (38, 53)),
    Sum.inr (Sum.inl (213, 32)),
    Sum.inr (Sum.inl (150, 23)),
    Sum.inr (Sum.inl (173, 63)),
    Sum.inr (Sum.inl (207, 62)),
    Sum.inr (Sum.inl (173, 61)),
    Sum.inr (Sum.inl (213, 30)),
    Sum.inr (Sum.inl (150, 63)),
    Sum.inr (Sum.inl (207, 33)),
    Sum.inr (Sum.inl (18, 47)),
    Sum.inr (Sum.inl (18, 31)),
    Sum.inr (Sum.inl (38, 61)),
    Sum.inr (Sum.inl (18, 63)),
    Sum.inr (Sum.inl (173, 31)),
    Sum.inr (Sum.inl (150, 31)),
    Sum.inr (Sum.inl (207, 0)),
    Sum.inr (Sum.inl (213, 1)),
    Sum.inr (Sum.inr (221, 8)),
    Sum.inr (Sum.inr (156, 22)),
    Sum.inr (Sum.inr (92, 2)),
    Sum.inr (Sum.inr (22, 12)),
    Sum.inr (Sum.inr (451, 7)),
    Sum.inr (Sum.inr (456, 5)),
    Sum.inr (Sum.inr (451, 18)),
    Sum.inr (Sum.inr (451, 4)),
    Sum.inr (Sum.inr (221, 0)),
    Sum.inr (Sum.inr (92, 9)),
    Sum.inr (Sum.inr (22, 20)),
    Sum.inr (Sum.inr (156, 15)),
    Sum.inr (Sum.inr (22, 3)),
    Sum.inr (Sum.inr (221, 23)),
    Sum.inr (Sum.inr (92, 14)),
    Sum.inr (Sum.inr (156, 11)),
    Sum.inr (Sum.inr (456, 16)),
    Sum.inr (Sum.inr (456, 17)),
    Sum.inr (Sum.inr (451, 6)),
    Sum.inr (Sum.inr (456, 19)),
    Sum.inr (Sum.inr (22, 10)),
    Sum.inr (Sum.inr (92, 21)),
    Sum.inr (Sum.inr (156, 1)),
    Sum.inr (Sum.inr (221, 13)),
    Sum.inr (Sum.inr (93, 0)),
    Sum.inr (Sum.inr (28, 15)),
    Sum.inr (Sum.inr (220, 9)),
    Sum.inr (Sum.inr (150, 20)),
    Sum.inr (Sum.inr (323, 7)),
    Sum.inr (Sum.inr (328, 5)),
    Sum.inr (Sum.inr (323, 18)),
    Sum.inr (Sum.inr (323, 4)),
    Sum.inr (Sum.inr (93, 8)),
    Sum.inr (Sum.inr (220, 2)),
    Sum.inr (Sum.inr (150, 12)),
    Sum.inr (Sum.inr (28, 22)),
    Sum.inr (Sum.inr (150, 10)),
    Sum.inr (Sum.inr (93, 13)),
    Sum.inr (Sum.inr (220, 21)),
    Sum.inr (Sum.inr (28, 1)),
    Sum.inr (Sum.inr (328, 16)),
    Sum.inr (Sum.inr (328, 17)),
    Sum.inr (Sum.inr (323, 6)),
    Sum.inr (Sum.inr (328, 19)),
    Sum.inr (Sum.inr (150, 3)),
    Sum.inr (Sum.inr (220, 14)),
    Sum.inr (Sum.inr (28, 11)),
    Sum.inr (Sum.inr (93, 23)),
    Sum.inr (Sum.inr (149, 23)),
    Sum.inr (Sum.inr (212, 11)),
    Sum.inr (Sum.inr (20, 14)),
    Sum.inr (Sum.inr (94, 3)),
    Sum.inr (Sum.inr (395, 7)),
    Sum.inr (Sum.inr (384, 5)),
    Sum.inr (Sum.inr (395, 18)),
    Sum.inr (Sum.inr (395, 4)),
    Sum.inr (Sum.inr (149, 13)),
    Sum.inr (Sum.inr (20, 21)),
    Sum.inr (Sum.inr (94, 10)),
    Sum.inr (Sum.inr (212, 1)),
    Sum.inr (Sum.inr (94, 12)),
    Sum.inr (Sum.inr (149, 8)),
    Sum.inr (Sum.inr (20, 2)),
    Sum.inr (Sum.inr (212, 22)),
    Sum.inr (Sum.inr (384, 16)),
    Sum.inr (Sum.inr (384, 17)),
    Sum.inr (Sum.inr (395, 6)),
    Sum.inr (Sum.inr (384, 19)),
    Sum.inr (Sum.inr (94, 20)),
    Sum.inr (Sum.inr (20, 9)),
    Sum.inr (Sum.inr (212, 15)),
    Sum.inr (Sum.inr (149, 0)),
    Sum.inr (Sum.inr (30, 13)),
    Sum.inr (Sum.inr (95, 1)),
    Sum.inr (Sum.inr (159, 21)),
    Sum.inr (Sum.inr (213, 10)),
    Sum.inr (Sum.inr (256, 7)),
    Sum.inr (Sum.inr (267, 5)),
    Sum.inr (Sum.inr (256, 18)),
    Sum.inr (Sum.inr (256, 4)),
    Sum.inr (Sum.inr (30, 23)),
    Sum.inr (Sum.inr (159, 14)),
    Sum.inr (Sum.inr (213, 3)),
    Sum.inr (Sum.inr (95, 11)),
    Sum.inr (Sum.inr (213, 20)),
    Sum.inr (Sum.inr (30, 0)),
    Sum.inr (Sum.inr (159, 9)),
    Sum.inr (Sum.inr (95, 15))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock099Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨25344 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock099InputMaskData : ℕ :=
  sixthHex% [
    "93e68bb9e68b86e68becee8bafd68badd68baed68becde8ba0c68ba8ce8b",
    "a4c68becc68bdc368bfc3e8bcc368bac368ba74e8a91468a8a4e8afc4e8a",
    "9b868a858e8aa2868afc868a83e68aa9e68a96e68afcee8abfde8abdde8a",
    "bede8afcd68ab0c68ab8ce8ab4c68afcc68acc3e8aec368adc3e8abc3e8a",
    "a74e899146898a4e89fc4e899b8689858e89a28689fc868983ee89a9ee89",
    "96ee89fce689bfd689bdd689bed689fcde89b0c689b8ce89b4c689fcc689",
    "cc3e89ec3689dc3e89bc3e89f74688c14e88da4688ac4688cb8e88d58688",
    "f28e88ac8e88d3e688f9e688c6e688acee88efd688edd688eed688acde88",
    "e0ce88e8c688e4ce88acce889c3e88bc36888c3e88ec3e88a34687954e87",
    "8e4687f846879f8e87818687a68e87f88e8787e687ade68792e687f8ee87",
    "bbd687b9d687bad687f8de87b4c687bcce87b0c687f8c687c83687e83e87",
    "d83687b83687b34686854e869e4686e846868f8e86918686b68e86e88e86",
    "97e686bde68682e686e8ee86abde86a9de86aade86e8d686a4c686acce86",
    "a0c686e8c686d83e86f83686c83e86a83e86b34685854e859e4685e84685",
    "8f8e85918685b68e85e88e8597ee85bdee8582ee85e8e685abd685a9d685",
    "aad685e8de85a4c685acce85a0c685e8c685d83e85f83685c83e85a83e85",
    "e34e84d54684ce4e84b84e84df8684c18e84e68684b88684c7e684ede684",
    "d2e684b8ee84fbd684f9d684fad684b8de84f4ce84fcc684f0ce84b8ce84",
    "883e84a83684983e84f83e848a4e83bc4683a74e83d14e83b68e83a88683",
    "8f8e83d18e83aeee8384ee83bbee83d1e68392de8390de8393de83d1d683",
    "9dce8395c68399ce83d1ce83e13683c13e83f13683913683da4682ec4e82",
    "f74682814682e68682f88e82df8682818682fee682d4e682ebe68281ee82",
    "c2de82c0de82c3de8281d682cdc682c5ce82c9c68281c682b13682913e82",
    "a13682c13682da4681ec4e81f74681814681e68681f88e81df8681818681",
    "feee81d4ee81ebee8181e681c2d681c0d681c3d68181de81cdc681c5ce81",
    "c9c68181c681b13681913e81a13681c13681"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock099InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock099InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock099OutputMaskData : ℕ :=
  sixthHex% [
    "fde15fc1727ff9a06ec17345c1d15ff10345d64a7fe2d86ec00c20b94420",
    "f10c2b8c042080eb45f5e27fa2315fd3786e983a75ce3b44b2e064e0a15e",
    "ff3630a5763bc63630983630dc9344e00064d8d275e0015e91e344a1315e",
    "867864b2ea75e17e3b98363bd07e30ad763bd0d95ea5d064f20344834a75",
    "93915dc5906cb94b4ceb0a76f49d18aedd13cd9d18939d18a6786c9aeb4c",
    "a2395d9aea76eb086cdbda76fc934cc8015dead513939d13dbd518a6dd13",
    "db7276ae7b4cf9a86c88e15db6a34de0a27c9c795cce3866d1af088bef03",
    "e8af08b6af08834a7cbfd95c870b4dbfd866bf7a7c8fa866a8e15c9c734d",
    "cfe703b6af03fee70883ef038f0066fa095cadda7cdc934d55f2c203f3f3",
    "7f28d32d69e932fe8768be8c0bfe8755fe87601bf35c88d3645ac25c89e9",
    "5c2bf36cf9e94bb0d37f22c25df68c24be8c6cf68711fe8c1d11e96818d3",
    "3fcbf34e82c27480d92281e85e5ac80c1bf2138c9c49cc972a8c9c748c9c",
    "4169e87dfac84528d97dfbf20c19e83ccbf21b82c82f10d97c849705cc97",
    "4d849c308c974d23f2382ac86ff9e81eb0d97f2bf1292ac055f1e007b0da",
    "1827b44267bf2127b47f27b43b82c00711e03fc3f10710da76f2c04620da",
    "6169e055fbf1772fbf0e67bf462fb43b27bf4688da3381e06452c0151bf1",
    "5a19e10c18d070c3f02282ca3d15a46755af0415a45a15a41eb0d02223f0",
    "1af1e12222ca2280d01252ca351bf00189e1521daf2b55af631da41e15af",
    "12faca67f3f03020d04169e1beeb46e8ea77943157c6706da8a703f2e708",
    "91a703cfa7038b0277b791578f4346b7906db7327787e06da0a957943b46",
    "b6ef08cfa70887ef03fae70887486df24157a59277d4db469bd956cdd867",
    "b10347e3427d8d9513d7d518b49513ea9513ae306792a347aa715692a27d",
    "e34067d3927df4db47c0495693dd18ea9518a2dd13dfd518d33a7da63347",
    "f1e06780a95690727ec6734fbaa86fe8e955863e3bdc7e30bf3e3be13e3b",
    "d4db4fe8486fd09a7ee8495599ab4fa979558e306fbaa27e987630e13e30",
    "a9763bd47e30d89155ad986ffa4b4f8b027e"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock099OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock099OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock099InputNumeratorData : ℕ :=
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
def generatedSixthXiShortBlock099InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock099InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock099OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f8617df86186185f85f7e185f6df8e37df8617e17e186186185f7e1",
    "85f85f96175d7e185f7df8617df7df85f85f7e185f6df8e38617df7e17e1",
    "8618617e185f8617e195f75d7df7e185f7df85f7df86185f86185f95f75d",
    "7e17df7df7e185f7df8617e18617e195f75d86185f85f7df85f7df7df7e1",
    "86185f95f75d85f8617df7e185f7df7df85f85f7e196175d7df86185f85f",
    "7df7df85f7e17e17e16df8e385f7e18617df8618617e17e185f7e196175d",
    "8617df85f85f7df7df7e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock099OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock099OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block099_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock099Input a) =
      generatedSixthXiShortBlock099InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock099Output a) =
      generatedSixthXiShortBlock099OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock099Input a) =
      generatedSixthXiShortBlock099InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock099Output a) =
      generatedSixthXiShortBlock099OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block099_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock099InputMask a) =
      generatedSixthXiShortBlock099OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock099InputMask a)) *
      generatedSixthXiShortBlock099InputNumerator a =
        generatedSixthXiShortBlock099OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block099_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock099Input a
    let y := generatedSixthXiShortBlock099Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block099_cache a
  have hs := generatedSixth_xi_short_block099_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block099_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock099Input a
    let y := generatedSixthXiShortBlock099Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block099_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block099_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock099Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block099_certificate a).1
    (generatedSixth_xi_short_block099_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
