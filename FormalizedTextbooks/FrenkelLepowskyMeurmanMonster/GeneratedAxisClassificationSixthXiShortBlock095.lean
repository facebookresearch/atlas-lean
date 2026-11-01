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
def generatedSixthXiShortBlock095Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (179, 20)),
    Sum.inr (Sum.inl (142, 25)),
    Sum.inr (Sum.inl (165, 4)),
    Sum.inr (Sum.inl (178, 33)),
    Sum.inr (Sum.inl (165, 36)),
    Sum.inr (Sum.inl (179, 42)),
    Sum.inr (Sum.inl (142, 36)),
    Sum.inr (Sum.inl (178, 9)),
    Sum.inr (Sum.inl (10, 32)),
    Sum.inr (Sum.inl (10, 16)),
    Sum.inr (Sum.inl (30, 4)),
    Sum.inr (Sum.inl (10, 48)),
    Sum.inr (Sum.inl (165, 6)),
    Sum.inr (Sum.inl (142, 6)),
    Sum.inr (Sum.inl (178, 22)),
    Sum.inr (Sum.inl (179, 5)),
    Sum.inr (Sum.inl (104, 49)),
    Sum.inr (Sum.inl (103, 52)),
    Sum.inr (Sum.inl (97, 22)),
    Sum.inr (Sum.inl (99, 59)),
    Sum.inr (Sum.inl (24, 25)),
    Sum.inr (Sum.inl (4, 55)),
    Sum.inr (Sum.inl (24, 19)),
    Sum.inr (Sum.inl (24, 17)),
    Sum.inr (Sum.inl (104, 46)),
    Sum.inr (Sum.inl (97, 4)),
    Sum.inr (Sum.inl (99, 41)),
    Sum.inr (Sum.inl (103, 43)),
    Sum.inr (Sum.inl (99, 43)),
    Sum.inr (Sum.inl (104, 10)),
    Sum.inr (Sum.inl (97, 43)),
    Sum.inr (Sum.inl (103, 22)),
    Sum.inr (Sum.inl (4, 23)),
    Sum.inr (Sum.inl (4, 39)),
    Sum.inr (Sum.inl (24, 27)),
    Sum.inr (Sum.inl (4, 7)),
    Sum.inr (Sum.inl (99, 57)),
    Sum.inr (Sum.inl (97, 57)),
    Sum.inr (Sum.inl (103, 9)),
    Sum.inr (Sum.inl (104, 21)),
    Sum.inr (Sum.inr (140, 0)),
    Sum.inr (Sum.inr (205, 11)),
    Sum.inr (Sum.inr (13, 21)),
    Sum.inr (Sum.inr (71, 12)),
    Sum.inr (Sum.inr (402, 6)),
    Sum.inr (Sum.inr (409, 5)),
    Sum.inr (Sum.inr (402, 4)),
    Sum.inr (Sum.inr (402, 18)),
    Sum.inr (Sum.inr (140, 8)),
    Sum.inr (Sum.inr (13, 14)),
    Sum.inr (Sum.inr (71, 20)),
    Sum.inr (Sum.inr (205, 1)),
    Sum.inr (Sum.inr (71, 3)),
    Sum.inr (Sum.inr (140, 13)),
    Sum.inr (Sum.inr (13, 9)),
    Sum.inr (Sum.inr (205, 22)),
    Sum.inr (Sum.inr (409, 16)),
    Sum.inr (Sum.inr (409, 17)),
    Sum.inr (Sum.inr (402, 7)),
    Sum.inr (Sum.inr (409, 19)),
    Sum.inr (Sum.inr (71, 10)),
    Sum.inr (Sum.inr (13, 2)),
    Sum.inr (Sum.inr (205, 15)),
    Sum.inr (Sum.inr (140, 23)),
    Sum.inr (Sum.inr (204, 8)),
    Sum.inr (Sum.inr (141, 1)),
    Sum.inr (Sum.inr (77, 14)),
    Sum.inr (Sum.inr (7, 20)),
    Sum.inr (Sum.inr (466, 6)),
    Sum.inr (Sum.inr (473, 5)),
    Sum.inr (Sum.inr (466, 4)),
    Sum.inr (Sum.inr (466, 18)),
    Sum.inr (Sum.inr (204, 0)),
    Sum.inr (Sum.inr (77, 21)),
    Sum.inr (Sum.inr (7, 12)),
    Sum.inr (Sum.inr (141, 11)),
    Sum.inr (Sum.inr (7, 10)),
    Sum.inr (Sum.inr (204, 23)),
    Sum.inr (Sum.inr (77, 2)),
    Sum.inr (Sum.inr (141, 15)),
    Sum.inr (Sum.inr (473, 16)),
    Sum.inr (Sum.inr (473, 17)),
    Sum.inr (Sum.inr (466, 7)),
    Sum.inr (Sum.inr (473, 19)),
    Sum.inr (Sum.inr (7, 3)),
    Sum.inr (Sum.inr (77, 9)),
    Sum.inr (Sum.inr (141, 22)),
    Sum.inr (Sum.inr (204, 13)),
    Sum.inr (Sum.inr (69, 13)),
    Sum.inr (Sum.inr (4, 22)),
    Sum.inr (Sum.inr (196, 9)),
    Sum.inr (Sum.inr (142, 3)),
    Sum.inr (Sum.inr (347, 6)),
    Sum.inr (Sum.inr (336, 5)),
    Sum.inr (Sum.inr (347, 4)),
    Sum.inr (Sum.inr (347, 18)),
    Sum.inr (Sum.inr (69, 23)),
    Sum.inr (Sum.inr (196, 2)),
    Sum.inr (Sum.inr (142, 10)),
    Sum.inr (Sum.inr (4, 15)),
    Sum.inr (Sum.inr (142, 12)),
    Sum.inr (Sum.inr (69, 0)),
    Sum.inr (Sum.inr (196, 21)),
    Sum.inr (Sum.inr (4, 11)),
    Sum.inr (Sum.inr (336, 16)),
    Sum.inr (Sum.inr (336, 17)),
    Sum.inr (Sum.inr (347, 7)),
    Sum.inr (Sum.inr (336, 19)),
    Sum.inr (Sum.inr (142, 20)),
    Sum.inr (Sum.inr (196, 14)),
    Sum.inr (Sum.inr (4, 1)),
    Sum.inr (Sum.inr (69, 8)),
    Sum.inr (Sum.inr (14, 23)),
    Sum.inr (Sum.inr (79, 15)),
    Sum.inr (Sum.inr (143, 2)),
    Sum.inr (Sum.inr (197, 10)),
    Sum.inr (Sum.inr (272, 6)),
    Sum.inr (Sum.inr (283, 5)),
    Sum.inr (Sum.inr (272, 4)),
    Sum.inr (Sum.inr (272, 18)),
    Sum.inr (Sum.inr (14, 13)),
    Sum.inr (Sum.inr (143, 9)),
    Sum.inr (Sum.inr (197, 3)),
    Sum.inr (Sum.inr (79, 22)),
    Sum.inr (Sum.inr (197, 20)),
    Sum.inr (Sum.inr (14, 8)),
    Sum.inr (Sum.inr (143, 14)),
    Sum.inr (Sum.inr (79, 1)),
    Sum.inr (Sum.inr (283, 16)),
    Sum.inr (Sum.inr (283, 17)),
    Sum.inr (Sum.inr (272, 7)),
    Sum.inr (Sum.inr (283, 19)),
    Sum.inr (Sum.inr (197, 12)),
    Sum.inr (Sum.inr (143, 21)),
    Sum.inr (Sum.inr (79, 11)),
    Sum.inr (Sum.inr (14, 0)),
    Sum.inr (Sum.inl (104, 50)),
    Sum.inr (Sum.inl (103, 56)),
    Sum.inr (Sum.inl (97, 26)),
    Sum.inr (Sum.inl (99, 55)),
    Sum.inr (Sum.inl (24, 23)),
    Sum.inr (Sum.inl (4, 5)),
    Sum.inr (Sum.inl (24, 29)),
    Sum.inr (Sum.inl (24, 31)),
    Sum.inr (Sum.inl (104, 45)),
    Sum.inr (Sum.inl (97, 8)),
    Sum.inr (Sum.inl (99, 37)),
    Sum.inr (Sum.inl (103, 39)),
    Sum.inr (Sum.inl (99, 39)),
    Sum.inr (Sum.inl (104, 9)),
    Sum.inr (Sum.inl (97, 39)),
    Sum.inr (Sum.inl (103, 26)),
    Sum.inr (Sum.inl (4, 37)),
    Sum.inr (Sum.inl (4, 21)),
    Sum.inr (Sum.inl (24, 21)),
    Sum.inr (Sum.inl (4, 53)),
    Sum.inr (Sum.inl (99, 53)),
    Sum.inr (Sum.inl (97, 53)),
    Sum.inr (Sum.inl (103, 5)),
    Sum.inr (Sum.inl (104, 22)),
    Sum.inr (Sum.inl (179, 55)),
    Sum.inr (Sum.inl (178, 61)),
    Sum.inr (Sum.inl (142, 55)),
    Sum.inr (Sum.inl (165, 42)),
    Sum.inr (Sum.inl (30, 8)),
    Sum.inr (Sum.inl (10, 50)),
    Sum.inr (Sum.inl (30, 2)),
    Sum.inr (Sum.inl (30, 0)),
    Sum.inr (Sum.inl (179, 24)),
    Sum.inr (Sum.inl (142, 21)),
    Sum.inr (Sum.inl (165, 8)),
    Sum.inr (Sum.inl (178, 34)),
    Sum.inr (Sum.inl (165, 40)),
    Sum.inr (Sum.inl (179, 38)),
    Sum.inr (Sum.inl (142, 40)),
    Sum.inr (Sum.inl (178, 10)),
    Sum.inr (Sum.inl (10, 18)),
    Sum.inr (Sum.inl (10, 34)),
    Sum.inr (Sum.inl (30, 10)),
    Sum.inr (Sum.inl (10, 2)),
    Sum.inr (Sum.inl (165, 10)),
    Sum.inr (Sum.inl (142, 10)),
    Sum.inr (Sum.inl (178, 21)),
    Sum.inr (Sum.inl (179, 9)),
    Sum.inr (Sum.inl (71, 7)),
    Sum.inr (Sum.inl (70, 25)),
    Sum.inr (Sum.inl (64, 56)),
    Sum.inr (Sum.inl (66, 62)),
    Sum.inr (Sum.inl (22, 56)),
    Sum.inr (Sum.inl (2, 62)),
    Sum.inr (Sum.inl (22, 50)),
    Sum.inr (Sum.inl (22, 48)),
    Sum.inr (Sum.inl (71, 22)),
    Sum.inr (Sum.inl (64, 24)),
    Sum.inr (Sum.inl (66, 46)),
    Sum.inr (Sum.inl (70, 56)),
    Sum.inr (Sum.inl (66, 54)),
    Sum.inr (Sum.inl (71, 40)),
    Sum.inr (Sum.inl (64, 25)),
    Sum.inr (Sum.inl (70, 39)),
    Sum.inr (Sum.inl (2, 30)),
    Sum.inr (Sum.inl (2, 46)),
    Sum.inr (Sum.inl (22, 58)),
    Sum.inr (Sum.inl (2, 14)),
    Sum.inr (Sum.inl (66, 38)),
    Sum.inr (Sum.inl (64, 57)),
    Sum.inr (Sum.inl (70, 6)),
    Sum.inr (Sum.inl (71, 57)),
    Sum.inr (Sum.inl (215, 41)),
    Sum.inr (Sum.inl (209, 7)),
    Sum.inr (Sum.inl (152, 49)),
    Sum.inr (Sum.inl (175, 55)),
    Sum.inr (Sum.inl (40, 39)),
    Sum.inr (Sum.inl (20, 9)),
    Sum.inr (Sum.inl (40, 45)),
    Sum.inr (Sum.inl (40, 47)),
    Sum.inr (Sum.inl (215, 56)),
    Sum.inr (Sum.inl (152, 33)),
    Sum.inr (Sum.inl (175, 39)),
    Sum.inr (Sum.inl (209, 38)),
    Sum.inr (Sum.inl (175, 37)),
    Sum.inr (Sum.inl (215, 40)),
    Sum.inr (Sum.inl (152, 53)),
    Sum.inr (Sum.inl (209, 39)),
    Sum.inr (Sum.inl (20, 41)),
    Sum.inr (Sum.inl (20, 25)),
    Sum.inr (Sum.inl (40, 37)),
    Sum.inr (Sum.inl (20, 57)),
    Sum.inr (Sum.inl (175, 53)),
    Sum.inr (Sum.inl (152, 37)),
    Sum.inr (Sum.inl (209, 6)),
    Sum.inr (Sum.inl (215, 57)),
    Sum.inr (Sum.inl (133, 63)),
    Sum.inr (Sum.inl (132, 32)),
    Sum.inr (Sum.inl (126, 33)),
    Sum.inr (Sum.inl (128, 39)),
    Sum.inr (Sum.inl (26, 55)),
    Sum.inr (Sum.inl (6, 15)),
    Sum.inr (Sum.inl (26, 63)),
    Sum.inr (Sum.inl (26, 51)),
    Sum.inr (Sum.inl (133, 16)),
    Sum.inr (Sum.inl (126, 0)),
    Sum.inr (Sum.inl (128, 55)),
    Sum.inr (Sum.inl (132, 1)),
    Sum.inr (Sum.inl (128, 47)),
    Sum.inr (Sum.inl (133, 46)),
    Sum.inr (Sum.inl (126, 32)),
    Sum.inr (Sum.inl (132, 63)),
    Sum.inr (Sum.inl (6, 47)),
    Sum.inr (Sum.inl (6, 31)),
    Sum.inr (Sum.inl (26, 59)),
    Sum.inr (Sum.inl (6, 63)),
    Sum.inr (Sum.inl (128, 63)),
    Sum.inr (Sum.inl (126, 1)),
    Sum.inr (Sum.inl (132, 30)),
    Sum.inr (Sum.inl (133, 1))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock095Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨24320 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock095InputMaskData : ℕ :=
  sixthHex% [
    "c3fe30f5fe30eefe3098f630ff3630e13e30c63630983630e75630cd5630",
    "f25e30985630db6e30d96630da6630986630d47e30dc7e30d07e30987630",
    "a88e30888630b88e30d88e30d6e5cfe0e5cffbe5cf8dedcfea2dcff425cf",
    "d32dcf8d2dcff24dcfd845cfe74dcf8d4dcfce75cfcc75cfcf75cf8d7dcf",
    "c16dcfc965cfc565cf8d65cfbd9dcf9d9dcfad95cfcd9dcfb6edce80edce",
    "9bedceede5ce8a25ce942dceb325ceed25ce9245ceb84dce8745ceed45ce",
    "ae75ceac75ceaf75ceed7dcea165cea96dcea56dceed6dcedd9dcefd9dce",
    "cd95cead9dcea3e5cd95e5cd8ee5cdf8edcd9f2dcd8125cda62dcdf82dcd",
    "8745cdad4dcd9245cdf845cdbb75cdb975cdba75cdf87dcdb46dcdbc65cd",
    "b065cdf865cdc895cde895cdd89dcdb895cd83e5ccb5e5ccaee5ccd8edcc",
    "bf2dcca125cc862dccd82dcca745cc8d4dccb245ccd845cc9b7dcc997dcc",
    "9a7dccd875cc946dcc9c65cc9065ccd865cce89dccc89dccf895cc989dcc",
    "8fe5cbb9e5cba2e5cbd4edcbb325cbad2dcb8a25cbd425cbab4dcb8145cb",
    "be4dcbd44dcb9775cb9575cb9675cbd47dcb986dcb9065cb9c65cbd465cb",
    "e495cbc495cbf49dcb9495cbafe5ca99e5ca82e5caf4edca9325ca8d2dca",
    "aa25caf425ca8b4dcaa145ca9e4dcaf44dcab77dcab57dcab67dcaf475ca",
    "b86dcab065cabc65caf465cac49dcae49dcad495cab49dcabaedc98cedc9",
    "97edc9e1e5c9862dc99825c9bf2dc9e12dc99e4dc9b445c98b4dc9e14dc9",
    "a27dc9a07dc9a37dc9e175c9ad65c9a56dc9a96dc9e16dc9d195c9f195c9",
    "c19dc9a195c9dae5c8ece5c8f7e5c881edc8e625c8f82dc8df25c88125c8",
    "fe45c8d44dc8eb45c88145c8c27dc8c07dc8c37dc88175c8cd6dc8c565c8",
    "c965c88165c8b195c89195c8a19dc8c195c8b6e5c780e5c79be5c7ededc7",
    "8a25c7942dc7b325c7ed25c79245c7b84dc78745c7ed45c7ae7dc7ac7dc7",
    "af7dc7ed75c7a165c7a96dc7a56dc7ed6dc7dd9dc7fd9dc7cd95c7ad9dc7",
    "96e5c6a0e5c6bbe5c6cdedc6aa25c6b42dc69325c6cd25c6b245c6984dc6",
    "a745c6cd45c68e75c68c75c68f75c6cd7dc6"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock095InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock095InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock095OutputMaskData : ℕ :=
  sixthHex% [
    "4fd34f68927e65095e46086428df0a729f0111df0a4fdf0a0b7a7e37e95e",
    "7e7b4f46a864460a7e07986420d15e65034f47d7014fdf0176d70a7a9f01",
    "07306472395e25ea7e54a34f09daa12e9b902300b000018a6ed6e43496ef",
    "57d6e409d6e44d739000a0b04932a100a18a00039030d18a1798b0230aa1",
    "709eef09d6ef30dee44dd6ef30798a3430b063e39063eaa10a7b912d3aa0",
    "20a18003a0ba6d77d43737df5477d40a77d44ed2a00301804a93910300ba",
    "72e2a04230ba65798051eb91733fdf0a77df337fd44e77df4298ba46d180",
    "1102a0110b9174d1885390b95e0b997d0aa313ddcd499dc62addcd74ddcd",
    "4138b90ceb994579880ceaa37d08b94ddaa36a93995e01880d95c674ddc6",
    "4dd5cd30ddc63c32a3387b996fa8b96fa1887330b354718259eaa27aeb98",
    "143cf64e7cfd2d3cf6733cf646d9820b0aa24298b30b0b980ba9823b7b98",
    "1c32a228a0b30a74fd733cfd4a34f6373cfd4a93984edaa21909821900b3",
    "c0100ee7513feaca1fc9cb25d65c4b8c1c40ef5c4bb15c4b84b93fc96a1f",
    "80f80ec96b25c9c93ff91b25de521feac00eb95440c01c40f9144b841c40",
    "88f3258cba1fdb693fdb600ec7f135e0b004ed2b24ce2a1ed1bd708bfd7b",
    "e8bd70b6bd70835804ce8b24871935ce8a1ebf68048fba1ea8f3249c6135",
    "beb57bc7fd7bfef57083fd7bfe521efa1b24adc804adc135b95b2c9e1a1d",
    "93813db08007af1769f55762961769c817698cb21dc1613d88f32cc16007",
    "b0821d805007a7193d938b2cc01f62b95762805f69fd576280f80784b13d",
    "d3621dd36b2cbafa1c9dbb2d90200db32137acb659f6f65295b659cbb659",
    "8f132dc2c00d8b521cc2c137c2632df2b137d5f80de16a1cc3be52baf652",
    "83fe59fef652f21937f6500da1832da18a1c7730b35071825deaa27eeb98",
    "617cf63b3cfd587cf6067cf642d9820f0aa24698b30f0b980fa9823f7b98",
    "1832a22ca0b37f34fd067cfd3f74f6427cfd4e93984adaa21d09821d00b3",
    "70d1885790b95a0b99790aa3669dcd3cddc65f9dcd019dcd4538b908eb99",
    "41798808eaa37908b949daa36e93995a0188"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock095OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock095OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock095InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock095InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock095InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock095OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e196175d8617df85f85f7df7df7e185f8617df96175d7df8617df7df",
    "85f7e17e17e186186196175d7e185f85f7e185f7e17e185f8617df96175d",
    "8617df7df7df85f7e185f85f86186196175d85f7e185f7e185f7e185f7e1",
    "7e18616e18e386185f8617e186185f8617e17e17df6e18e385f8617e17df",
    "86185f86185f85f7df95f75d86185f7df85f7df7e18617e17e17df6e18e3",
    "7e17df7e17df86185f7df7e186186196175d85f7e185f7e185f7e185f7e1",
    "8617df96175d8617df7df7df"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock095OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock095OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block095_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock095Input a) =
      generatedSixthXiShortBlock095InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock095Output a) =
      generatedSixthXiShortBlock095OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock095Input a) =
      generatedSixthXiShortBlock095InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock095Output a) =
      generatedSixthXiShortBlock095OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block095_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock095InputMask a) =
      generatedSixthXiShortBlock095OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock095InputMask a)) *
      generatedSixthXiShortBlock095InputNumerator a =
        generatedSixthXiShortBlock095OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block095_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock095Input a
    let y := generatedSixthXiShortBlock095Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block095_cache a
  have hs := generatedSixth_xi_short_block095_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block095_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock095Input a
    let y := generatedSixthXiShortBlock095Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block095_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block095_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock095Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block095_certificate a).1
    (generatedSixth_xi_short_block095_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
