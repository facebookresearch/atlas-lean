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
def generatedSixthXiShortBlock093Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (94, 23)),
    Sum.inr (Sum.inr (31, 11)),
    Sum.inr (Sum.inr (223, 14)),
    Sum.inr (Sum.inr (149, 3)),
    Sum.inr (Sum.inr (320, 7)),
    Sum.inr (Sum.inr (331, 5)),
    Sum.inr (Sum.inr (320, 18)),
    Sum.inr (Sum.inr (320, 4)),
    Sum.inr (Sum.inr (94, 13)),
    Sum.inr (Sum.inr (223, 21)),
    Sum.inr (Sum.inr (149, 10)),
    Sum.inr (Sum.inr (31, 1)),
    Sum.inr (Sum.inr (149, 12)),
    Sum.inr (Sum.inr (94, 8)),
    Sum.inr (Sum.inr (223, 2)),
    Sum.inr (Sum.inr (31, 22)),
    Sum.inr (Sum.inr (331, 16)),
    Sum.inr (Sum.inr (331, 17)),
    Sum.inr (Sum.inr (320, 6)),
    Sum.inr (Sum.inr (331, 19)),
    Sum.inr (Sum.inr (149, 20)),
    Sum.inr (Sum.inr (223, 9)),
    Sum.inr (Sum.inr (31, 15)),
    Sum.inr (Sum.inr (94, 0)),
    Sum.inr (Sum.inr (150, 0)),
    Sum.inr (Sum.inr (215, 15)),
    Sum.inr (Sum.inr (23, 9)),
    Sum.inr (Sum.inr (93, 20)),
    Sum.inr (Sum.inr (392, 7)),
    Sum.inr (Sum.inr (387, 5)),
    Sum.inr (Sum.inr (392, 18)),
    Sum.inr (Sum.inr (392, 4)),
    Sum.inr (Sum.inr (150, 8)),
    Sum.inr (Sum.inr (23, 2)),
    Sum.inr (Sum.inr (93, 12)),
    Sum.inr (Sum.inr (215, 22)),
    Sum.inr (Sum.inr (93, 10)),
    Sum.inr (Sum.inr (150, 13)),
    Sum.inr (Sum.inr (23, 21)),
    Sum.inr (Sum.inr (215, 1)),
    Sum.inr (Sum.inr (387, 16)),
    Sum.inr (Sum.inr (387, 17)),
    Sum.inr (Sum.inr (392, 6)),
    Sum.inr (Sum.inr (387, 19)),
    Sum.inr (Sum.inr (93, 3)),
    Sum.inr (Sum.inr (23, 14)),
    Sum.inr (Sum.inr (215, 11)),
    Sum.inr (Sum.inr (150, 23)),
    Sum.inr (Sum.inr (22, 8)),
    Sum.inr (Sum.inr (87, 22)),
    Sum.inr (Sum.inr (151, 2)),
    Sum.inr (Sum.inr (221, 12)),
    Sum.inr (Sum.inr (264, 7)),
    Sum.inr (Sum.inr (259, 5)),
    Sum.inr (Sum.inr (264, 18)),
    Sum.inr (Sum.inr (264, 4)),
    Sum.inr (Sum.inr (22, 0)),
    Sum.inr (Sum.inr (151, 9)),
    Sum.inr (Sum.inr (221, 20)),
    Sum.inr (Sum.inr (87, 15)),
    Sum.inr (Sum.inr (221, 3)),
    Sum.inr (Sum.inr (22, 23)),
    Sum.inr (Sum.inr (151, 14)),
    Sum.inr (Sum.inr (87, 11)),
    Sum.inr (Sum.inr (259, 16)),
    Sum.inr (Sum.inr (259, 17)),
    Sum.inr (Sum.inr (264, 6)),
    Sum.inr (Sum.inr (259, 19)),
    Sum.inr (Sum.inr (221, 10)),
    Sum.inr (Sum.inr (151, 21)),
    Sum.inr (Sum.inr (87, 1)),
    Sum.inr (Sum.inr (22, 13)),
    Sum.inr (Sum.inl (119, 47)),
    Sum.inr (Sum.inl (118, 47)),
    Sum.inr (Sum.inl (112, 63)),
    Sum.inr (Sum.inl (114, 50)),
    Sum.inr (Sum.inl (25, 32)),
    Sum.inr (Sum.inl (5, 56)),
    Sum.inr (Sum.inl (25, 40)),
    Sum.inr (Sum.inl (25, 42)),
    Sum.inr (Sum.inl (119, 62)),
    Sum.inr (Sum.inl (112, 45)),
    Sum.inr (Sum.inl (114, 34)),
    Sum.inr (Sum.inl (118, 48)),
    Sum.inr (Sum.inl (114, 32)),
    Sum.inr (Sum.inl (119, 0)),
    Sum.inr (Sum.inl (112, 2)),
    Sum.inr (Sum.inl (118, 24)),
    Sum.inr (Sum.inl (5, 24)),
    Sum.inr (Sum.inl (5, 40)),
    Sum.inr (Sum.inl (25, 34)),
    Sum.inr (Sum.inl (5, 8)),
    Sum.inr (Sum.inl (114, 48)),
    Sum.inr (Sum.inl (112, 16)),
    Sum.inr (Sum.inl (118, 7)),
    Sum.inr (Sum.inl (119, 17)),
    Sum.inr (Sum.inl (53, 60)),
    Sum.inr (Sum.inl (52, 13)),
    Sum.inr (Sum.inl (46, 44)),
    Sum.inr (Sum.inl (48, 31)),
    Sum.inr (Sum.inl (21, 30)),
    Sum.inr (Sum.inl (1, 6)),
    Sum.inr (Sum.inl (21, 22)),
    Sum.inr (Sum.inl (21, 20)),
    Sum.inr (Sum.inl (53, 45)),
    Sum.inr (Sum.inl (46, 61)),
    Sum.inr (Sum.inl (48, 15)),
    Sum.inr (Sum.inl (52, 45)),
    Sum.inr (Sum.inl (48, 27)),
    Sum.inr (Sum.inl (53, 61)),
    Sum.inr (Sum.inl (46, 60)),
    Sum.inr (Sum.inl (52, 44)),
    Sum.inr (Sum.inl (1, 38)),
    Sum.inr (Sum.inl (1, 22)),
    Sum.inr (Sum.inl (21, 28)),
    Sum.inr (Sum.inl (1, 54)),
    Sum.inr (Sum.inl (48, 11)),
    Sum.inr (Sum.inl (46, 45)),
    Sum.inr (Sum.inl (52, 12)),
    Sum.inr (Sum.inl (53, 44)),
    Sum.inr (Sum.inl (158, 16)),
    Sum.inr (Sum.inl (157, 32)),
    Sum.inr (Sum.inl (140, 2)),
    Sum.inr (Sum.inl (153, 0)),
    Sum.inr (Sum.inl (28, 63)),
    Sum.inr (Sum.inl (8, 15)),
    Sum.inr (Sum.inl (28, 55)),
    Sum.inr (Sum.inl (28, 53)),
    Sum.inr (Sum.inl (158, 63)),
    Sum.inr (Sum.inl (140, 45)),
    Sum.inr (Sum.inl (153, 34)),
    Sum.inr (Sum.inl (157, 2)),
    Sum.inr (Sum.inl (153, 2)),
    Sum.inr (Sum.inl (158, 43)),
    Sum.inr (Sum.inl (140, 16)),
    Sum.inr (Sum.inl (157, 63)),
    Sum.inr (Sum.inl (8, 47)),
    Sum.inr (Sum.inl (8, 31)),
    Sum.inr (Sum.inl (28, 61)),
    Sum.inr (Sum.inl (8, 63)),
    Sum.inr (Sum.inl (153, 32)),
    Sum.inr (Sum.inl (140, 63)),
    Sum.inr (Sum.inl (157, 29)),
    Sum.inr (Sum.inl (158, 4)),
    Sum.inr (Sum.inl (213, 61)),
    Sum.inr (Sum.inl (207, 3)),
    Sum.inr (Sum.inl (150, 32)),
    Sum.inr (Sum.inl (173, 35)),
    Sum.inr (Sum.inl (38, 1)),
    Sum.inr (Sum.inl (18, 49)),
    Sum.inr (Sum.inl (38, 9)),
    Sum.inr (Sum.inl (38, 11)),
    Sum.inr (Sum.inl (213, 34)),
    Sum.inr (Sum.inl (150, 0)),
    Sum.inr (Sum.inl (173, 1)),
    Sum.inr (Sum.inl (207, 34)),
    Sum.inr (Sum.inl (173, 3)),
    Sum.inr (Sum.inl (213, 28)),
    Sum.inr (Sum.inl (150, 40)),
    Sum.inr (Sum.inl (207, 61)),
    Sum.inr (Sum.inl (18, 17)),
    Sum.inr (Sum.inl (18, 33)),
    Sum.inr (Sum.inl (38, 3)),
    Sum.inr (Sum.inl (18, 1)),
    Sum.inr (Sum.inl (173, 33)),
    Sum.inr (Sum.inl (150, 8)),
    Sum.inr (Sum.inl (207, 28)),
    Sum.inr (Sum.inl (213, 3)),
    Sum.inr (Sum.inr (29, 8)),
    Sum.inr (Sum.inr (92, 22)),
    Sum.inr (Sum.inr (156, 2)),
    Sum.inr (Sum.inr (214, 12)),
    Sum.inr (Sum.inr (259, 7)),
    Sum.inr (Sum.inr (264, 5)),
    Sum.inr (Sum.inr (259, 18)),
    Sum.inr (Sum.inr (259, 4)),
    Sum.inr (Sum.inr (29, 0)),
    Sum.inr (Sum.inr (156, 9)),
    Sum.inr (Sum.inr (214, 20)),
    Sum.inr (Sum.inr (92, 15)),
    Sum.inr (Sum.inr (214, 3)),
    Sum.inr (Sum.inr (29, 23)),
    Sum.inr (Sum.inr (156, 14)),
    Sum.inr (Sum.inr (92, 11)),
    Sum.inr (Sum.inr (264, 16)),
    Sum.inr (Sum.inr (264, 17)),
    Sum.inr (Sum.inr (259, 6)),
    Sum.inr (Sum.inr (264, 19)),
    Sum.inr (Sum.inr (214, 10)),
    Sum.inr (Sum.inr (156, 21)),
    Sum.inr (Sum.inr (92, 1)),
    Sum.inr (Sum.inr (29, 13)),
    Sum.inr (Sum.inr (157, 0)),
    Sum.inr (Sum.inr (220, 15)),
    Sum.inr (Sum.inr (28, 9)),
    Sum.inr (Sum.inr (86, 20)),
    Sum.inr (Sum.inr (387, 7)),
    Sum.inr (Sum.inr (392, 5)),
    Sum.inr (Sum.inr (387, 18)),
    Sum.inr (Sum.inr (387, 4)),
    Sum.inr (Sum.inr (157, 8)),
    Sum.inr (Sum.inr (28, 2)),
    Sum.inr (Sum.inr (86, 12)),
    Sum.inr (Sum.inr (220, 22)),
    Sum.inr (Sum.inr (86, 10)),
    Sum.inr (Sum.inr (157, 13)),
    Sum.inr (Sum.inr (28, 21)),
    Sum.inr (Sum.inr (220, 1)),
    Sum.inr (Sum.inr (392, 16)),
    Sum.inr (Sum.inr (392, 17)),
    Sum.inr (Sum.inr (387, 6)),
    Sum.inr (Sum.inr (392, 19)),
    Sum.inr (Sum.inr (86, 3)),
    Sum.inr (Sum.inr (28, 14)),
    Sum.inr (Sum.inr (220, 11)),
    Sum.inr (Sum.inr (157, 23)),
    Sum.inr (Sum.inr (85, 23)),
    Sum.inr (Sum.inr (20, 11)),
    Sum.inr (Sum.inr (212, 14)),
    Sum.inr (Sum.inr (158, 3)),
    Sum.inr (Sum.inr (331, 7)),
    Sum.inr (Sum.inr (320, 5)),
    Sum.inr (Sum.inr (331, 18)),
    Sum.inr (Sum.inr (331, 4)),
    Sum.inr (Sum.inr (85, 13)),
    Sum.inr (Sum.inr (212, 21)),
    Sum.inr (Sum.inr (158, 10)),
    Sum.inr (Sum.inr (20, 1)),
    Sum.inr (Sum.inr (158, 12)),
    Sum.inr (Sum.inr (85, 8)),
    Sum.inr (Sum.inr (212, 2)),
    Sum.inr (Sum.inr (20, 22)),
    Sum.inr (Sum.inr (320, 16)),
    Sum.inr (Sum.inr (320, 17)),
    Sum.inr (Sum.inr (331, 6)),
    Sum.inr (Sum.inr (320, 19)),
    Sum.inr (Sum.inr (158, 20)),
    Sum.inr (Sum.inr (212, 9)),
    Sum.inr (Sum.inr (20, 15)),
    Sum.inr (Sum.inr (85, 0)),
    Sum.inr (Sum.inr (222, 13)),
    Sum.inr (Sum.inr (159, 1)),
    Sum.inr (Sum.inr (95, 21)),
    Sum.inr (Sum.inr (21, 10)),
    Sum.inr (Sum.inr (448, 7)),
    Sum.inr (Sum.inr (459, 5)),
    Sum.inr (Sum.inr (448, 18)),
    Sum.inr (Sum.inr (448, 4)),
    Sum.inr (Sum.inr (222, 23)),
    Sum.inr (Sum.inr (95, 14)),
    Sum.inr (Sum.inr (21, 3)),
    Sum.inr (Sum.inr (159, 11)),
    Sum.inr (Sum.inr (21, 20)),
    Sum.inr (Sum.inr (222, 0)),
    Sum.inr (Sum.inr (95, 9)),
    Sum.inr (Sum.inr (159, 15))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock093Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨23808 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock093InputMaskData : ℕ :=
  sixthHex% [
    "bdd5ab97d5aba8ddabc2d5ab81e5ab83edab80e5abc2e5ab8efdab86f5ab",
    "8afdabc2fdabf20dabd20dabe205ab820dabb87daa8e7daa9575aae37daa",
    "84b5aa9abdaabdb5aae3b5aa9cddaab6ddaa89d5aae3ddaaa0e5aaa2edaa",
    "a1e5aae3e5aaaff5aaa7fdaaabf5aae3f5aad30daaf30daac305aaa30daa",
    "937da9a57da9be75a9c87da9afb5a9b1bda996b5a9c8b5a9b7d5a99dd5a9",
    "a2dda9c8d5a98beda989e5a98aeda9c8eda984f5a98cfda980f5a9c8f5a9",
    "f80da9d80da9e805a9880da9f27da8c47da8df75a8a97da8ceb5a8d0bda8",
    "f7b5a8a9b5a8d6d5a8fcd5a8c3dda8a9d5a8eae5a8e8eda8ebe5a8a9e5a8",
    "e5f5a8edfda8e1f5a8a9f5a89905a8b905a8890da8e905a8967da7a07da7",
    "bb75a7cd7da7aab5a7b4bda793b5a7cdb5a7b2d5a798d5a7a7dda7cdd5a7",
    "8ee5a78ceda78fe5a7cde5a781fda789f5a785fda7cdfda7fd0da7dd0da7",
    "ed05a78d0da7b775a68175a69a7da6ec75a68bbda695b5a6b2bda6ecbda6",
    "93dda6b9dda686d5a6ecdda6afe5a6adeda6aee5a6ece5a6a0f5a6a8fda6",
    "a4f5a6ecf5a6dc0da6fc0da6cc05a6ac0da69c75a5aa75a5b17da5c775a5",
    "a0bda5beb5a599bda5c7bda5b8d5a592d5a5addda5c7d5a584eda586e5a5",
    "85eda5c7eda58bf5a583fda58ff5a5c7f5a5f70da5d70da5e705a5870da5",
    "fd75a4cb75a4d07da4a675a4c1bda4dfb5a4f8bda4a6bda4d9d5a4f3d5a4",
    "ccdda4a6d5a4e5e5a4e7eda4e4e5a4a6e5a4eaf5a4e2fda4eef5a4a6f5a4",
    "9605a4b605a4860da4e605a48f75a3b975a3a27da3d475a3b3b5a3adbda3",
    "8ab5a3d4b5a3abdda381dda3bed5a3d4dda397eda395e5a396eda3d4eda3",
    "98f5a390fda39cf5a3d4f5a3e40da3c40da3f405a3940da3ee75a2d875a2",
    "c37da2b575a2d2b5a2ccbda2ebb5a2b5b5a2cadda2e0dda2dfd5a2b5dda2",
    "f6e5a2f4eda2f7e5a2b5e5a2f9f5a2f1fda2fdf5a2b5f5a28505a2a505a2",
    "950da2f505a2c575a1f375a1e87da19e75a1f9b5a1e7bda1c0b5a19eb5a1",
    "e1d5a1cbd5a1f4dda19ed5a1ddeda1dfe5a1dceda19eeda1d2f5a1dafda1",
    "d6f5a19ef5a1ae05a18e05a1be0da1de05a1"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock093InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock093InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock093OutputMaskData : ℕ :=
  sixthHex% [
    "fc4a7fc0d95f894b4eb19865c07a7f81e865d7e15f92334eb0e700c9af00",
    "81e70bfcef00f00065f4495fa39a7fa3934ea899558fd864f30344d0027e",
    "cf951095d51bf69510a895109d7064a1e344e87155d0a27ed0006491927e",
    "c79b44824955d1dd1ba8951be0dd109dd51be07a7ee43344b3e064b3e955",
    "883a7daf7b4cd3a06cf0a156ef3638b57633d63638883638cc934cf0006c",
    "b9927d81415681e34cc0715696786cd3aa7df17e33883633c07e38bd7633",
    "c0d956c4906c93434c934a7ded406dca015cb6da7c95db468a4c28d00c23",
    "b34c28ed4c28a9e95c957a7cdce86de43b4695d95cd44b4682427cc7906d",
    "940423ed4c23a50428d80c23d4e346d0aa7c87795c87706d2882c20fc3f3",
    "7318d35019e94f8e8715ce8c768e87288e876c2bf350b8d3192ac221f9e9",
    "501bf31189e94780d30252c220868c59ce8c1186876c8e8c6061e96428d3",
    "33fbf333f2c249b8d96ef9e81222c83123f22eb49c74f49717b49c49b49c",
    "0d11e83182c87810d940c3f24061e801f3f257fac81228d941bc9738f497",
    "70bc9c0db497701bf27452c82381e82388d9691bf14e5ac03281e01180da",
    "0e17b45457bf3717b46917b45cf2c06061e029f3f11120da1182c05010da",
    "0619e043cbf1611fbf1857bf501fb42d17bf50b8da54f1e00322c0032bf1",
    "0c61e12b20d057fbf074faca6b6da4312daf526da40c6da43988d0051bf0",
    "4c89e1745aca05b8d0442aca1223f057f1e10465af7d2daf3565a4486daf",
    "4482ca40cbf01718d01711e1e50866c24957be92779d934df34423a90428",
    "ca4423944423a1a1579d3277d4a066ec734d9d9157dc034d8a0a77cfd866",
    "ed0c28944428dc0c23a10428dcab4dd8e2778f31578f3866807276a73347",
    "dbe867f8e95d963e33cc7e38af3e33f13e33c4db47f84867b1da7689095d",
    "89ab47c8395d9e3067dbe276887638f13e38b97633c47e38c8915dccd867",
    "9b0b479b0276a0d15e87906ffb4b4fd84a75b69d1becdd108f9d1bd19d1b",
    "95386fa9ab4fe0395ed8ea75d8486f99da75cfd34f8a015ea8d510d19d10",
    "99d51be4dd10e83275ec7b4fbba86fbba15e"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock093OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock093OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock093InputNumeratorData : ℕ :=
  sixthHex% [
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock093InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock093InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock093OutputNumeratorData : ℕ :=
  sixthHex% [
    "85f7e17df8617df7df7e17e17e185f6df8e37df8617e17e186186185f7e1",
    "7e17e16df8e385f7e18617df8618617e17e17e185f6df8e38617df7e17e1",
    "8618617e185f8617e195f75d7df7e185f7df85f7df86185f7df7e16e18e3",
    "85f86186185f7e18617df85f8617e195f75d86185f85f7df85f7df7df7e1",
    "7df7e16e18e37e17df86185f7e18618617e185f7e196175d7df86185f85f",
    "7df7df85f7e185f85f96175d7e185f7df8617df7df85f85f85f7e196175d",
    "8617df85f85f7df7df7e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock093OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock093OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block093_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock093Input a) =
      generatedSixthXiShortBlock093InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock093Output a) =
      generatedSixthXiShortBlock093OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock093Input a) =
      generatedSixthXiShortBlock093InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock093Output a) =
      generatedSixthXiShortBlock093OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block093_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock093InputMask a) =
      generatedSixthXiShortBlock093OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock093InputMask a)) *
      generatedSixthXiShortBlock093InputNumerator a =
        generatedSixthXiShortBlock093OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block093_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock093Input a
    let y := generatedSixthXiShortBlock093Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block093_cache a
  have hs := generatedSixth_xi_short_block093_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block093_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock093Input a
    let y := generatedSixthXiShortBlock093Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block093_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block093_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock093Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block093_certificate a).1
    (generatedSixth_xi_short_block093_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
