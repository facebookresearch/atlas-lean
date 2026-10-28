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
def generatedSixthXiShortBlock107Output : Fin 232 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (104, 53)),
    Sum.inr (Sum.inl (97, 40)),
    Sum.inr (Sum.inl (99, 23)),
    Sum.inr (Sum.inl (103, 42)),
    Sum.inr (Sum.inl (99, 21)),
    Sum.inr (Sum.inl (104, 17)),
    Sum.inr (Sum.inl (97, 7)),
    Sum.inr (Sum.inl (103, 23)),
    Sum.inr (Sum.inl (4, 41)),
    Sum.inr (Sum.inl (4, 25)),
    Sum.inr (Sum.inl (24, 37)),
    Sum.inr (Sum.inl (4, 57)),
    Sum.inr (Sum.inl (99, 7)),
    Sum.inr (Sum.inl (97, 21)),
    Sum.inr (Sum.inl (103, 8)),
    Sum.inr (Sum.inl (104, 14)),
    Sum.inr (Sum.inl (179, 53)),
    Sum.inr (Sum.inl (178, 42)),
    Sum.inr (Sum.inl (142, 54)),
    Sum.inr (Sum.inl (165, 9)),
    Sum.inr (Sum.inl (30, 54)),
    Sum.inr (Sum.inl (10, 12)),
    Sum.inr (Sum.inl (30, 60)),
    Sum.inr (Sum.inl (30, 62)),
    Sum.inr (Sum.inl (179, 26)),
    Sum.inr (Sum.inl (142, 20)),
    Sum.inr (Sum.inl (165, 43)),
    Sum.inr (Sum.inl (178, 53)),
    Sum.inr (Sum.inl (165, 11)),
    Sum.inr (Sum.inl (179, 36)),
    Sum.inr (Sum.inl (142, 41)),
    Sum.inr (Sum.inl (178, 29)),
    Sum.inr (Sum.inl (10, 44)),
    Sum.inr (Sum.inl (10, 28)),
    Sum.inr (Sum.inl (30, 52)),
    Sum.inr (Sum.inl (10, 60)),
    Sum.inr (Sum.inl (165, 41)),
    Sum.inr (Sum.inl (142, 11)),
    Sum.inr (Sum.inl (178, 2)),
    Sum.inr (Sum.inl (179, 11)),
    Sum.inr (Sum.inr (77, 8)),
    Sum.inr (Sum.inr (12, 1)),
    Sum.inr (Sum.inr (204, 14)),
    Sum.inr (Sum.inr (134, 20)),
    Sum.inr (Sum.inr (339, 6)),
    Sum.inr (Sum.inr (344, 5)),
    Sum.inr (Sum.inr (339, 4)),
    Sum.inr (Sum.inr (339, 18)),
    Sum.inr (Sum.inr (77, 0)),
    Sum.inr (Sum.inr (204, 21)),
    Sum.inr (Sum.inr (134, 12)),
    Sum.inr (Sum.inr (12, 11)),
    Sum.inr (Sum.inr (134, 10)),
    Sum.inr (Sum.inr (77, 23)),
    Sum.inr (Sum.inr (204, 2)),
    Sum.inr (Sum.inr (12, 15)),
    Sum.inr (Sum.inr (344, 16)),
    Sum.inr (Sum.inr (344, 17)),
    Sum.inr (Sum.inr (339, 7)),
    Sum.inr (Sum.inr (344, 19)),
    Sum.inr (Sum.inr (134, 3)),
    Sum.inr (Sum.inr (204, 9)),
    Sum.inr (Sum.inr (12, 22)),
    Sum.inr (Sum.inr (77, 13)),
    Sum.inr (Sum.inr (13, 0)),
    Sum.inr (Sum.inr (76, 11)),
    Sum.inr (Sum.inr (140, 21)),
    Sum.inr (Sum.inr (198, 12)),
    Sum.inr (Sum.inr (275, 6)),
    Sum.inr (Sum.inr (280, 5)),
    Sum.inr (Sum.inr (275, 4)),
    Sum.inr (Sum.inr (275, 18)),
    Sum.inr (Sum.inr (13, 8)),
    Sum.inr (Sum.inr (140, 14)),
    Sum.inr (Sum.inr (198, 20)),
    Sum.inr (Sum.inr (76, 1)),
    Sum.inr (Sum.inr (198, 3)),
    Sum.inr (Sum.inr (13, 13)),
    Sum.inr (Sum.inr (140, 9)),
    Sum.inr (Sum.inr (76, 22)),
    Sum.inr (Sum.inr (280, 16)),
    Sum.inr (Sum.inr (280, 17)),
    Sum.inr (Sum.inr (275, 7)),
    Sum.inr (Sum.inr (280, 19)),
    Sum.inr (Sum.inr (198, 10)),
    Sum.inr (Sum.inr (140, 2)),
    Sum.inr (Sum.inr (76, 15)),
    Sum.inr (Sum.inr (13, 23)),
    Sum.inr (Sum.inr (143, 23)),
    Sum.inr (Sum.inr (206, 15)),
    Sum.inr (Sum.inr (14, 2)),
    Sum.inr (Sum.inr (68, 10)),
    Sum.inr (Sum.inr (401, 6)),
    Sum.inr (Sum.inr (410, 5)),
    Sum.inr (Sum.inr (401, 4)),
    Sum.inr (Sum.inr (401, 18)),
    Sum.inr (Sum.inr (143, 13)),
    Sum.inr (Sum.inr (14, 9)),
    Sum.inr (Sum.inr (68, 3)),
    Sum.inr (Sum.inr (206, 22)),
    Sum.inr (Sum.inr (68, 20)),
    Sum.inr (Sum.inr (143, 8)),
    Sum.inr (Sum.inr (14, 14)),
    Sum.inr (Sum.inr (206, 1)),
    Sum.inr (Sum.inr (410, 16)),
    Sum.inr (Sum.inr (410, 17)),
    Sum.inr (Sum.inr (401, 7)),
    Sum.inr (Sum.inr (410, 19)),
    Sum.inr (Sum.inr (68, 12)),
    Sum.inr (Sum.inr (14, 21)),
    Sum.inr (Sum.inr (206, 11)),
    Sum.inr (Sum.inr (143, 0)),
    Sum.inr (Sum.inr (196, 13)),
    Sum.inr (Sum.inr (133, 22)),
    Sum.inr (Sum.inr (69, 9)),
    Sum.inr (Sum.inr (15, 3)),
    Sum.inr (Sum.inr (474, 6)),
    Sum.inr (Sum.inr (465, 5)),
    Sum.inr (Sum.inr (474, 4)),
    Sum.inr (Sum.inr (474, 18)),
    Sum.inr (Sum.inr (196, 23)),
    Sum.inr (Sum.inr (69, 2)),
    Sum.inr (Sum.inr (15, 10)),
    Sum.inr (Sum.inr (133, 15)),
    Sum.inr (Sum.inr (15, 12)),
    Sum.inr (Sum.inr (196, 0)),
    Sum.inr (Sum.inr (69, 21)),
    Sum.inr (Sum.inr (133, 11)),
    Sum.inr (Sum.inr (465, 16)),
    Sum.inr (Sum.inr (465, 17)),
    Sum.inr (Sum.inr (474, 7)),
    Sum.inr (Sum.inr (465, 19)),
    Sum.inr (Sum.inr (15, 20)),
    Sum.inr (Sum.inr (69, 14)),
    Sum.inr (Sum.inr (133, 1)),
    Sum.inr (Sum.inr (196, 8)),
    Sum.inr (Sum.inl (179, 57)),
    Sum.inr (Sum.inl (178, 41)),
    Sum.inr (Sum.inl (142, 58)),
    Sum.inr (Sum.inl (165, 5)),
    Sum.inr (Sum.inl (30, 56)),
    Sum.inr (Sum.inl (10, 62)),
    Sum.inr (Sum.inl (30, 50)),
    Sum.inr (Sum.inl (30, 48)),
    Sum.inr (Sum.inl (179, 22)),
    Sum.inr (Sum.inl (142, 24)),
    Sum.inr (Sum.inl (165, 39)),
    Sum.inr (Sum.inl (178, 54)),
    Sum.inr (Sum.inl (165, 7)),
    Sum.inr (Sum.inl (179, 40)),
    Sum.inr (Sum.inl (142, 37)),
    Sum.inr (Sum.inl (178, 30)),
    Sum.inr (Sum.inl (10, 30)),
    Sum.inr (Sum.inl (10, 46)),
    Sum.inr (Sum.inl (30, 58)),
    Sum.inr (Sum.inl (10, 14)),
    Sum.inr (Sum.inl (165, 37)),
    Sum.inr (Sum.inl (142, 7)),
    Sum.inr (Sum.inl (178, 1)),
    Sum.inr (Sum.inl (179, 7)),
    Sum.inr (Sum.inl (104, 41)),
    Sum.inr (Sum.inl (103, 57)),
    Sum.inr (Sum.inl (97, 54)),
    Sum.inr (Sum.inl (99, 9)),
    Sum.inr (Sum.inl (24, 41)),
    Sum.inr (Sum.inl (4, 59)),
    Sum.inr (Sum.inl (24, 35)),
    Sum.inr (Sum.inl (24, 33)),
    Sum.inr (Sum.inl (104, 54)),
    Sum.inr (Sum.inl (97, 36)),
    Sum.inr (Sum.inl (99, 27)),
    Sum.inr (Sum.inl (103, 38)),
    Sum.inr (Sum.inl (99, 25)),
    Sum.inr (Sum.inl (104, 18)),
    Sum.inr (Sum.inl (97, 11)),
    Sum.inr (Sum.inl (103, 27)),
    Sum.inr (Sum.inl (4, 27)),
    Sum.inr (Sum.inl (4, 43)),
    Sum.inr (Sum.inl (24, 43)),
    Sum.inr (Sum.inl (4, 11)),
    Sum.inr (Sum.inl (99, 11)),
    Sum.inr (Sum.inl (97, 25)),
    Sum.inr (Sum.inl (103, 4)),
    Sum.inr (Sum.inl (104, 13)),
    Sum.inr (Sum.inl (215, 58)),
    Sum.inr (Sum.inl (209, 58)),
    Sum.inr (Sum.inl (152, 26)),
    Sum.inr (Sum.inl (175, 9)),
    Sum.inr (Sum.inl (40, 25)),
    Sum.inr (Sum.inl (20, 55)),
    Sum.inr (Sum.inl (40, 19)),
    Sum.inr (Sum.inl (40, 17)),
    Sum.inr (Sum.inl (215, 43)),
    Sum.inr (Sum.inl (152, 10)),
    Sum.inr (Sum.inl (175, 25)),
    Sum.inr (Sum.inl (209, 27)),
    Sum.inr (Sum.inl (175, 27)),
    Sum.inr (Sum.inl (215, 59)),
    Sum.inr (Sum.inl (152, 30)),
    Sum.inr (Sum.inl (209, 26)),
    Sum.inr (Sum.inl (20, 23)),
    Sum.inr (Sum.inl (20, 39)),
    Sum.inr (Sum.inl (40, 27)),
    Sum.inr (Sum.inl (20, 7)),
    Sum.inr (Sum.inl (175, 11)),
    Sum.inr (Sum.inl (152, 14)),
    Sum.inr (Sum.inl (209, 59)),
    Sum.inr (Sum.inl (215, 42)),
    Sum.inr (Sum.inl (71, 9)),
    Sum.inr (Sum.inl (70, 9)),
    Sum.inr (Sum.inl (64, 9)),
    Sum.inr (Sum.inl (66, 26)),
    Sum.inr (Sum.inl (22, 8)),
    Sum.inr (Sum.inl (2, 50)),
    Sum.inr (Sum.inl (22, 2)),
    Sum.inr (Sum.inl (22, 0)),
    Sum.inr (Sum.inl (71, 24)),
    Sum.inr (Sum.inl (64, 41)),
    Sum.inr (Sum.inl (66, 10)),
    Sum.inr (Sum.inl (70, 40)),
    Sum.inr (Sum.inl (66, 18)),
    Sum.inr (Sum.inl (71, 38)),
    Sum.inr (Sum.inl (64, 40)),
    Sum.inr (Sum.inl (70, 55)),
    Sum.inr (Sum.inl (2, 18)),
    Sum.inr (Sum.inl (2, 34)),
    Sum.inr (Sum.inl (22, 10)),
    Sum.inr (Sum.inl (2, 2)),
    Sum.inr (Sum.inl (66, 2)),
    Sum.inr (Sum.inl (64, 8)),
    Sum.inr (Sum.inl (70, 22)),
    Sum.inr (Sum.inl (71, 55))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock107Input (a : Fin 232) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨27392 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock107InputMaskData : ℕ :=
  sixthHex% [
    "c077dff67fdfed77df9b77dffcb7dfe2bfdfc5b7df9bb7dfe4d7dfced7df",
    "f1dfdf9bd7dfd8e7dfdae7dfd9efdf9be7dfd7f7dfdfffdfd3ffdf9bffdf",
    "ab0fdf8b07dfbb07dfdb07dfb277de847fde9f77dee977de8eb7de90bfde",
    "b7b7dee9b7de96d7debcd7de83dfdee9d7deaaefdea8efdeabe7dee9efde",
    "a5f7deadffdea1ffdee9ffded907def90fdec90fdea90fde9a77ddac7fdd",
    "b777ddc177dda6b7ddb8bfdd9fb7ddc1b7ddbedfdd94dfddabd7ddc1dfdd",
    "82e7dd80e7dd83efddc1e7dd8df7dd85ffdd89ffddc1ffddf107ddd10fdd",
    "e10fdd810fdda87fdc9e77dc857fdcf37fdc94bfdc8ab7dcadbfdcf3bfdc",
    "8cd7dca6d7dc99dfdcf3d7dcb0e7dcb2e7dcb1efdcf3e7dcbfffdcb7f7dc",
    "bbf7dcf3f7dcc307dce30fdcd30fdcb30fdc8977dbbf7fdba477dbd277db",
    "b5bfdbabb7db8cbfdbd2bfdbadd7db87d7dbb8dfdbd2d7db91e7db93e7db",
    "90efdbd2e7db9ef7db96ffdb9affdbd2ffdbe207dbc20fdbf20fdb920fdb",
    "bb7fda8d77da967fdae07fda87b7da99bfdabeb7dae0b7da9fdfdab5dfda",
    "8ad7dae0dfdaa3e7daa1e7daa2efdae0e7daacffdaa4f7daa8f7dae0f7da",
    "d007daf00fdac00fdaa00fda937fd9a577d9be7fd9c87fd9afb7d9b1bfd9",
    "96b7d9c8b7d9b7d7d99dd7d9a2dfd9c8d7d98befd989efd98ae7d9c8efd9",
    "84ffd98cf7d980f7d9c8f7d9f807d9d80fd9e80fd9880fd9e17fd8d777d8",
    "cc7fd8ba7fd8ddb7d8c3bfd8e4b7d8bab7d8c5d7d8efd7d8d0dfd8bad7d8",
    "f9e7d8fbe7d8f8efd8bae7d8f6ffd8fef7d8f2f7d8baf7d88a0fd8aa07d8",
    "9a07d8fa07d89d7fd7ab77d7b07fd7c67fd7a1b7d7bfbfd798b7d7c6b7d7",
    "b9d7d793d7d7acdfd7c6d7d785e7d787e7d784efd7c6e7d78af7d782ffd7",
    "8effd7c6ffd7f607d7d60fd7e60fd7860fd7af77d6997fd68277d6f477d6",
    "93bfd68db7d6aabfd6f4bfd68bdfd6a1dfd69ed7d6f4dfd6b7e7d6b5e7d6",
    "b6efd6f4e7d6"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock107InputMask (a : Fin 232) : ℕ :=
  (generatedSixthXiShortBlock107InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock107OutputMaskData : ℕ :=
  sixthHex% [
    "5303910502a079d9802b98ba454fd41f0fdf7c4fd4224fd466eaa05a7980",
    "13eb912b38ba5adaa06a08ba3c01800893915b07df224fdf1b47d4664fdf",
    "6aa0ba1fa980393aa048739133eaa165eb901930b04b718a25a6e47fe6ef",
    "1ca6e442a6e40603903a90b07302a14bd18a4b73907ba18a2da8b0193aa1",
    "3beeef42a6ef7baee406a6ef7b098a0e00b028939059daa13400b3620182",
    "1edaa24c9b98224cf6780cfd1b4cf6454cf670a9824c3aa205a8b33d7b98",
    "3dd9820d0b985b02a26f90b33c04fd454cfd7c44f6014cfd7ce39809eaa2",
    "2f79825e30b350a98806a8b97a73992832a346e5cd1ca5c67fe5cd21e5cd",
    "1400b928939961018859d2a32830b918e2a34eeb997a798858adc621e5c6",
    "18edcd65e5c6690aa31c03993a90b94bd988b81324ee121592c935c0880f",
    "df1f61855f6ae61f61b81f618dfa15b16935f8fb24c0280fb1ca1581180f",
    "d71135e38324b0176ac95f6af057618d5f6af0f00f85f935a36a15d22324",
    "dcba1f8abb2ef6600ea42134bbb65ae1f65182b65adcb65ae9532ed5c00e",
    "9c521fa48134a4232e94f134c2f80ef66a1fd4be51adf65194fe5ae9f651",
    "e5193490100eb6832ec7ca1fdb500d8d513cf18a1ca3cb26bc5c48e61c43",
    "855c48db5c489ff93ca36a1ceaf80dd22b26d2893ce25b26b4521c80c00d",
    "d35443aa1c43931448ee1c43e2f32697fa1cb1693cc0200dbbb93dedb80c",
    "91632cc32216dcb57886f573e5b578bbb578ff100cc3832c8a113db2c216",
    "c3200cf3f216a5fb2c91693db3bd73caf573f3fd788ef573f35a1686532c",
    "a0c00cd1893d54a98802a8b97e73992c32a333a5cd69e5c60aa5cd54a5cd",
    "1000b92c93996501885dd2a32c30b91ce2a34aeb997e79882dedc654a5c6",
    "6dadcd10a5c66d0aa31803993e90b94fd9883000b36601821adaa2489b98",
    "570cf60d4cfd6e0cf6300cf674a982483aa201a8b3397b9839d982090b98",
    "5f02a26b90b3"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock107OutputMask (a : Fin 232) : ℕ :=
  (generatedSixthXiShortBlock107OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock107InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e186186196175d7e185f85f7e1",
    "85f7e17e185f86186196175d7e185f85f7e185f7e17e185f7df7df6df8e3",
    "85f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f86186196175d7e185f85f7e1",
    "85f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e3",
    "85f7e17e185f7e185f85f7e186186196175d7e185f85f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock107InputNumerator (a : Fin 232) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock107InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock107OutputNumeratorData : ℕ :=
  sixthHex% [
    "86186196175d7e185f85f7e185f7e17e185f8617df96175d7df8617df7df",
    "85f7e17e17e17df7df6df8e37e185f7e185f7e185f7e185f7df8616df8e3",
    "7df8618618617e185f7e17e17e17df6e18e385f8617e17df86185f86185f",
    "7e18616e18e386185f8617e186185f8617e17e17df6e18e37e17df7e17df",
    "86185f7df7e185f7df95f75d86185f7df85f7df7e18617e17df8616df8e3",
    "7df8618618617e185f7e17e17df7df6df8e37e185f7e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock107OutputNumerator (a : Fin 232) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock107OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block107_cache (a : Fin 232) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock107Input a) =
      generatedSixthXiShortBlock107InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock107Output a) =
      generatedSixthXiShortBlock107OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock107Input a) =
      generatedSixthXiShortBlock107InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock107Output a) =
      generatedSixthXiShortBlock107OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block107_scalar (a : Fin 232) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock107InputMask a) =
      generatedSixthXiShortBlock107OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock107InputMask a)) *
      generatedSixthXiShortBlock107InputNumerator a =
        generatedSixthXiShortBlock107OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block107_folded_certificate (a : Fin 232) :
    let x := generatedSixthXiShortBlock107Input a
    let y := generatedSixthXiShortBlock107Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block107_cache a
  have hs := generatedSixth_xi_short_block107_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block107_certificate (a : Fin 232) :
    let x := generatedSixthXiShortBlock107Input a
    let y := generatedSixthXiShortBlock107Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block107_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block107_signed (a : Fin 232) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock107Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block107_certificate a).1
    (generatedSixth_xi_short_block107_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
