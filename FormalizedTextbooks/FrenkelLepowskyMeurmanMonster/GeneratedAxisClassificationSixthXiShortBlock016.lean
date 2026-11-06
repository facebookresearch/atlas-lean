/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortNumbering
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiCombinedMaskPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressMaskEight

/-! Original sparse masks and full signed phases certify a bounded part of actual short support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Candidate sparse outputs are checked against the original full binary and phase action. -/
def generatedSixthXiShortBlock016Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (72, 39)),
    Sum.inr (Sum.inl (155, 1)),
    Sum.inr (Sum.inl (72, 43)),
    Sum.inr (Sum.inl (155, 3)),
    Sum.inr (Sum.inl (55, 21)),
    Sum.inr (Sum.inl (177, 5)),
    Sum.inr (Sum.inl (55, 23)),
    Sum.inr (Sum.inl (177, 6)),
    Sum.inr (Sum.inl (155, 18)),
    Sum.inr (Sum.inl (72, 42)),
    Sum.inr (Sum.inl (155, 16)),
    Sum.inr (Sum.inl (72, 38)),
    Sum.inr (Sum.inl (177, 61)),
    Sum.inr (Sum.inl (55, 44)),
    Sum.inr (Sum.inl (177, 62)),
    Sum.inr (Sum.inl (55, 46)),
    Sum.inr (Sum.inl (78, 21)),
    Sum.inr (Sum.inl (124, 1)),
    Sum.inr (Sum.inl (78, 25)),
    Sum.inr (Sum.inl (124, 9)),
    Sum.inr (Sum.inl (225, 60)),
    Sum.inr (Sum.inl (139, 20)),
    Sum.inr (Sum.inl (225, 46)),
    Sum.inr (Sum.inl (139, 24)),
    Sum.inr (Sum.inl (72, 8)),
    Sum.inr (Sum.inl (155, 37)),
    Sum.inr (Sum.inl (72, 4)),
    Sum.inr (Sum.inl (155, 39)),
    Sum.inr (Sum.inl (55, 61)),
    Sum.inr (Sum.inl (177, 45)),
    Sum.inr (Sum.inl (55, 63)),
    Sum.inr (Sum.inl (177, 46)),
    Sum.inr (Sum.inl (124, 21)),
    Sum.inr (Sum.inl (78, 5)),
    Sum.inr (Sum.inl (124, 29)),
    Sum.inr (Sum.inl (78, 9)),
    Sum.inr (Sum.inl (139, 54)),
    Sum.inr (Sum.inl (225, 20)),
    Sum.inr (Sum.inl (139, 58)),
    Sum.inr (Sum.inl (225, 6)),
    Sum.inr (Sum.inl (202, 24)),
    Sum.inr (Sum.inl (129, 26)),
    Sum.inr (Sum.inl (116, 16)),
    Sum.inr (Sum.inl (163, 43)),
    Sum.inr (Sum.inl (105, 34)),
    Sum.inr (Sum.inl (60, 26)),
    Sum.inr (Sum.inl (222, 4)),
    Sum.inr (Sum.inl (56, 57)),
    Sum.inr (Sum.inl (202, 10)),
    Sum.inr (Sum.inl (129, 53)),
    Sum.inr (Sum.inl (116, 63)),
    Sum.inr (Sum.inl (163, 57)),
    Sum.inr (Sum.inl (105, 2)),
    Sum.inr (Sum.inl (60, 11)),
    Sum.inr (Sum.inl (222, 1)),
    Sum.inr (Sum.inl (56, 49)),
    Sum.inr (Sum.inl (116, 18)),
    Sum.inr (Sum.inl (163, 35)),
    Sum.inr (Sum.inl (202, 20)),
    Sum.inr (Sum.inl (129, 22)),
    Sum.inr (Sum.inl (222, 6)),
    Sum.inr (Sum.inl (56, 43)),
    Sum.inr (Sum.inl (105, 33)),
    Sum.inr (Sum.inl (60, 22)),
    Sum.inr (Sum.inl (116, 61)),
    Sum.inr (Sum.inl (163, 49)),
    Sum.inr (Sum.inl (202, 6)),
    Sum.inr (Sum.inl (129, 57)),
    Sum.inr (Sum.inl (222, 3)),
    Sum.inr (Sum.inl (56, 35)),
    Sum.inr (Sum.inl (105, 1)),
    Sum.inr (Sum.inl (60, 7)),
    Sum.inr (Sum.inl (129, 24)),
    Sum.inr (Sum.inl (202, 56)),
    Sum.inr (Sum.inl (163, 16)),
    Sum.inr (Sum.inl (116, 28)),
    Sum.inr (Sum.inl (60, 24)),
    Sum.inr (Sum.inl (105, 54)),
    Sum.inr (Sum.inl (56, 24)),
    Sum.inr (Sum.inl (222, 44)),
    Sum.inr (Sum.inl (129, 55)),
    Sum.inr (Sum.inl (202, 42)),
    Sum.inr (Sum.inl (163, 2)),
    Sum.inr (Sum.inl (116, 51)),
    Sum.inr (Sum.inl (60, 9)),
    Sum.inr (Sum.inl (105, 22)),
    Sum.inr (Sum.inl (56, 16)),
    Sum.inr (Sum.inl (222, 41)),
    Sum.inr (Sum.inl (163, 24)),
    Sum.inr (Sum.inl (116, 30)),
    Sum.inr (Sum.inl (129, 20)),
    Sum.inr (Sum.inl (202, 52)),
    Sum.inr (Sum.inl (56, 10)),
    Sum.inr (Sum.inl (222, 46)),
    Sum.inr (Sum.inl (60, 20)),
    Sum.inr (Sum.inl (105, 53)),
    Sum.inr (Sum.inl (163, 10)),
    Sum.inr (Sum.inl (116, 49)),
    Sum.inr (Sum.inl (129, 59)),
    Sum.inr (Sum.inl (202, 38)),
    Sum.inr (Sum.inl (56, 2)),
    Sum.inr (Sum.inl (222, 43)),
    Sum.inr (Sum.inl (60, 5)),
    Sum.inr (Sum.inl (105, 21)),
    Sum.inr (Sum.inl (113, 20)),
    Sum.inr (Sum.inl (89, 7)),
    Sum.inr (Sum.inl (61, 1)),
    Sum.inr (Sum.inl (193, 56)),
    Sum.inr (Sum.inl (221, 53)),
    Sum.inr (Sum.inl (185, 47)),
    Sum.inr (Sum.inl (131, 37)),
    Sum.inr (Sum.inl (57, 5)),
    Sum.inr (Sum.inl (113, 54)),
    Sum.inr (Sum.inl (89, 48)),
    Sum.inr (Sum.inl (61, 54)),
    Sum.inr (Sum.inl (193, 5)),
    Sum.inr (Sum.inl (221, 61)),
    Sum.inr (Sum.inl (185, 14)),
    Sum.inr (Sum.inl (131, 4)),
    Sum.inr (Sum.inl (57, 13)),
    Sum.inr (Sum.inl (61, 19)),
    Sum.inr (Sum.inl (193, 32)),
    Sum.inr (Sum.inl (113, 28)),
    Sum.inr (Sum.inl (89, 3)),
    Sum.inr (Sum.inl (131, 55)),
    Sum.inr (Sum.inl (57, 23)),
    Sum.inr (Sum.inl (221, 33)),
    Sum.inr (Sum.inl (185, 39)),
    Sum.inr (Sum.inl (61, 36)),
    Sum.inr (Sum.inl (193, 29)),
    Sum.inr (Sum.inl (113, 62)),
    Sum.inr (Sum.inl (89, 52)),
    Sum.inr (Sum.inl (131, 22)),
    Sum.inr (Sum.inl (57, 31)),
    Sum.inr (Sum.inl (221, 41)),
    Sum.inr (Sum.inl (185, 6)),
    Sum.inr (Sum.inl (89, 37)),
    Sum.inr (Sum.inl (113, 47)),
    Sum.inr (Sum.inl (193, 60)),
    Sum.inr (Sum.inl (61, 5)),
    Sum.inr (Sum.inl (185, 61)),
    Sum.inr (Sum.inl (221, 23)),
    Sum.inr (Sum.inl (57, 36)),
    Sum.inr (Sum.inl (131, 45)),
    Sum.inr (Sum.inl (89, 18)),
    Sum.inr (Sum.inl (113, 13)),
    Sum.inr (Sum.inl (193, 1)),
    Sum.inr (Sum.inl (61, 50)),
    Sum.inr (Sum.inl (185, 28)),
    Sum.inr (Sum.inl (221, 31)),
    Sum.inr (Sum.inl (57, 44)),
    Sum.inr (Sum.inl (131, 12)),
    Sum.inr (Sum.inl (193, 36)),
    Sum.inr (Sum.inl (61, 23)),
    Sum.inr (Sum.inl (89, 33)),
    Sum.inr (Sum.inl (113, 39)),
    Sum.inr (Sum.inl (57, 54)),
    Sum.inr (Sum.inl (131, 63)),
    Sum.inr (Sum.inl (185, 53)),
    Sum.inr (Sum.inl (221, 3)),
    Sum.inr (Sum.inl (193, 25)),
    Sum.inr (Sum.inl (61, 32)),
    Sum.inr (Sum.inl (89, 22)),
    Sum.inr (Sum.inl (113, 5)),
    Sum.inr (Sum.inl (57, 62)),
    Sum.inr (Sum.inl (131, 30)),
    Sum.inr (Sum.inl (185, 20)),
    Sum.inr (Sum.inl (221, 11)),
    Sum.inr (Sum.inl (63, 37)),
    Sum.inr (Sum.inl (161, 57)),
    Sum.inr (Sum.inl (121, 58)),
    Sum.inr (Sum.inl (102, 7)),
    Sum.inr (Sum.inl (192, 37)),
    Sum.inr (Sum.inl (220, 39)),
    Sum.inr (Sum.inl (84, 23)),
    Sum.inr (Sum.inl (58, 7)),
    Sum.inr (Sum.inl (63, 38)),
    Sum.inr (Sum.inl (161, 43)),
    Sum.inr (Sum.inl (121, 56)),
    Sum.inr (Sum.inl (102, 11)),
    Sum.inr (Sum.inl (192, 39)),
    Sum.inr (Sum.inl (220, 43)),
    Sum.inr (Sum.inl (84, 27)),
    Sum.inr (Sum.inl (58, 15)),
    Sum.inr (Sum.inl (121, 43)),
    Sum.inr (Sum.inl (102, 37)),
    Sum.inr (Sum.inl (63, 58)),
    Sum.inr (Sum.inl (161, 49)),
    Sum.inr (Sum.inl (84, 54)),
    Sum.inr (Sum.inl (58, 21)),
    Sum.inr (Sum.inl (192, 58)),
    Sum.inr (Sum.inl (220, 7)),
    Sum.inr (Sum.inl (121, 41)),
    Sum.inr (Sum.inl (102, 41)),
    Sum.inr (Sum.inl (63, 57)),
    Sum.inr (Sum.inl (161, 35)),
    Sum.inr (Sum.inl (84, 58)),
    Sum.inr (Sum.inl (58, 29)),
    Sum.inr (Sum.inl (192, 56)),
    Sum.inr (Sum.inl (220, 11)),
    Sum.inr (Sum.inl (192, 52)),
    Sum.inr (Sum.inl (220, 53)),
    Sum.inr (Sum.inl (84, 42)),
    Sum.inr (Sum.inl (58, 35)),
    Sum.inr (Sum.inl (63, 45)),
    Sum.inr (Sum.inl (161, 29)),
    Sum.inr (Sum.inl (121, 13)),
    Sum.inr (Sum.inl (102, 23)),
    Sum.inr (Sum.inl (192, 54)),
    Sum.inr (Sum.inl (220, 57)),
    Sum.inr (Sum.inl (84, 38)),
    Sum.inr (Sum.inl (58, 43)),
    Sum.inr (Sum.inl (63, 46)),
    Sum.inr (Sum.inl (161, 15)),
    Sum.inr (Sum.inl (121, 15)),
    Sum.inr (Sum.inl (102, 27)),
    Sum.inr (Sum.inl (84, 11)),
    Sum.inr (Sum.inl (58, 49)),
    Sum.inr (Sum.inl (192, 43)),
    Sum.inr (Sum.inl (220, 21)),
    Sum.inr (Sum.inl (121, 28)),
    Sum.inr (Sum.inl (102, 53)),
    Sum.inr (Sum.inl (63, 50)),
    Sum.inr (Sum.inl (161, 21)),
    Sum.inr (Sum.inl (84, 7)),
    Sum.inr (Sum.inl (58, 57)),
    Sum.inr (Sum.inl (192, 41)),
    Sum.inr (Sum.inl (220, 25)),
    Sum.inr (Sum.inl (121, 30)),
    Sum.inr (Sum.inl (102, 57)),
    Sum.inr (Sum.inl (63, 49)),
    Sum.inr (Sum.inl (161, 7)),
    Sum.inr (Sum.inl (199, 59)),
    Sum.inr (Sum.inl (199, 63)),
    Sum.inr (Sum.inl (219, 41)),
    Sum.inr (Sum.inl (219, 11)),
    Sum.inr (Sum.inl (183, 61)),
    Sum.inr (Sum.inl (183, 31)),
    Sum.inr (Sum.inl (62, 13)),
    Sum.inr (Sum.inl (62, 29)),
    Sum.inr (Sum.inl (183, 49)),
    Sum.inr (Sum.inl (183, 19)),
    Sum.inr (Sum.inl (62, 1)),
    Sum.inr (Sum.inl (62, 17)),
    Sum.inr (Sum.inl (199, 41)),
    Sum.inr (Sum.inl (199, 45)),
    Sum.inr (Sum.inl (219, 33)),
    Sum.inr (Sum.inl (219, 3)),
    Sum.inr (Sum.inl (219, 61)),
    Sum.inr (Sum.inl (219, 31)),
    Sum.inr (Sum.inl (199, 19)),
    Sum.inr (Sum.inl (199, 23)),
    Sum.inr (Sum.inl (62, 47)),
    Sum.inr (Sum.inl (62, 63)),
    Sum.inr (Sum.inl (183, 45)),
    Sum.inr (Sum.inl (183, 15))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock016Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨4096 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block016_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock016Input a
    let y := generatedSixthXiShortBlock016Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiCombinedMaskPhase
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block016_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock016Input a
    let y := generatedSixthXiShortBlock016Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block016_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block016_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock016Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block016_certificate a).1
    (generatedSixth_xi_short_block016_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
