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
def generatedSixthXiShortBlock013Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (75, 19)),
    Sum.inr (Sum.inl (43, 19)),
    Sum.inr (Sum.inl (115, 59)),
    Sum.inr (Sum.inl (164, 3)),
    Sum.inr (Sum.inl (130, 50)),
    Sum.inr (Sum.inl (201, 39)),
    Sum.inr (Sum.inl (90, 5)),
    Sum.inr (Sum.inl (217, 1)),
    Sum.inr (Sum.inl (90, 33)),
    Sum.inr (Sum.inl (217, 63)),
    Sum.inr (Sum.inl (130, 38)),
    Sum.inr (Sum.inl (201, 25)),
    Sum.inr (Sum.inl (115, 47)),
    Sum.inr (Sum.inl (164, 61)),
    Sum.inr (Sum.inl (75, 60)),
    Sum.inr (Sum.inl (43, 45)),
    Sum.inr (Sum.inl (115, 44)),
    Sum.inr (Sum.inl (164, 49)),
    Sum.inr (Sum.inl (75, 48)),
    Sum.inr (Sum.inl (43, 33)),
    Sum.inr (Sum.inl (90, 35)),
    Sum.inr (Sum.inl (217, 45)),
    Sum.inr (Sum.inl (130, 36)),
    Sum.inr (Sum.inl (201, 17)),
    Sum.inr (Sum.inl (130, 47)),
    Sum.inr (Sum.inl (201, 61)),
    Sum.inr (Sum.inl (90, 14)),
    Sum.inr (Sum.inl (217, 27)),
    Sum.inr (Sum.inl (75, 62)),
    Sum.inr (Sum.inl (43, 63)),
    Sum.inr (Sum.inl (115, 39)),
    Sum.inr (Sum.inl (164, 29)),
    Sum.inr (Sum.inl (75, 50)),
    Sum.inr (Sum.inl (43, 51)),
    Sum.inr (Sum.inl (115, 36)),
    Sum.inr (Sum.inl (164, 17)),
    Sum.inr (Sum.inl (130, 45)),
    Sum.inr (Sum.inl (201, 53)),
    Sum.inr (Sum.inl (90, 12)),
    Sum.inr (Sum.inl (217, 9)),
    Sum.inr (Sum.inl (162, 55)),
    Sum.inr (Sum.inl (100, 40)),
    Sum.inr (Sum.inl (134, 37)),
    Sum.inr (Sum.inl (223, 23)),
    Sum.inr (Sum.inl (134, 47)),
    Sum.inr (Sum.inl (223, 31)),
    Sum.inr (Sum.inl (162, 39)),
    Sum.inr (Sum.inl (100, 56)),
    Sum.inr (Sum.inl (100, 34)),
    Sum.inr (Sum.inl (162, 40)),
    Sum.inr (Sum.inl (223, 42)),
    Sum.inr (Sum.inl (134, 58)),
    Sum.inr (Sum.inl (223, 34)),
    Sum.inr (Sum.inl (134, 48)),
    Sum.inr (Sum.inl (100, 50)),
    Sum.inr (Sum.inl (162, 56)),
    Sum.inr (Sum.inl (191, 57)),
    Sum.inr (Sum.inl (86, 19)),
    Sum.inr (Sum.inl (77, 33)),
    Sum.inr (Sum.inl (44, 1)),
    Sum.inr (Sum.inl (77, 43)),
    Sum.inr (Sum.inl (44, 7)),
    Sum.inr (Sum.inl (191, 40)),
    Sum.inr (Sum.inl (86, 3)),
    Sum.inr (Sum.inl (86, 26)),
    Sum.inr (Sum.inl (191, 49)),
    Sum.inr (Sum.inl (44, 8)),
    Sum.inr (Sum.inl (77, 1)),
    Sum.inr (Sum.inl (44, 14)),
    Sum.inr (Sum.inl (77, 11)),
    Sum.inr (Sum.inl (86, 10)),
    Sum.inr (Sum.inl (191, 32)),
    Sum.inr (Sum.inl (162, 61)),
    Sum.inr (Sum.inl (100, 55)),
    Sum.inr (Sum.inl (134, 53)),
    Sum.inr (Sum.inl (223, 51)),
    Sum.inr (Sum.inl (134, 63)),
    Sum.inr (Sum.inl (223, 59)),
    Sum.inr (Sum.inl (162, 45)),
    Sum.inr (Sum.inl (100, 39)),
    Sum.inr (Sum.inl (100, 61)),
    Sum.inr (Sum.inl (162, 34)),
    Sum.inr (Sum.inl (223, 14)),
    Sum.inr (Sum.inl (134, 42)),
    Sum.inr (Sum.inl (223, 6)),
    Sum.inr (Sum.inl (134, 32)),
    Sum.inr (Sum.inl (100, 45)),
    Sum.inr (Sum.inl (162, 50)),
    Sum.inr (Sum.inl (191, 29)),
    Sum.inr (Sum.inl (86, 21)),
    Sum.inr (Sum.inl (77, 36)),
    Sum.inr (Sum.inl (44, 33)),
    Sum.inr (Sum.inl (77, 46)),
    Sum.inr (Sum.inl (44, 39)),
    Sum.inr (Sum.inl (191, 12)),
    Sum.inr (Sum.inl (86, 5)),
    Sum.inr (Sum.inl (86, 28)),
    Sum.inr (Sum.inl (191, 21)),
    Sum.inr (Sum.inl (44, 40)),
    Sum.inr (Sum.inl (77, 4)),
    Sum.inr (Sum.inl (44, 46)),
    Sum.inr (Sum.inl (77, 14)),
    Sum.inr (Sum.inl (86, 12)),
    Sum.inr (Sum.inl (191, 4)),
    Sum.inr (Sum.inl (76, 7)),
    Sum.inr (Sum.inl (120, 7)),
    Sum.inr (Sum.inl (120, 11)),
    Sum.inr (Sum.inl (76, 15)),
    Sum.inr (Sum.inl (182, 53)),
    Sum.inr (Sum.inl (200, 23)),
    Sum.inr (Sum.inl (200, 27)),
    Sum.inr (Sum.inl (182, 39)),
    Sum.inr (Sum.inl (101, 58)),
    Sum.inr (Sum.inl (82, 39)),
    Sum.inr (Sum.inl (82, 43)),
    Sum.inr (Sum.inl (101, 56)),
    Sum.inr (Sum.inl (224, 21)),
    Sum.inr (Sum.inl (45, 13)),
    Sum.inr (Sum.inl (45, 14)),
    Sum.inr (Sum.inl (224, 23)),
    Sum.inr (Sum.inl (76, 19)),
    Sum.inr (Sum.inl (120, 39)),
    Sum.inr (Sum.inl (120, 43)),
    Sum.inr (Sum.inl (76, 27)),
    Sum.inr (Sum.inl (182, 29)),
    Sum.inr (Sum.inl (200, 53)),
    Sum.inr (Sum.inl (200, 57)),
    Sum.inr (Sum.inl (182, 15)),
    Sum.inr (Sum.inl (101, 21)),
    Sum.inr (Sum.inl (82, 53)),
    Sum.inr (Sum.inl (82, 57)),
    Sum.inr (Sum.inl (101, 23)),
    Sum.inr (Sum.inl (224, 28)),
    Sum.inr (Sum.inl (45, 29)),
    Sum.inr (Sum.inl (45, 30)),
    Sum.inr (Sum.inl (224, 30)),
    Sum.inr (Sum.inl (101, 30)),
    Sum.inr (Sum.inl (82, 56)),
    Sum.inr (Sum.inl (82, 52)),
    Sum.inr (Sum.inl (101, 28)),
    Sum.inr (Sum.inl (224, 37)),
    Sum.inr (Sum.inl (45, 37)),
    Sum.inr (Sum.inl (45, 38)),
    Sum.inr (Sum.inl (224, 39)),
    Sum.inr (Sum.inl (76, 58)),
    Sum.inr (Sum.inl (120, 58)),
    Sum.inr (Sum.inl (120, 54)),
    Sum.inr (Sum.inl (76, 50)),
    Sum.inr (Sum.inl (182, 52)),
    Sum.inr (Sum.inl (200, 22)),
    Sum.inr (Sum.inl (200, 26)),
    Sum.inr (Sum.inl (182, 38)),
    Sum.inr (Sum.inl (101, 49)),
    Sum.inr (Sum.inl (82, 42)),
    Sum.inr (Sum.inl (82, 38)),
    Sum.inr (Sum.inl (101, 51)),
    Sum.inr (Sum.inl (224, 44)),
    Sum.inr (Sum.inl (45, 53)),
    Sum.inr (Sum.inl (45, 54)),
    Sum.inr (Sum.inl (224, 46)),
    Sum.inr (Sum.inl (76, 46)),
    Sum.inr (Sum.inl (120, 26)),
    Sum.inr (Sum.inl (120, 22)),
    Sum.inr (Sum.inl (76, 38)),
    Sum.inr (Sum.inl (182, 28)),
    Sum.inr (Sum.inl (200, 52)),
    Sum.inr (Sum.inl (200, 56)),
    Sum.inr (Sum.inl (182, 14)),
    Sum.inr (Sum.inr (16, 14)),
    Sum.inr (Sum.inr (16, 9)),
    Sum.inr (Sum.inr (90, 21)),
    Sum.inr (Sum.inr (90, 2)),
    Sum.inr (Sum.inr (388, 21)),
    Sum.inr (Sum.inr (388, 2)),
    Sum.inr (Sum.inr (462, 14)),
    Sum.inr (Sum.inr (462, 9)),
    Sum.inr (Sum.inr (399, 21)),
    Sum.inr (Sum.inr (399, 2)),
    Sum.inr (Sum.inr (453, 14)),
    Sum.inr (Sum.inr (453, 9)),
    Sum.inr (Sum.inr (27, 14)),
    Sum.inr (Sum.inr (27, 9)),
    Sum.inr (Sum.inr (81, 21)),
    Sum.inr (Sum.inr (81, 2)),
    Sum.inr (Sum.inr (16, 2)),
    Sum.inr (Sum.inr (16, 21)),
    Sum.inr (Sum.inr (90, 9)),
    Sum.inr (Sum.inr (90, 14)),
    Sum.inr (Sum.inr (388, 9)),
    Sum.inr (Sum.inr (388, 14)),
    Sum.inr (Sum.inr (462, 2)),
    Sum.inr (Sum.inr (462, 21)),
    Sum.inr (Sum.inr (399, 9)),
    Sum.inr (Sum.inr (399, 14)),
    Sum.inr (Sum.inr (453, 2)),
    Sum.inr (Sum.inr (453, 21)),
    Sum.inr (Sum.inr (27, 2)),
    Sum.inr (Sum.inr (27, 21)),
    Sum.inr (Sum.inr (81, 9)),
    Sum.inr (Sum.inr (81, 14)),
    Sum.inr (Sum.inr (208, 21)),
    Sum.inr (Sum.inr (208, 2)),
    Sum.inr (Sum.inr (154, 14)),
    Sum.inr (Sum.inr (154, 9)),
    Sum.inr (Sum.inr (324, 14)),
    Sum.inr (Sum.inr (324, 9)),
    Sum.inr (Sum.inr (270, 21)),
    Sum.inr (Sum.inr (270, 2)),
    Sum.inr (Sum.inr (335, 14)),
    Sum.inr (Sum.inr (335, 9)),
    Sum.inr (Sum.inr (261, 21)),
    Sum.inr (Sum.inr (261, 2)),
    Sum.inr (Sum.inr (219, 21)),
    Sum.inr (Sum.inr (219, 2)),
    Sum.inr (Sum.inr (145, 14)),
    Sum.inr (Sum.inr (145, 9)),
    Sum.inr (Sum.inr (208, 9)),
    Sum.inr (Sum.inr (208, 14)),
    Sum.inr (Sum.inr (154, 2)),
    Sum.inr (Sum.inr (154, 21)),
    Sum.inr (Sum.inr (324, 2)),
    Sum.inr (Sum.inr (324, 21)),
    Sum.inr (Sum.inr (270, 9)),
    Sum.inr (Sum.inr (270, 14)),
    Sum.inr (Sum.inr (335, 2)),
    Sum.inr (Sum.inr (335, 21)),
    Sum.inr (Sum.inr (261, 9)),
    Sum.inr (Sum.inr (261, 14)),
    Sum.inr (Sum.inr (219, 9)),
    Sum.inr (Sum.inr (219, 14)),
    Sum.inr (Sum.inr (145, 2)),
    Sum.inr (Sum.inr (145, 21)),
    Sum.inr (Sum.inl (123, 31)),
    Sum.inr (Sum.inl (226, 63)),
    Sum.inr (Sum.inl (123, 7)),
    Sum.inr (Sum.inl (226, 39)),
    Sum.inr (Sum.inl (67, 7)),
    Sum.inr (Sum.inl (197, 27)),
    Sum.inr (Sum.inl (67, 5)),
    Sum.inr (Sum.inl (197, 3)),
    Sum.inr (Sum.inl (80, 48)),
    Sum.inr (Sum.inl (110, 31)),
    Sum.inr (Sum.inl (80, 50)),
    Sum.inr (Sum.inl (110, 11)),
    Sum.inr (Sum.inl (190, 29)),
    Sum.inr (Sum.inl (47, 11)),
    Sum.inr (Sum.inl (190, 9)),
    Sum.inr (Sum.inl (47, 9)),
    Sum.inr (Sum.inl (67, 47)),
    Sum.inr (Sum.inl (197, 63)),
    Sum.inr (Sum.inl (67, 45)),
    Sum.inr (Sum.inl (197, 39)),
    Sum.inr (Sum.inl (123, 29)),
    Sum.inr (Sum.inl (226, 27)),
    Sum.inr (Sum.inl (123, 5)),
    Sum.inr (Sum.inl (226, 3))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock013Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨3328 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block013_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock013Input a
    let y := generatedSixthXiShortBlock013Output a
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
theorem generatedSixth_xi_short_block013_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock013Input a
    let y := generatedSixthXiShortBlock013Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block013_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block013_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock013Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block013_certificate a).1
    (generatedSixth_xi_short_block013_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
