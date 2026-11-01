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
def generatedSixthXiShortBlock014Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (190, 31)),
    Sum.inr (Sum.inl (47, 31)),
    Sum.inr (Sum.inl (190, 11)),
    Sum.inr (Sum.inl (47, 29)),
    Sum.inr (Sum.inl (80, 14)),
    Sum.inr (Sum.inl (110, 29)),
    Sum.inr (Sum.inl (80, 12)),
    Sum.inr (Sum.inl (110, 9)),
    Sum.inr (Sum.inl (80, 24)),
    Sum.inr (Sum.inl (110, 55)),
    Sum.inr (Sum.inl (80, 26)),
    Sum.inr (Sum.inl (110, 35)),
    Sum.inr (Sum.inl (190, 42)),
    Sum.inr (Sum.inl (47, 35)),
    Sum.inr (Sum.inl (190, 62)),
    Sum.inr (Sum.inl (47, 33)),
    Sum.inr (Sum.inl (123, 33)),
    Sum.inr (Sum.inl (226, 61)),
    Sum.inr (Sum.inl (123, 57)),
    Sum.inr (Sum.inl (226, 37)),
    Sum.inr (Sum.inl (67, 57)),
    Sum.inr (Sum.inl (197, 25)),
    Sum.inr (Sum.inl (67, 59)),
    Sum.inr (Sum.inl (197, 1)),
    Sum.inr (Sum.inl (190, 40)),
    Sum.inr (Sum.inl (47, 55)),
    Sum.inr (Sum.inl (190, 60)),
    Sum.inr (Sum.inl (47, 53)),
    Sum.inr (Sum.inl (80, 38)),
    Sum.inr (Sum.inl (110, 53)),
    Sum.inr (Sum.inl (80, 36)),
    Sum.inr (Sum.inl (110, 33)),
    Sum.inr (Sum.inl (67, 17)),
    Sum.inr (Sum.inl (197, 61)),
    Sum.inr (Sum.inl (67, 19)),
    Sum.inr (Sum.inl (197, 37)),
    Sum.inr (Sum.inl (123, 35)),
    Sum.inr (Sum.inl (226, 25)),
    Sum.inr (Sum.inl (123, 59)),
    Sum.inr (Sum.inl (226, 1)),
    Sum.inr (Sum.inr (16, 3)),
    Sum.inr (Sum.inr (462, 20)),
    Sum.inr (Sum.inr (453, 20)),
    Sum.inr (Sum.inr (27, 3)),
    Sum.inr (Sum.inr (16, 12)),
    Sum.inr (Sum.inr (462, 10)),
    Sum.inr (Sum.inr (453, 10)),
    Sum.inr (Sum.inr (27, 12)),
    Sum.inr (Sum.inr (154, 20)),
    Sum.inr (Sum.inr (324, 3)),
    Sum.inr (Sum.inr (335, 3)),
    Sum.inr (Sum.inr (145, 20)),
    Sum.inr (Sum.inr (154, 10)),
    Sum.inr (Sum.inr (324, 12)),
    Sum.inr (Sum.inr (335, 12)),
    Sum.inr (Sum.inr (145, 10)),
    Sum.inr (Sum.inr (16, 10)),
    Sum.inr (Sum.inr (462, 12)),
    Sum.inr (Sum.inr (453, 12)),
    Sum.inr (Sum.inr (27, 10)),
    Sum.inr (Sum.inr (16, 20)),
    Sum.inr (Sum.inr (462, 3)),
    Sum.inr (Sum.inr (453, 3)),
    Sum.inr (Sum.inr (27, 20)),
    Sum.inr (Sum.inr (154, 12)),
    Sum.inr (Sum.inr (324, 10)),
    Sum.inr (Sum.inr (335, 10)),
    Sum.inr (Sum.inr (145, 12)),
    Sum.inr (Sum.inr (154, 3)),
    Sum.inr (Sum.inr (324, 20)),
    Sum.inr (Sum.inr (335, 20)),
    Sum.inr (Sum.inr (145, 3)),
    Sum.inr (Sum.inr (90, 20)),
    Sum.inr (Sum.inr (388, 3)),
    Sum.inr (Sum.inr (399, 3)),
    Sum.inr (Sum.inr (81, 20)),
    Sum.inr (Sum.inr (90, 10)),
    Sum.inr (Sum.inr (388, 12)),
    Sum.inr (Sum.inr (399, 12)),
    Sum.inr (Sum.inr (81, 10)),
    Sum.inr (Sum.inr (208, 3)),
    Sum.inr (Sum.inr (270, 20)),
    Sum.inr (Sum.inr (261, 20)),
    Sum.inr (Sum.inr (219, 3)),
    Sum.inr (Sum.inr (208, 12)),
    Sum.inr (Sum.inr (270, 10)),
    Sum.inr (Sum.inr (261, 10)),
    Sum.inr (Sum.inr (219, 12)),
    Sum.inr (Sum.inr (90, 12)),
    Sum.inr (Sum.inr (388, 10)),
    Sum.inr (Sum.inr (399, 10)),
    Sum.inr (Sum.inr (81, 12)),
    Sum.inr (Sum.inr (90, 3)),
    Sum.inr (Sum.inr (388, 20)),
    Sum.inr (Sum.inr (399, 20)),
    Sum.inr (Sum.inr (81, 3)),
    Sum.inr (Sum.inr (208, 10)),
    Sum.inr (Sum.inr (270, 12)),
    Sum.inr (Sum.inr (261, 12)),
    Sum.inr (Sum.inr (219, 10)),
    Sum.inr (Sum.inr (208, 20)),
    Sum.inr (Sum.inr (270, 3)),
    Sum.inr (Sum.inr (261, 3)),
    Sum.inr (Sum.inr (219, 20)),
    Sum.inr (Sum.inl (189, 47)),
    Sum.inr (Sum.inl (93, 48)),
    Sum.inr (Sum.inl (189, 35)),
    Sum.inr (Sum.inl (93, 11)),
    Sum.inr (Sum.inl (65, 47)),
    Sum.inr (Sum.inl (95, 31)),
    Sum.inr (Sum.inl (65, 45)),
    Sum.inr (Sum.inl (95, 15)),
    Sum.inr (Sum.inl (65, 35)),
    Sum.inr (Sum.inl (95, 19)),
    Sum.inr (Sum.inl (65, 33)),
    Sum.inr (Sum.inl (95, 3)),
    Sum.inr (Sum.inl (189, 45)),
    Sum.inr (Sum.inl (93, 56)),
    Sum.inr (Sum.inl (189, 33)),
    Sum.inr (Sum.inl (93, 3)),
    Sum.inr (Sum.inl (136, 63)),
    Sum.inr (Sum.inl (198, 47)),
    Sum.inr (Sum.inl (136, 30)),
    Sum.inr (Sum.inl (198, 7)),
    Sum.inr (Sum.inl (229, 63)),
    Sum.inr (Sum.inl (49, 31)),
    Sum.inr (Sum.inl (229, 39)),
    Sum.inr (Sum.inl (49, 29)),
    Sum.inr (Sum.inl (229, 60)),
    Sum.inr (Sum.inl (49, 19)),
    Sum.inr (Sum.inl (229, 36)),
    Sum.inr (Sum.inl (49, 17)),
    Sum.inr (Sum.inl (136, 45)),
    Sum.inr (Sum.inl (198, 45)),
    Sum.inr (Sum.inl (136, 12)),
    Sum.inr (Sum.inl (198, 5)),
    Sum.inr (Sum.inl (93, 34)),
    Sum.inr (Sum.inl (189, 48)),
    Sum.inr (Sum.inl (93, 25)),
    Sum.inr (Sum.inl (189, 60)),
    Sum.inr (Sum.inl (95, 61)),
    Sum.inr (Sum.inl (65, 48)),
    Sum.inr (Sum.inl (95, 45)),
    Sum.inr (Sum.inl (65, 50)),
    Sum.inr (Sum.inl (95, 49)),
    Sum.inr (Sum.inl (65, 60)),
    Sum.inr (Sum.inl (95, 33)),
    Sum.inr (Sum.inl (65, 62)),
    Sum.inr (Sum.inl (93, 42)),
    Sum.inr (Sum.inl (189, 50)),
    Sum.inr (Sum.inl (93, 17)),
    Sum.inr (Sum.inl (189, 62)),
    Sum.inr (Sum.inl (198, 62)),
    Sum.inr (Sum.inl (136, 55)),
    Sum.inr (Sum.inl (198, 22)),
    Sum.inr (Sum.inl (136, 22)),
    Sum.inr (Sum.inl (49, 62)),
    Sum.inr (Sum.inl (229, 31)),
    Sum.inr (Sum.inl (49, 60)),
    Sum.inr (Sum.inl (229, 7)),
    Sum.inr (Sum.inl (49, 50)),
    Sum.inr (Sum.inl (229, 28)),
    Sum.inr (Sum.inl (49, 48)),
    Sum.inr (Sum.inl (229, 4)),
    Sum.inr (Sum.inl (198, 60)),
    Sum.inr (Sum.inl (136, 37)),
    Sum.inr (Sum.inl (198, 20)),
    Sum.inr (Sum.inl (136, 4)),
    Sum.inr (Sum.inl (180, 55)),
    Sum.inr (Sum.inl (228, 19)),
    Sum.inr (Sum.inl (180, 59)),
    Sum.inr (Sum.inl (228, 27)),
    Sum.inr (Sum.inl (160, 34)),
    Sum.inr (Sum.inl (96, 53)),
    Sum.inr (Sum.inl (160, 32)),
    Sum.inr (Sum.inl (96, 57)),
    Sum.inr (Sum.inl (228, 55)),
    Sum.inr (Sum.inl (180, 23)),
    Sum.inr (Sum.inl (228, 63)),
    Sum.inr (Sum.inl (180, 27)),
    Sum.inr (Sum.inl (96, 55)),
    Sum.inr (Sum.inl (160, 21)),
    Sum.inr (Sum.inl (96, 59)),
    Sum.inr (Sum.inl (160, 23)),
    Sum.inr (Sum.inl (122, 53)),
    Sum.inr (Sum.inl (69, 5)),
    Sum.inr (Sum.inl (122, 39)),
    Sum.inr (Sum.inl (69, 9)),
    Sum.inr (Sum.inl (94, 13)),
    Sum.inr (Sum.inl (50, 4)),
    Sum.inr (Sum.inl (94, 14)),
    Sum.inr (Sum.inl (50, 6)),
    Sum.inr (Sum.inl (69, 23)),
    Sum.inr (Sum.inl (122, 17)),
    Sum.inr (Sum.inl (69, 27)),
    Sum.inr (Sum.inl (122, 3)),
    Sum.inr (Sum.inl (50, 13)),
    Sum.inr (Sum.inl (94, 9)),
    Sum.inr (Sum.inl (50, 15)),
    Sum.inr (Sum.inl (94, 10)),
    Sum.inr (Sum.inl (160, 18)),
    Sum.inr (Sum.inl (96, 42)),
    Sum.inr (Sum.inl (160, 16)),
    Sum.inr (Sum.inl (96, 38)),
    Sum.inr (Sum.inl (180, 10)),
    Sum.inr (Sum.inl (228, 46)),
    Sum.inr (Sum.inl (180, 6)),
    Sum.inr (Sum.inl (228, 38)),
    Sum.inr (Sum.inl (96, 40)),
    Sum.inr (Sum.inl (160, 37)),
    Sum.inr (Sum.inl (96, 36)),
    Sum.inr (Sum.inl (160, 39)),
    Sum.inr (Sum.inl (228, 10)),
    Sum.inr (Sum.inl (180, 42)),
    Sum.inr (Sum.inl (228, 2)),
    Sum.inr (Sum.inl (180, 38)),
    Sum.inr (Sum.inl (94, 37)),
    Sum.inr (Sum.inl (50, 32)),
    Sum.inr (Sum.inl (94, 38)),
    Sum.inr (Sum.inl (50, 34)),
    Sum.inr (Sum.inl (122, 52)),
    Sum.inr (Sum.inl (69, 4)),
    Sum.inr (Sum.inl (122, 38)),
    Sum.inr (Sum.inl (69, 8)),
    Sum.inr (Sum.inl (50, 41)),
    Sum.inr (Sum.inl (94, 33)),
    Sum.inr (Sum.inl (50, 43)),
    Sum.inr (Sum.inl (94, 34)),
    Sum.inr (Sum.inl (69, 22)),
    Sum.inr (Sum.inl (122, 16)),
    Sum.inr (Sum.inl (69, 26)),
    Sum.inr (Sum.inl (122, 2)),
    Sum.inr (Sum.inl (227, 61)),
    Sum.inr (Sum.inl (109, 24)),
    Sum.inr (Sum.inl (227, 25)),
    Sum.inr (Sum.inl (109, 60)),
    Sum.inr (Sum.inl (137, 55)),
    Sum.inr (Sum.inl (79, 40)),
    Sum.inr (Sum.inl (137, 37)),
    Sum.inr (Sum.inl (79, 56)),
    Sum.inr (Sum.inl (137, 59)),
    Sum.inr (Sum.inl (79, 36)),
    Sum.inr (Sum.inl (137, 41)),
    Sum.inr (Sum.inl (79, 52)),
    Sum.inr (Sum.inl (227, 47)),
    Sum.inr (Sum.inl (109, 16)),
    Sum.inr (Sum.inl (227, 11)),
    Sum.inr (Sum.inl (109, 52)),
    Sum.inr (Sum.inl (68, 41)),
    Sum.inr (Sum.inl (181, 54)),
    Sum.inr (Sum.inl (68, 32)),
    Sum.inr (Sum.inl (181, 1)),
    Sum.inr (Sum.inl (159, 41)),
    Sum.inr (Sum.inl (51, 7)),
    Sum.inr (Sum.inl (159, 33)),
    Sum.inr (Sum.inl (51, 5))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock014Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨3584 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block014_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock014Input a
    let y := generatedSixthXiShortBlock014Output a
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
theorem generatedSixth_xi_short_block014_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock014Input a
    let y := generatedSixthXiShortBlock014Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block014_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block014_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock014Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block014_certificate a).1
    (generatedSixth_xi_short_block014_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
