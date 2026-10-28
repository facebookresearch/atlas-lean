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
def generatedSixthXiShortBlock019Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (190, 35)),
    Sum.inr (Sum.inl (67, 60)),
    Sum.inr (Sum.inl (190, 55)),
    Sum.inr (Sum.inl (67, 62)),
    Sum.inr (Sum.inl (47, 42)),
    Sum.inr (Sum.inl (197, 26)),
    Sum.inr (Sum.inl (47, 40)),
    Sum.inr (Sum.inl (197, 2)),
    Sum.inr (Sum.inl (47, 0)),
    Sum.inr (Sum.inl (197, 0)),
    Sum.inr (Sum.inl (47, 2)),
    Sum.inr (Sum.inl (197, 24)),
    Sum.inr (Sum.inl (190, 0)),
    Sum.inr (Sum.inl (67, 0)),
    Sum.inr (Sum.inl (190, 20)),
    Sum.inr (Sum.inl (67, 2)),
    Sum.inr (Sum.inl (110, 2)),
    Sum.inr (Sum.inl (226, 36)),
    Sum.inr (Sum.inl (110, 22)),
    Sum.inr (Sum.inl (226, 60)),
    Sum.inr (Sum.inl (80, 62)),
    Sum.inr (Sum.inl (123, 2)),
    Sum.inr (Sum.inl (80, 60)),
    Sum.inr (Sum.inl (123, 26)),
    Sum.inr (Sum.inl (190, 33)),
    Sum.inr (Sum.inl (67, 20)),
    Sum.inr (Sum.inl (190, 53)),
    Sum.inr (Sum.inl (67, 22)),
    Sum.inr (Sum.inl (47, 62)),
    Sum.inr (Sum.inl (197, 62)),
    Sum.inr (Sum.inl (47, 60)),
    Sum.inr (Sum.inl (197, 38)),
    Sum.inr (Sum.inl (80, 42)),
    Sum.inr (Sum.inl (123, 38)),
    Sum.inr (Sum.inl (80, 40)),
    Sum.inr (Sum.inl (123, 62)),
    Sum.inr (Sum.inl (110, 60)),
    Sum.inr (Sum.inl (226, 26)),
    Sum.inr (Sum.inl (110, 40)),
    Sum.inr (Sum.inl (226, 2)),
    Sum.inr (Sum.inl (79, 0)),
    Sum.inr (Sum.inl (109, 36)),
    Sum.inr (Sum.inl (79, 12)),
    Sum.inr (Sum.inl (109, 44)),
    Sum.inr (Sum.inl (181, 36)),
    Sum.inr (Sum.inl (51, 45)),
    Sum.inr (Sum.inl (181, 38)),
    Sum.inr (Sum.inl (51, 33)),
    Sum.inr (Sum.inl (109, 0)),
    Sum.inr (Sum.inl (79, 16)),
    Sum.inr (Sum.inl (109, 8)),
    Sum.inr (Sum.inl (79, 28)),
    Sum.inr (Sum.inl (51, 47)),
    Sum.inr (Sum.inl (181, 19)),
    Sum.inr (Sum.inl (51, 35)),
    Sum.inr (Sum.inl (181, 17)),
    Sum.inr (Sum.inl (181, 0)),
    Sum.inr (Sum.inl (51, 2)),
    Sum.inr (Sum.inl (181, 2)),
    Sum.inr (Sum.inl (51, 14)),
    Sum.inr (Sum.inl (79, 61)),
    Sum.inr (Sum.inl (109, 25)),
    Sum.inr (Sum.inl (79, 49)),
    Sum.inr (Sum.inl (109, 17)),
    Sum.inr (Sum.inl (51, 0)),
    Sum.inr (Sum.inl (181, 55)),
    Sum.inr (Sum.inl (51, 12)),
    Sum.inr (Sum.inl (181, 53)),
    Sum.inr (Sum.inl (109, 61)),
    Sum.inr (Sum.inl (79, 45)),
    Sum.inr (Sum.inl (109, 53)),
    Sum.inr (Sum.inl (79, 33)),
    Sum.inr (Sum.inl (227, 0)),
    Sum.inr (Sum.inl (137, 18)),
    Sum.inr (Sum.inl (227, 18)),
    Sum.inr (Sum.inl (137, 30)),
    Sum.inr (Sum.inl (159, 20)),
    Sum.inr (Sum.inl (68, 29)),
    Sum.inr (Sum.inl (159, 23)),
    Sum.inr (Sum.inl (68, 31)),
    Sum.inr (Sum.inl (137, 0)),
    Sum.inr (Sum.inl (227, 36)),
    Sum.inr (Sum.inl (137, 12)),
    Sum.inr (Sum.inl (227, 54)),
    Sum.inr (Sum.inl (68, 20)),
    Sum.inr (Sum.inl (159, 28)),
    Sum.inr (Sum.inl (68, 22)),
    Sum.inr (Sum.inl (159, 31)),
    Sum.inr (Sum.inl (159, 0)),
    Sum.inr (Sum.inl (68, 9)),
    Sum.inr (Sum.inl (159, 3)),
    Sum.inr (Sum.inl (68, 11)),
    Sum.inr (Sum.inl (227, 1)),
    Sum.inr (Sum.inl (137, 19)),
    Sum.inr (Sum.inl (227, 19)),
    Sum.inr (Sum.inl (137, 31)),
    Sum.inr (Sum.inl (68, 0)),
    Sum.inr (Sum.inl (159, 8)),
    Sum.inr (Sum.inl (68, 2)),
    Sum.inr (Sum.inl (159, 11)),
    Sum.inr (Sum.inl (137, 1)),
    Sum.inr (Sum.inl (227, 37)),
    Sum.inr (Sum.inl (137, 13)),
    Sum.inr (Sum.inl (227, 55)),
    Sum.inr (Sum.inl (160, 0)),
    Sum.inr (Sum.inl (160, 48)),
    Sum.inr (Sum.inl (228, 25)),
    Sum.inr (Sum.inl (228, 36)),
    Sum.inr (Sum.inl (180, 61)),
    Sum.inr (Sum.inl (180, 0)),
    Sum.inr (Sum.inl (96, 2)),
    Sum.inr (Sum.inl (96, 29)),
    Sum.inr (Sum.inl (180, 49)),
    Sum.inr (Sum.inl (180, 12)),
    Sum.inr (Sum.inl (96, 14)),
    Sum.inr (Sum.inl (96, 17)),
    Sum.inr (Sum.inl (160, 2)),
    Sum.inr (Sum.inl (160, 50)),
    Sum.inr (Sum.inl (228, 17)),
    Sum.inr (Sum.inl (228, 44)),
    Sum.inr (Sum.inl (228, 61)),
    Sum.inr (Sum.inl (228, 0)),
    Sum.inr (Sum.inl (160, 55)),
    Sum.inr (Sum.inl (160, 7)),
    Sum.inr (Sum.inl (96, 0)),
    Sum.inr (Sum.inl (96, 31)),
    Sum.inr (Sum.inl (180, 29)),
    Sum.inr (Sum.inl (180, 32)),
    Sum.inr (Sum.inl (96, 12)),
    Sum.inr (Sum.inl (96, 19)),
    Sum.inr (Sum.inl (180, 17)),
    Sum.inr (Sum.inl (180, 44)),
    Sum.inr (Sum.inl (228, 53)),
    Sum.inr (Sum.inl (228, 8)),
    Sum.inr (Sum.inl (160, 53)),
    Sum.inr (Sum.inl (160, 5)),
    Sum.inr (Sum.inl (122, 54)),
    Sum.inr (Sum.inl (122, 55)),
    Sum.inr (Sum.inl (50, 38)),
    Sum.inr (Sum.inl (50, 2)),
    Sum.inr (Sum.inl (94, 47)),
    Sum.inr (Sum.inl (94, 7)),
    Sum.inr (Sum.inl (69, 12)),
    Sum.inr (Sum.inl (69, 13)),
    Sum.inr (Sum.inl (94, 44)),
    Sum.inr (Sum.inl (94, 4)),
    Sum.inr (Sum.inl (69, 0)),
    Sum.inr (Sum.inl (69, 1)),
    Sum.inr (Sum.inl (122, 36)),
    Sum.inr (Sum.inl (122, 37)),
    Sum.inr (Sum.inl (50, 36)),
    Sum.inr (Sum.inl (50, 0)),
    Sum.inr (Sum.inl (50, 47)),
    Sum.inr (Sum.inl (50, 11)),
    Sum.inr (Sum.inl (122, 18)),
    Sum.inr (Sum.inl (122, 19)),
    Sum.inr (Sum.inl (69, 30)),
    Sum.inr (Sum.inl (69, 31)),
    Sum.inr (Sum.inl (94, 43)),
    Sum.inr (Sum.inl (94, 3)),
    Sum.inr (Sum.inl (69, 18)),
    Sum.inr (Sum.inl (69, 19)),
    Sum.inr (Sum.inl (94, 40)),
    Sum.inr (Sum.inl (94, 0)),
    Sum.inr (Sum.inl (50, 45)),
    Sum.inr (Sum.inl (50, 9)),
    Sum.inr (Sum.inl (122, 0)),
    Sum.inr (Sum.inl (122, 1)),
    Sum.inr (Sum.inr (0, 22)),
    Sum.inr (Sum.inr (65, 1)),
    Sum.inr (Sum.inr (203, 22)),
    Sum.inr (Sum.inr (138, 1)),
    Sum.inr (Sum.inr (277, 22)),
    Sum.inr (Sum.inr (340, 1)),
    Sum.inr (Sum.inr (478, 22)),
    Sum.inr (Sum.inr (415, 1)),
    Sum.inr (Sum.inr (286, 22)),
    Sum.inr (Sum.inr (351, 1)),
    Sum.inr (Sum.inr (469, 22)),
    Sum.inr (Sum.inr (404, 1)),
    Sum.inr (Sum.inr (11, 22)),
    Sum.inr (Sum.inr (74, 1)),
    Sum.inr (Sum.inr (192, 22)),
    Sum.inr (Sum.inr (129, 1)),
    Sum.inr (Sum.inr (129, 22)),
    Sum.inr (Sum.inr (192, 1)),
    Sum.inr (Sum.inr (74, 22)),
    Sum.inr (Sum.inr (11, 1)),
    Sum.inr (Sum.inr (404, 22)),
    Sum.inr (Sum.inr (469, 1)),
    Sum.inr (Sum.inr (351, 22)),
    Sum.inr (Sum.inr (286, 1)),
    Sum.inr (Sum.inr (415, 22)),
    Sum.inr (Sum.inr (478, 1)),
    Sum.inr (Sum.inr (340, 22)),
    Sum.inr (Sum.inr (277, 1)),
    Sum.inr (Sum.inr (138, 22)),
    Sum.inr (Sum.inr (203, 1)),
    Sum.inr (Sum.inr (65, 22)),
    Sum.inr (Sum.inr (0, 1)),
    Sum.inr (Sum.inr (65, 11)),
    Sum.inr (Sum.inr (0, 15)),
    Sum.inr (Sum.inr (138, 11)),
    Sum.inr (Sum.inr (203, 15)),
    Sum.inr (Sum.inr (340, 11)),
    Sum.inr (Sum.inr (277, 15)),
    Sum.inr (Sum.inr (415, 11)),
    Sum.inr (Sum.inr (478, 15)),
    Sum.inr (Sum.inr (351, 11)),
    Sum.inr (Sum.inr (286, 15)),
    Sum.inr (Sum.inr (404, 11)),
    Sum.inr (Sum.inr (469, 15)),
    Sum.inr (Sum.inr (74, 11)),
    Sum.inr (Sum.inr (11, 15)),
    Sum.inr (Sum.inr (129, 11)),
    Sum.inr (Sum.inr (192, 15)),
    Sum.inr (Sum.inr (192, 11)),
    Sum.inr (Sum.inr (129, 15)),
    Sum.inr (Sum.inr (11, 11)),
    Sum.inr (Sum.inr (74, 15)),
    Sum.inr (Sum.inr (469, 11)),
    Sum.inr (Sum.inr (404, 15)),
    Sum.inr (Sum.inr (286, 11)),
    Sum.inr (Sum.inr (351, 15)),
    Sum.inr (Sum.inr (478, 11)),
    Sum.inr (Sum.inr (415, 15)),
    Sum.inr (Sum.inr (277, 11)),
    Sum.inr (Sum.inr (340, 15)),
    Sum.inr (Sum.inr (203, 11)),
    Sum.inr (Sum.inr (138, 15)),
    Sum.inr (Sum.inr (0, 11)),
    Sum.inr (Sum.inr (65, 15)),
    Sum.inr (Sum.inr (0, 13)),
    Sum.inr (Sum.inr (65, 0)),
    Sum.inr (Sum.inr (138, 13)),
    Sum.inr (Sum.inr (203, 0)),
    Sum.inr (Sum.inr (340, 13)),
    Sum.inr (Sum.inr (277, 0)),
    Sum.inr (Sum.inr (478, 13)),
    Sum.inr (Sum.inr (415, 0)),
    Sum.inr (Sum.inr (351, 13)),
    Sum.inr (Sum.inr (286, 0)),
    Sum.inr (Sum.inr (469, 13)),
    Sum.inr (Sum.inr (404, 0)),
    Sum.inr (Sum.inr (11, 13)),
    Sum.inr (Sum.inr (74, 0)),
    Sum.inr (Sum.inr (129, 13)),
    Sum.inr (Sum.inr (192, 0)),
    Sum.inr (Sum.inr (65, 8)),
    Sum.inr (Sum.inr (0, 23)),
    Sum.inr (Sum.inr (203, 8)),
    Sum.inr (Sum.inr (138, 23)),
    Sum.inr (Sum.inr (277, 8)),
    Sum.inr (Sum.inr (340, 23)),
    Sum.inr (Sum.inr (415, 8)),
    Sum.inr (Sum.inr (478, 23))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock019Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨4864 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block019_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock019Input a
    let y := generatedSixthXiShortBlock019Output a
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
theorem generatedSixth_xi_short_block019_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock019Input a
    let y := generatedSixthXiShortBlock019Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block019_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block019_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock019Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block019_certificate a).1
    (generatedSixth_xi_short_block019_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
