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
def generatedSixthXiShortBlock018Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (121, 19)),
    Sum.inr (Sum.inl (84, 45)),
    Sum.inr (Sum.inl (84, 33)),
    Sum.inr (Sum.inl (121, 17)),
    Sum.inr (Sum.inl (58, 26)),
    Sum.inr (Sum.inl (102, 46)),
    Sum.inr (Sum.inl (102, 34)),
    Sum.inr (Sum.inl (58, 18)),
    Sum.inr (Sum.inl (161, 0)),
    Sum.inr (Sum.inl (220, 0)),
    Sum.inr (Sum.inl (220, 12)),
    Sum.inr (Sum.inl (161, 18)),
    Sum.inr (Sum.inl (192, 0)),
    Sum.inr (Sum.inl (63, 0)),
    Sum.inr (Sum.inl (63, 3)),
    Sum.inr (Sum.inl (192, 2)),
    Sum.inr (Sum.inl (161, 36)),
    Sum.inr (Sum.inl (220, 18)),
    Sum.inr (Sum.inl (220, 30)),
    Sum.inr (Sum.inl (161, 54)),
    Sum.inr (Sum.inl (192, 17)),
    Sum.inr (Sum.inl (63, 8)),
    Sum.inr (Sum.inl (63, 11)),
    Sum.inr (Sum.inl (192, 19)),
    Sum.inr (Sum.inl (192, 12)),
    Sum.inr (Sum.inl (63, 20)),
    Sum.inr (Sum.inl (63, 23)),
    Sum.inr (Sum.inl (192, 14)),
    Sum.inr (Sum.inl (161, 62)),
    Sum.inr (Sum.inl (220, 62)),
    Sum.inr (Sum.inl (220, 50)),
    Sum.inr (Sum.inl (161, 44)),
    Sum.inr (Sum.inl (192, 29)),
    Sum.inr (Sum.inl (63, 28)),
    Sum.inr (Sum.inl (63, 31)),
    Sum.inr (Sum.inl (192, 31)),
    Sum.inr (Sum.inl (161, 26)),
    Sum.inr (Sum.inl (220, 44)),
    Sum.inr (Sum.inl (220, 32)),
    Sum.inr (Sum.inl (161, 8)),
    Sum.inr (Sum.inr (0, 9)),
    Sum.inr (Sum.inr (0, 14)),
    Sum.inr (Sum.inr (74, 21)),
    Sum.inr (Sum.inr (74, 2)),
    Sum.inr (Sum.inr (404, 21)),
    Sum.inr (Sum.inr (404, 2)),
    Sum.inr (Sum.inr (478, 9)),
    Sum.inr (Sum.inr (478, 14)),
    Sum.inr (Sum.inr (415, 21)),
    Sum.inr (Sum.inr (415, 2)),
    Sum.inr (Sum.inr (469, 9)),
    Sum.inr (Sum.inr (469, 14)),
    Sum.inr (Sum.inr (11, 9)),
    Sum.inr (Sum.inr (11, 14)),
    Sum.inr (Sum.inr (65, 21)),
    Sum.inr (Sum.inr (65, 2)),
    Sum.inr (Sum.inr (129, 21)),
    Sum.inr (Sum.inr (129, 2)),
    Sum.inr (Sum.inr (203, 9)),
    Sum.inr (Sum.inr (203, 14)),
    Sum.inr (Sum.inr (277, 9)),
    Sum.inr (Sum.inr (277, 14)),
    Sum.inr (Sum.inr (351, 21)),
    Sum.inr (Sum.inr (351, 2)),
    Sum.inr (Sum.inr (286, 9)),
    Sum.inr (Sum.inr (286, 14)),
    Sum.inr (Sum.inr (340, 21)),
    Sum.inr (Sum.inr (340, 2)),
    Sum.inr (Sum.inr (138, 21)),
    Sum.inr (Sum.inr (138, 2)),
    Sum.inr (Sum.inr (192, 9)),
    Sum.inr (Sum.inr (192, 14)),
    Sum.inr (Sum.inr (0, 2)),
    Sum.inr (Sum.inr (0, 21)),
    Sum.inr (Sum.inr (74, 14)),
    Sum.inr (Sum.inr (74, 9)),
    Sum.inr (Sum.inr (404, 14)),
    Sum.inr (Sum.inr (404, 9)),
    Sum.inr (Sum.inr (478, 2)),
    Sum.inr (Sum.inr (478, 21)),
    Sum.inr (Sum.inr (415, 14)),
    Sum.inr (Sum.inr (415, 9)),
    Sum.inr (Sum.inr (469, 2)),
    Sum.inr (Sum.inr (469, 21)),
    Sum.inr (Sum.inr (11, 2)),
    Sum.inr (Sum.inr (11, 21)),
    Sum.inr (Sum.inr (65, 14)),
    Sum.inr (Sum.inr (65, 9)),
    Sum.inr (Sum.inr (129, 14)),
    Sum.inr (Sum.inr (129, 9)),
    Sum.inr (Sum.inr (203, 2)),
    Sum.inr (Sum.inr (203, 21)),
    Sum.inr (Sum.inr (277, 2)),
    Sum.inr (Sum.inr (277, 21)),
    Sum.inr (Sum.inr (351, 14)),
    Sum.inr (Sum.inr (351, 9)),
    Sum.inr (Sum.inr (286, 2)),
    Sum.inr (Sum.inr (286, 21)),
    Sum.inr (Sum.inr (340, 14)),
    Sum.inr (Sum.inr (340, 9)),
    Sum.inr (Sum.inr (138, 14)),
    Sum.inr (Sum.inr (138, 9)),
    Sum.inr (Sum.inr (192, 2)),
    Sum.inr (Sum.inr (192, 21)),
    Sum.inr (Sum.inl (198, 0)),
    Sum.inr (Sum.inl (93, 0)),
    Sum.inr (Sum.inl (198, 40)),
    Sum.inr (Sum.inl (93, 59)),
    Sum.inr (Sum.inl (49, 0)),
    Sum.inr (Sum.inl (95, 0)),
    Sum.inr (Sum.inl (49, 2)),
    Sum.inr (Sum.inl (95, 16)),
    Sum.inr (Sum.inl (49, 12)),
    Sum.inr (Sum.inl (95, 12)),
    Sum.inr (Sum.inl (49, 14)),
    Sum.inr (Sum.inl (95, 28)),
    Sum.inr (Sum.inl (198, 2)),
    Sum.inr (Sum.inl (93, 8)),
    Sum.inr (Sum.inl (198, 42)),
    Sum.inr (Sum.inl (93, 51)),
    Sum.inr (Sum.inl (93, 33)),
    Sum.inr (Sum.inl (198, 59)),
    Sum.inr (Sum.inl (93, 26)),
    Sum.inr (Sum.inl (198, 19)),
    Sum.inr (Sum.inl (95, 62)),
    Sum.inr (Sum.inl (49, 47)),
    Sum.inr (Sum.inl (95, 46)),
    Sum.inr (Sum.inl (49, 45)),
    Sum.inr (Sum.inl (95, 50)),
    Sum.inr (Sum.inl (49, 35)),
    Sum.inr (Sum.inl (95, 34)),
    Sum.inr (Sum.inl (49, 33)),
    Sum.inr (Sum.inl (93, 41)),
    Sum.inr (Sum.inl (198, 57)),
    Sum.inr (Sum.inl (93, 18)),
    Sum.inr (Sum.inl (198, 17)),
    Sum.inr (Sum.inl (136, 0)),
    Sum.inr (Sum.inl (189, 0)),
    Sum.inr (Sum.inl (136, 33)),
    Sum.inr (Sum.inl (189, 12)),
    Sum.inr (Sum.inl (229, 0)),
    Sum.inr (Sum.inl (65, 0)),
    Sum.inr (Sum.inl (229, 24)),
    Sum.inr (Sum.inl (65, 2)),
    Sum.inr (Sum.inl (229, 3)),
    Sum.inr (Sum.inl (65, 12)),
    Sum.inr (Sum.inl (229, 27)),
    Sum.inr (Sum.inl (65, 14)),
    Sum.inr (Sum.inl (136, 18)),
    Sum.inr (Sum.inl (189, 2)),
    Sum.inr (Sum.inl (136, 51)),
    Sum.inr (Sum.inl (189, 14)),
    Sum.inr (Sum.inl (189, 17)),
    Sum.inr (Sum.inl (136, 59)),
    Sum.inr (Sum.inl (189, 29)),
    Sum.inr (Sum.inl (136, 26)),
    Sum.inr (Sum.inl (65, 17)),
    Sum.inr (Sum.inl (229, 59)),
    Sum.inr (Sum.inl (65, 19)),
    Sum.inr (Sum.inl (229, 35)),
    Sum.inr (Sum.inl (65, 29)),
    Sum.inr (Sum.inl (229, 56)),
    Sum.inr (Sum.inl (65, 31)),
    Sum.inr (Sum.inl (229, 32)),
    Sum.inr (Sum.inl (189, 19)),
    Sum.inr (Sum.inl (136, 41)),
    Sum.inr (Sum.inl (189, 31)),
    Sum.inr (Sum.inl (136, 8)),
    Sum.inr (Sum.inr (0, 3)),
    Sum.inr (Sum.inr (478, 20)),
    Sum.inr (Sum.inr (469, 20)),
    Sum.inr (Sum.inr (11, 3)),
    Sum.inr (Sum.inr (74, 20)),
    Sum.inr (Sum.inr (404, 3)),
    Sum.inr (Sum.inr (415, 3)),
    Sum.inr (Sum.inr (65, 20)),
    Sum.inr (Sum.inr (0, 12)),
    Sum.inr (Sum.inr (478, 10)),
    Sum.inr (Sum.inr (469, 10)),
    Sum.inr (Sum.inr (11, 12)),
    Sum.inr (Sum.inr (74, 10)),
    Sum.inr (Sum.inr (404, 12)),
    Sum.inr (Sum.inr (415, 12)),
    Sum.inr (Sum.inr (65, 10)),
    Sum.inr (Sum.inr (0, 10)),
    Sum.inr (Sum.inr (478, 12)),
    Sum.inr (Sum.inr (469, 12)),
    Sum.inr (Sum.inr (11, 10)),
    Sum.inr (Sum.inr (74, 12)),
    Sum.inr (Sum.inr (404, 10)),
    Sum.inr (Sum.inr (415, 10)),
    Sum.inr (Sum.inr (65, 12)),
    Sum.inr (Sum.inr (0, 20)),
    Sum.inr (Sum.inr (478, 3)),
    Sum.inr (Sum.inr (469, 3)),
    Sum.inr (Sum.inr (11, 20)),
    Sum.inr (Sum.inr (74, 3)),
    Sum.inr (Sum.inr (404, 20)),
    Sum.inr (Sum.inr (415, 20)),
    Sum.inr (Sum.inr (65, 3)),
    Sum.inr (Sum.inr (203, 20)),
    Sum.inr (Sum.inr (277, 3)),
    Sum.inr (Sum.inr (286, 3)),
    Sum.inr (Sum.inr (192, 20)),
    Sum.inr (Sum.inr (129, 3)),
    Sum.inr (Sum.inr (351, 20)),
    Sum.inr (Sum.inr (340, 20)),
    Sum.inr (Sum.inr (138, 3)),
    Sum.inr (Sum.inr (203, 10)),
    Sum.inr (Sum.inr (277, 12)),
    Sum.inr (Sum.inr (286, 12)),
    Sum.inr (Sum.inr (192, 10)),
    Sum.inr (Sum.inr (129, 12)),
    Sum.inr (Sum.inr (351, 10)),
    Sum.inr (Sum.inr (340, 10)),
    Sum.inr (Sum.inr (138, 12)),
    Sum.inr (Sum.inr (203, 12)),
    Sum.inr (Sum.inr (277, 10)),
    Sum.inr (Sum.inr (286, 10)),
    Sum.inr (Sum.inr (192, 12)),
    Sum.inr (Sum.inr (129, 10)),
    Sum.inr (Sum.inr (351, 12)),
    Sum.inr (Sum.inr (340, 12)),
    Sum.inr (Sum.inr (138, 10)),
    Sum.inr (Sum.inr (203, 3)),
    Sum.inr (Sum.inr (277, 20)),
    Sum.inr (Sum.inr (286, 20)),
    Sum.inr (Sum.inr (192, 3)),
    Sum.inr (Sum.inr (129, 20)),
    Sum.inr (Sum.inr (351, 3)),
    Sum.inr (Sum.inr (340, 3)),
    Sum.inr (Sum.inr (138, 20)),
    Sum.inr (Sum.inl (110, 0)),
    Sum.inr (Sum.inl (226, 0)),
    Sum.inr (Sum.inl (110, 20)),
    Sum.inr (Sum.inl (226, 24)),
    Sum.inr (Sum.inl (80, 0)),
    Sum.inr (Sum.inl (123, 0)),
    Sum.inr (Sum.inl (80, 2)),
    Sum.inr (Sum.inl (123, 24)),
    Sum.inr (Sum.inl (47, 20)),
    Sum.inr (Sum.inl (197, 36)),
    Sum.inr (Sum.inl (47, 22)),
    Sum.inr (Sum.inl (197, 60)),
    Sum.inr (Sum.inl (190, 2)),
    Sum.inr (Sum.inl (67, 40)),
    Sum.inr (Sum.inl (190, 22)),
    Sum.inr (Sum.inl (67, 42)),
    Sum.inr (Sum.inl (80, 20)),
    Sum.inr (Sum.inl (123, 36)),
    Sum.inr (Sum.inl (80, 22)),
    Sum.inr (Sum.inl (123, 60)),
    Sum.inr (Sum.inl (110, 62)),
    Sum.inr (Sum.inl (226, 62)),
    Sum.inr (Sum.inl (110, 42)),
    Sum.inr (Sum.inl (226, 38))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock018Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨4608 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block018_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock018Input a
    let y := generatedSixthXiShortBlock018Output a
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
theorem generatedSixth_xi_short_block018_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock018Input a
    let y := generatedSixthXiShortBlock018Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block018_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block018_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock018Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block018_certificate a).1
    (generatedSixth_xi_short_block018_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
