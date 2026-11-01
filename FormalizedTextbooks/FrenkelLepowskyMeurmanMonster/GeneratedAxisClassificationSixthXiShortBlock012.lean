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
def generatedSixthXiShortBlock012Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (37, 4)),
    Sum.inr (Sum.inr (315, 7)),
    Sum.inr (Sum.inr (378, 7)),
    Sum.inr (Sum.inr (100, 4)),
    Sum.inr (Sum.inr (442, 7)),
    Sum.inr (Sum.inr (164, 4)),
    Sum.inr (Sum.inr (229, 4)),
    Sum.inr (Sum.inr (507, 7)),
    Sum.inr (Sum.inr (507, 6)),
    Sum.inr (Sum.inr (229, 18)),
    Sum.inr (Sum.inr (164, 18)),
    Sum.inr (Sum.inr (442, 6)),
    Sum.inr (Sum.inr (100, 18)),
    Sum.inr (Sum.inr (378, 6)),
    Sum.inr (Sum.inr (315, 6)),
    Sum.inr (Sum.inr (37, 18)),
    Sum.inr (Sum.inr (46, 18)),
    Sum.inr (Sum.inr (304, 6)),
    Sum.inr (Sum.inr (369, 6)),
    Sum.inr (Sum.inr (111, 18)),
    Sum.inr (Sum.inr (433, 6)),
    Sum.inr (Sum.inr (175, 18)),
    Sum.inr (Sum.inr (238, 18)),
    Sum.inr (Sum.inr (496, 6)),
    Sum.inr (Sum.inr (507, 4)),
    Sum.inr (Sum.inr (229, 7)),
    Sum.inr (Sum.inr (164, 7)),
    Sum.inr (Sum.inr (442, 4)),
    Sum.inr (Sum.inr (100, 7)),
    Sum.inr (Sum.inr (378, 4)),
    Sum.inr (Sum.inr (315, 4)),
    Sum.inr (Sum.inr (37, 7)),
    Sum.inr (Sum.inr (46, 7)),
    Sum.inr (Sum.inr (304, 4)),
    Sum.inr (Sum.inr (369, 4)),
    Sum.inr (Sum.inr (111, 7)),
    Sum.inr (Sum.inr (433, 4)),
    Sum.inr (Sum.inr (175, 7)),
    Sum.inr (Sum.inr (238, 7)),
    Sum.inr (Sum.inr (496, 4)),
    Sum.inr (Sum.inr (64, 7)),
    Sum.inr (Sum.inr (479, 18)),
    Sum.inr (Sum.inr (64, 6)),
    Sum.inr (Sum.inr (479, 4)),
    Sum.inr (Sum.inr (75, 18)),
    Sum.inr (Sum.inr (468, 7)),
    Sum.inr (Sum.inr (75, 4)),
    Sum.inr (Sum.inr (468, 6)),
    Sum.inr (Sum.inr (64, 4)),
    Sum.inr (Sum.inr (479, 6)),
    Sum.inr (Sum.inr (64, 18)),
    Sum.inr (Sum.inr (479, 7)),
    Sum.inr (Sum.inr (75, 6)),
    Sum.inr (Sum.inr (468, 4)),
    Sum.inr (Sum.inr (75, 7)),
    Sum.inr (Sum.inr (468, 18)),
    Sum.inr (Sum.inr (405, 18)),
    Sum.inr (Sum.inr (10, 7)),
    Sum.inr (Sum.inr (405, 4)),
    Sum.inr (Sum.inr (10, 6)),
    Sum.inr (Sum.inr (414, 7)),
    Sum.inr (Sum.inr (1, 18)),
    Sum.inr (Sum.inr (414, 6)),
    Sum.inr (Sum.inr (1, 4)),
    Sum.inr (Sum.inr (405, 6)),
    Sum.inr (Sum.inr (10, 4)),
    Sum.inr (Sum.inr (405, 7)),
    Sum.inr (Sum.inr (10, 18)),
    Sum.inr (Sum.inr (414, 4)),
    Sum.inr (Sum.inr (1, 6)),
    Sum.inr (Sum.inr (414, 18)),
    Sum.inr (Sum.inr (1, 7)),
    Sum.inr (Sum.inr (287, 18)),
    Sum.inr (Sum.inr (128, 7)),
    Sum.inr (Sum.inr (287, 4)),
    Sum.inr (Sum.inr (128, 6)),
    Sum.inr (Sum.inr (276, 7)),
    Sum.inr (Sum.inr (139, 18)),
    Sum.inr (Sum.inr (276, 6)),
    Sum.inr (Sum.inr (139, 4)),
    Sum.inr (Sum.inr (287, 6)),
    Sum.inr (Sum.inr (128, 4)),
    Sum.inr (Sum.inr (287, 7)),
    Sum.inr (Sum.inr (128, 18)),
    Sum.inr (Sum.inr (276, 4)),
    Sum.inr (Sum.inr (139, 6)),
    Sum.inr (Sum.inr (276, 18)),
    Sum.inr (Sum.inr (139, 7)),
    Sum.inr (Sum.inr (202, 7)),
    Sum.inr (Sum.inr (341, 18)),
    Sum.inr (Sum.inr (202, 6)),
    Sum.inr (Sum.inr (341, 4)),
    Sum.inr (Sum.inr (193, 18)),
    Sum.inr (Sum.inr (350, 7)),
    Sum.inr (Sum.inr (193, 4)),
    Sum.inr (Sum.inr (350, 6)),
    Sum.inr (Sum.inr (202, 4)),
    Sum.inr (Sum.inr (341, 6)),
    Sum.inr (Sum.inr (202, 18)),
    Sum.inr (Sum.inr (341, 7)),
    Sum.inr (Sum.inr (193, 6)),
    Sum.inr (Sum.inr (350, 4)),
    Sum.inr (Sum.inr (193, 7)),
    Sum.inr (Sum.inr (350, 18)),
    Sum.inr (Sum.inl (138, 0)),
    Sum.inr (Sum.inl (108, 31)),
    Sum.inr (Sum.inl (108, 19)),
    Sum.inr (Sum.inl (138, 8)),
    Sum.inr (Sum.inl (216, 7)),
    Sum.inr (Sum.inl (154, 32)),
    Sum.inr (Sum.inl (154, 44)),
    Sum.inr (Sum.inl (216, 5)),
    Sum.inr (Sum.inl (138, 34)),
    Sum.inr (Sum.inl (108, 0)),
    Sum.inr (Sum.inl (108, 12)),
    Sum.inr (Sum.inl (138, 42)),
    Sum.inr (Sum.inl (216, 40)),
    Sum.inr (Sum.inl (154, 29)),
    Sum.inr (Sum.inl (154, 17)),
    Sum.inr (Sum.inl (216, 42)),
    Sum.inr (Sum.inl (91, 51)),
    Sum.inr (Sum.inl (125, 47)),
    Sum.inr (Sum.inl (125, 35)),
    Sum.inr (Sum.inl (91, 33)),
    Sum.inr (Sum.inl (186, 35)),
    Sum.inr (Sum.inl (41, 3)),
    Sum.inr (Sum.inl (41, 0)),
    Sum.inr (Sum.inl (186, 33)),
    Sum.inr (Sum.inl (91, 55)),
    Sum.inr (Sum.inl (125, 14)),
    Sum.inr (Sum.inl (125, 2)),
    Sum.inr (Sum.inl (91, 37)),
    Sum.inr (Sum.inl (186, 2)),
    Sum.inr (Sum.inl (41, 11)),
    Sum.inr (Sum.inl (41, 8)),
    Sum.inr (Sum.inl (186, 0)),
    Sum.inr (Sum.inl (216, 47)),
    Sum.inr (Sum.inl (154, 0)),
    Sum.inr (Sum.inl (154, 12)),
    Sum.inr (Sum.inl (216, 45)),
    Sum.inr (Sum.inl (138, 59)),
    Sum.inr (Sum.inl (108, 29)),
    Sum.inr (Sum.inl (108, 17)),
    Sum.inr (Sum.inl (138, 51)),
    Sum.inr (Sum.inl (216, 0)),
    Sum.inr (Sum.inl (154, 61)),
    Sum.inr (Sum.inl (154, 49)),
    Sum.inr (Sum.inl (216, 2)),
    Sum.inr (Sum.inl (138, 25)),
    Sum.inr (Sum.inl (108, 2)),
    Sum.inr (Sum.inl (108, 14)),
    Sum.inr (Sum.inl (138, 17)),
    Sum.inr (Sum.inl (186, 55)),
    Sum.inr (Sum.inl (41, 39)),
    Sum.inr (Sum.inl (41, 36)),
    Sum.inr (Sum.inl (186, 53)),
    Sum.inr (Sum.inl (91, 18)),
    Sum.inr (Sum.inl (125, 45)),
    Sum.inr (Sum.inl (125, 33)),
    Sum.inr (Sum.inl (91, 0)),
    Sum.inr (Sum.inl (186, 22)),
    Sum.inr (Sum.inl (41, 47)),
    Sum.inr (Sum.inl (41, 44)),
    Sum.inr (Sum.inl (186, 20)),
    Sum.inr (Sum.inl (91, 22)),
    Sum.inr (Sum.inl (125, 12)),
    Sum.inr (Sum.inl (125, 0)),
    Sum.inr (Sum.inl (91, 4)),
    Sum.inr (Sum.inl (106, 10)),
    Sum.inr (Sum.inl (184, 40)),
    Sum.inr (Sum.inl (106, 58)),
    Sum.inr (Sum.inl (184, 19)),
    Sum.inr (Sum.inl (127, 40)),
    Sum.inr (Sum.inl (218, 55)),
    Sum.inr (Sum.inl (127, 42)),
    Sum.inr (Sum.inl (218, 23)),
    Sum.inr (Sum.inl (127, 36)),
    Sum.inr (Sum.inl (218, 59)),
    Sum.inr (Sum.inl (127, 38)),
    Sum.inr (Sum.inl (218, 27)),
    Sum.inr (Sum.inl (106, 8)),
    Sum.inr (Sum.inl (184, 32)),
    Sum.inr (Sum.inl (106, 56)),
    Sum.inr (Sum.inl (184, 27)),
    Sum.inr (Sum.inl (74, 49)),
    Sum.inr (Sum.inl (194, 13)),
    Sum.inr (Sum.inl (74, 16)),
    Sum.inr (Sum.inl (194, 1)),
    Sum.inr (Sum.inl (117, 25)),
    Sum.inr (Sum.inl (42, 7)),
    Sum.inr (Sum.inl (117, 1)),
    Sum.inr (Sum.inl (42, 5)),
    Sum.inr (Sum.inl (117, 26)),
    Sum.inr (Sum.inl (42, 11)),
    Sum.inr (Sum.inl (117, 2)),
    Sum.inr (Sum.inl (42, 9)),
    Sum.inr (Sum.inl (74, 35)),
    Sum.inr (Sum.inl (194, 15)),
    Sum.inr (Sum.inl (74, 2)),
    Sum.inr (Sum.inl (194, 3)),
    Sum.inr (Sum.inl (184, 10)),
    Sum.inr (Sum.inl (106, 61)),
    Sum.inr (Sum.inl (184, 49)),
    Sum.inr (Sum.inl (106, 13)),
    Sum.inr (Sum.inl (218, 10)),
    Sum.inr (Sum.inl (127, 55)),
    Sum.inr (Sum.inl (218, 42)),
    Sum.inr (Sum.inl (127, 53)),
    Sum.inr (Sum.inl (218, 6)),
    Sum.inr (Sum.inl (127, 59)),
    Sum.inr (Sum.inl (218, 38)),
    Sum.inr (Sum.inl (127, 57)),
    Sum.inr (Sum.inl (184, 2)),
    Sum.inr (Sum.inl (106, 63)),
    Sum.inr (Sum.inl (184, 57)),
    Sum.inr (Sum.inl (106, 15)),
    Sum.inr (Sum.inl (194, 44)),
    Sum.inr (Sum.inl (74, 53)),
    Sum.inr (Sum.inl (194, 32)),
    Sum.inr (Sum.inl (74, 20)),
    Sum.inr (Sum.inl (42, 38)),
    Sum.inr (Sum.inl (117, 29)),
    Sum.inr (Sum.inl (42, 36)),
    Sum.inr (Sum.inl (117, 5)),
    Sum.inr (Sum.inl (42, 42)),
    Sum.inr (Sum.inl (117, 30)),
    Sum.inr (Sum.inl (42, 40)),
    Sum.inr (Sum.inl (117, 6)),
    Sum.inr (Sum.inl (194, 46)),
    Sum.inr (Sum.inl (74, 39)),
    Sum.inr (Sum.inl (194, 34)),
    Sum.inr (Sum.inl (74, 6)),
    Sum.inr (Sum.inl (90, 40)),
    Sum.inr (Sum.inl (217, 55)),
    Sum.inr (Sum.inl (130, 57)),
    Sum.inr (Sum.inl (201, 11)),
    Sum.inr (Sum.inl (115, 48)),
    Sum.inr (Sum.inl (164, 47)),
    Sum.inr (Sum.inl (75, 29)),
    Sum.inr (Sum.inl (43, 13)),
    Sum.inr (Sum.inl (115, 51)),
    Sum.inr (Sum.inl (164, 35)),
    Sum.inr (Sum.inl (75, 17)),
    Sum.inr (Sum.inl (43, 1)),
    Sum.inr (Sum.inl (90, 42)),
    Sum.inr (Sum.inl (217, 37)),
    Sum.inr (Sum.inl (130, 59)),
    Sum.inr (Sum.inl (201, 3)),
    Sum.inr (Sum.inl (130, 48)),
    Sum.inr (Sum.inl (201, 47)),
    Sum.inr (Sum.inl (90, 7)),
    Sum.inr (Sum.inl (217, 19)),
    Sum.inr (Sum.inl (75, 31)),
    Sum.inr (Sum.inl (43, 31)),
    Sum.inr (Sum.inl (115, 56)),
    Sum.inr (Sum.inl (164, 15))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock012Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨3072 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block012_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock012Input a
    let y := generatedSixthXiShortBlock012Output a
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
theorem generatedSixth_xi_short_block012_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock012Input a
    let y := generatedSixthXiShortBlock012Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block012_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block012_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock012Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block012_certificate a).1
    (generatedSixth_xi_short_block012_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
