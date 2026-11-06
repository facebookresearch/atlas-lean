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
def generatedSixthXiShortBlock031Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (90, 19)),
    Sum.inr (Sum.inl (75, 15)),
    Sum.inr (Sum.inl (75, 3)),
    Sum.inr (Sum.inl (90, 17)),
    Sum.inr (Sum.inl (201, 14)),
    Sum.inr (Sum.inl (164, 46)),
    Sum.inr (Sum.inl (164, 34)),
    Sum.inr (Sum.inl (201, 6)),
    Sum.inr (Sum.inl (217, 4)),
    Sum.inr (Sum.inl (43, 2)),
    Sum.inr (Sum.inl (43, 14)),
    Sum.inr (Sum.inl (217, 22)),
    Sum.inr (Sum.inl (130, 62)),
    Sum.inr (Sum.inl (115, 55)),
    Sum.inr (Sum.inl (115, 52)),
    Sum.inr (Sum.inl (130, 60)),
    Sum.inr (Sum.inl (217, 32)),
    Sum.inr (Sum.inl (43, 16)),
    Sum.inr (Sum.inl (43, 28)),
    Sum.inr (Sum.inl (217, 50)),
    Sum.inr (Sum.inl (130, 55)),
    Sum.inr (Sum.inl (115, 63)),
    Sum.inr (Sum.inl (115, 60)),
    Sum.inr (Sum.inl (130, 53)),
    Sum.inr (Sum.inl (130, 42)),
    Sum.inr (Sum.inl (115, 35)),
    Sum.inr (Sum.inl (115, 32)),
    Sum.inr (Sum.inl (130, 40)),
    Sum.inr (Sum.inl (217, 58)),
    Sum.inr (Sum.inl (43, 60)),
    Sum.inr (Sum.inl (43, 48)),
    Sum.inr (Sum.inl (217, 40)),
    Sum.inr (Sum.inl (130, 35)),
    Sum.inr (Sum.inl (115, 43)),
    Sum.inr (Sum.inl (115, 40)),
    Sum.inr (Sum.inl (130, 33)),
    Sum.inr (Sum.inl (217, 30)),
    Sum.inr (Sum.inl (43, 46)),
    Sum.inr (Sum.inl (43, 34)),
    Sum.inr (Sum.inl (217, 12)),
    Sum.inr (Sum.inl (60, 37)),
    Sum.inr (Sum.inl (163, 60)),
    Sum.inr (Sum.inl (60, 41)),
    Sum.inr (Sum.inl (163, 52)),
    Sum.inr (Sum.inl (222, 25)),
    Sum.inr (Sum.inl (202, 39)),
    Sum.inr (Sum.inl (222, 27)),
    Sum.inr (Sum.inl (202, 43)),
    Sum.inr (Sum.inl (222, 49)),
    Sum.inr (Sum.inl (202, 7)),
    Sum.inr (Sum.inl (222, 51)),
    Sum.inr (Sum.inl (202, 11)),
    Sum.inr (Sum.inl (60, 39)),
    Sum.inr (Sum.inl (163, 7)),
    Sum.inr (Sum.inl (60, 43)),
    Sum.inr (Sum.inl (163, 15)),
    Sum.inr (Sum.inl (56, 60)),
    Sum.inr (Sum.inl (129, 21)),
    Sum.inr (Sum.inl (56, 46)),
    Sum.inr (Sum.inl (129, 25)),
    Sum.inr (Sum.inl (105, 45)),
    Sum.inr (Sum.inl (116, 21)),
    Sum.inr (Sum.inl (105, 46)),
    Sum.inr (Sum.inl (116, 23)),
    Sum.inr (Sum.inl (105, 57)),
    Sum.inr (Sum.inl (116, 25)),
    Sum.inr (Sum.inl (105, 58)),
    Sum.inr (Sum.inl (116, 27)),
    Sum.inr (Sum.inl (56, 29)),
    Sum.inr (Sum.inl (129, 23)),
    Sum.inr (Sum.inl (56, 15)),
    Sum.inr (Sum.inl (129, 27)),
    Sum.inr (Sum.inl (163, 29)),
    Sum.inr (Sum.inl (60, 58)),
    Sum.inr (Sum.inl (163, 21)),
    Sum.inr (Sum.inl (60, 54)),
    Sum.inr (Sum.inl (202, 25)),
    Sum.inr (Sum.inl (222, 54)),
    Sum.inr (Sum.inl (202, 21)),
    Sum.inr (Sum.inl (222, 52)),
    Sum.inr (Sum.inl (202, 57)),
    Sum.inr (Sum.inl (222, 30)),
    Sum.inr (Sum.inl (202, 53)),
    Sum.inr (Sum.inl (222, 28)),
    Sum.inr (Sum.inl (163, 38)),
    Sum.inr (Sum.inl (60, 56)),
    Sum.inr (Sum.inl (163, 46)),
    Sum.inr (Sum.inl (60, 52)),
    Sum.inr (Sum.inl (129, 52)),
    Sum.inr (Sum.inl (56, 7)),
    Sum.inr (Sum.inl (129, 56)),
    Sum.inr (Sum.inl (56, 21)),
    Sum.inr (Sum.inl (116, 52)),
    Sum.inr (Sum.inl (105, 26)),
    Sum.inr (Sum.inl (116, 54)),
    Sum.inr (Sum.inl (105, 25)),
    Sum.inr (Sum.inl (116, 56)),
    Sum.inr (Sum.inl (105, 14)),
    Sum.inr (Sum.inl (116, 58)),
    Sum.inr (Sum.inl (105, 13)),
    Sum.inr (Sum.inl (129, 54)),
    Sum.inr (Sum.inl (56, 38)),
    Sum.inr (Sum.inl (129, 58)),
    Sum.inr (Sum.inl (56, 52)),
    Sum.inr (Sum.inl (184, 12)),
    Sum.inr (Sum.inl (127, 10)),
    Sum.inr (Sum.inl (127, 6)),
    Sum.inr (Sum.inl (184, 4)),
    Sum.inr (Sum.inl (184, 46)),
    Sum.inr (Sum.inl (127, 21)),
    Sum.inr (Sum.inl (127, 25)),
    Sum.inr (Sum.inl (184, 38)),
    Sum.inr (Sum.inl (106, 34)),
    Sum.inr (Sum.inl (218, 8)),
    Sum.inr (Sum.inl (218, 4)),
    Sum.inr (Sum.inl (106, 32)),
    Sum.inr (Sum.inl (106, 21)),
    Sum.inr (Sum.inl (218, 53)),
    Sum.inr (Sum.inl (218, 57)),
    Sum.inr (Sum.inl (106, 23)),
    Sum.inr (Sum.inl (106, 18)),
    Sum.inr (Sum.inl (218, 40)),
    Sum.inr (Sum.inl (218, 36)),
    Sum.inr (Sum.inl (106, 16)),
    Sum.inr (Sum.inl (106, 37)),
    Sum.inr (Sum.inl (218, 21)),
    Sum.inr (Sum.inl (218, 25)),
    Sum.inr (Sum.inl (106, 39)),
    Sum.inr (Sum.inl (184, 55)),
    Sum.inr (Sum.inl (127, 8)),
    Sum.inr (Sum.inl (127, 4)),
    Sum.inr (Sum.inl (184, 63)),
    Sum.inr (Sum.inl (184, 21)),
    Sum.inr (Sum.inl (127, 23)),
    Sum.inr (Sum.inl (127, 27)),
    Sum.inr (Sum.inl (184, 29)),
    Sum.inr (Sum.inl (74, 52)),
    Sum.inr (Sum.inl (42, 37)),
    Sum.inr (Sum.inl (42, 41)),
    Sum.inr (Sum.inl (74, 38)),
    Sum.inr (Sum.inl (74, 48)),
    Sum.inr (Sum.inl (42, 4)),
    Sum.inr (Sum.inl (42, 8)),
    Sum.inr (Sum.inl (74, 34)),
    Sum.inr (Sum.inl (194, 37)),
    Sum.inr (Sum.inl (117, 13)),
    Sum.inr (Sum.inl (117, 14)),
    Sum.inr (Sum.inl (194, 39)),
    Sum.inr (Sum.inl (194, 4)),
    Sum.inr (Sum.inl (117, 9)),
    Sum.inr (Sum.inl (117, 10)),
    Sum.inr (Sum.inl (194, 6)),
    Sum.inr (Sum.inl (194, 41)),
    Sum.inr (Sum.inl (117, 21)),
    Sum.inr (Sum.inl (117, 22)),
    Sum.inr (Sum.inl (194, 43)),
    Sum.inr (Sum.inl (194, 8)),
    Sum.inr (Sum.inl (117, 17)),
    Sum.inr (Sum.inl (117, 18)),
    Sum.inr (Sum.inl (194, 10)),
    Sum.inr (Sum.inl (74, 21)),
    Sum.inr (Sum.inl (42, 39)),
    Sum.inr (Sum.inl (42, 43)),
    Sum.inr (Sum.inl (74, 7)),
    Sum.inr (Sum.inl (74, 17)),
    Sum.inr (Sum.inl (42, 6)),
    Sum.inr (Sum.inl (42, 10)),
    Sum.inr (Sum.inl (74, 3)),
    Sum.inr (Sum.inr (144, 1)),
    Sum.inr (Sum.inr (260, 1)),
    Sum.inr (Sum.inr (271, 1)),
    Sum.inr (Sum.inr (155, 1)),
    Sum.inr (Sum.inr (218, 1)),
    Sum.inr (Sum.inr (334, 1)),
    Sum.inr (Sum.inr (325, 1)),
    Sum.inr (Sum.inr (209, 1)),
    Sum.inr (Sum.inr (80, 11)),
    Sum.inr (Sum.inr (452, 11)),
    Sum.inr (Sum.inr (463, 11)),
    Sum.inr (Sum.inr (91, 11)),
    Sum.inr (Sum.inr (26, 11)),
    Sum.inr (Sum.inr (398, 11)),
    Sum.inr (Sum.inr (389, 11)),
    Sum.inr (Sum.inr (17, 11)),
    Sum.inr (Sum.inr (17, 1)),
    Sum.inr (Sum.inr (389, 1)),
    Sum.inr (Sum.inr (398, 1)),
    Sum.inr (Sum.inr (26, 1)),
    Sum.inr (Sum.inr (91, 1)),
    Sum.inr (Sum.inr (463, 1)),
    Sum.inr (Sum.inr (452, 1)),
    Sum.inr (Sum.inr (80, 1)),
    Sum.inr (Sum.inr (209, 11)),
    Sum.inr (Sum.inr (325, 11)),
    Sum.inr (Sum.inr (334, 11)),
    Sum.inr (Sum.inr (218, 11)),
    Sum.inr (Sum.inr (155, 11)),
    Sum.inr (Sum.inr (271, 11)),
    Sum.inr (Sum.inr (260, 11)),
    Sum.inr (Sum.inr (144, 11)),
    Sum.inr (Sum.inr (80, 15)),
    Sum.inr (Sum.inr (452, 15)),
    Sum.inr (Sum.inr (463, 15)),
    Sum.inr (Sum.inr (91, 15)),
    Sum.inr (Sum.inr (26, 15)),
    Sum.inr (Sum.inr (398, 15)),
    Sum.inr (Sum.inr (389, 15)),
    Sum.inr (Sum.inr (17, 15)),
    Sum.inr (Sum.inr (144, 22)),
    Sum.inr (Sum.inr (260, 22)),
    Sum.inr (Sum.inr (271, 22)),
    Sum.inr (Sum.inr (155, 22)),
    Sum.inr (Sum.inr (218, 22)),
    Sum.inr (Sum.inr (334, 22)),
    Sum.inr (Sum.inr (325, 22)),
    Sum.inr (Sum.inr (209, 22)),
    Sum.inr (Sum.inr (209, 15)),
    Sum.inr (Sum.inr (325, 15)),
    Sum.inr (Sum.inr (334, 15)),
    Sum.inr (Sum.inr (218, 15)),
    Sum.inr (Sum.inr (155, 15)),
    Sum.inr (Sum.inr (271, 15)),
    Sum.inr (Sum.inr (260, 15)),
    Sum.inr (Sum.inr (144, 15)),
    Sum.inr (Sum.inr (17, 22)),
    Sum.inr (Sum.inr (389, 22)),
    Sum.inr (Sum.inr (398, 22)),
    Sum.inr (Sum.inr (26, 22)),
    Sum.inr (Sum.inr (91, 22)),
    Sum.inr (Sum.inr (463, 22)),
    Sum.inr (Sum.inr (452, 22)),
    Sum.inr (Sum.inr (80, 22)),
    Sum.inr (Sum.inr (144, 13)),
    Sum.inr (Sum.inr (17, 0)),
    Sum.inr (Sum.inr (80, 13)),
    Sum.inr (Sum.inr (209, 0)),
    Sum.inr (Sum.inr (260, 13)),
    Sum.inr (Sum.inr (389, 0)),
    Sum.inr (Sum.inr (452, 13)),
    Sum.inr (Sum.inr (325, 0)),
    Sum.inr (Sum.inr (271, 13)),
    Sum.inr (Sum.inr (398, 0)),
    Sum.inr (Sum.inr (463, 13)),
    Sum.inr (Sum.inr (334, 0)),
    Sum.inr (Sum.inr (155, 13)),
    Sum.inr (Sum.inr (26, 0)),
    Sum.inr (Sum.inr (91, 13)),
    Sum.inr (Sum.inr (218, 0)),
    Sum.inr (Sum.inr (17, 8)),
    Sum.inr (Sum.inr (144, 23)),
    Sum.inr (Sum.inr (209, 8)),
    Sum.inr (Sum.inr (80, 23)),
    Sum.inr (Sum.inr (389, 8)),
    Sum.inr (Sum.inr (260, 23)),
    Sum.inr (Sum.inr (325, 8)),
    Sum.inr (Sum.inr (452, 23))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock031Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨7936 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block031_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock031Input a
    let y := generatedSixthXiShortBlock031Output a
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
theorem generatedSixth_xi_short_block031_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock031Input a
    let y := generatedSixthXiShortBlock031Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block031_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block031_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock031Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block031_certificate a).1
    (generatedSixth_xi_short_block031_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
