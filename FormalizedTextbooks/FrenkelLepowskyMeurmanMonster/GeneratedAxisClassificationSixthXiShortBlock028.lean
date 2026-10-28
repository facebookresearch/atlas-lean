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
def generatedSixthXiShortBlock028Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (279, 11)),
    Sum.inr (Sum.inr (406, 11)),
    Sum.inr (Sum.inr (471, 1)),
    Sum.inr (Sum.inr (342, 1)),
    Sum.inr (Sum.inr (131, 11)),
    Sum.inr (Sum.inr (2, 11)),
    Sum.inr (Sum.inr (67, 1)),
    Sum.inr (Sum.inr (194, 1)),
    Sum.inr (Sum.inr (2, 15)),
    Sum.inr (Sum.inr (131, 15)),
    Sum.inr (Sum.inr (194, 22)),
    Sum.inr (Sum.inr (67, 22)),
    Sum.inr (Sum.inr (406, 15)),
    Sum.inr (Sum.inr (279, 15)),
    Sum.inr (Sum.inr (342, 22)),
    Sum.inr (Sum.inr (471, 22)),
    Sum.inr (Sum.inr (413, 15)),
    Sum.inr (Sum.inr (284, 15)),
    Sum.inr (Sum.inr (349, 22)),
    Sum.inr (Sum.inr (476, 22)),
    Sum.inr (Sum.inr (9, 15)),
    Sum.inr (Sum.inr (136, 15)),
    Sum.inr (Sum.inr (201, 22)),
    Sum.inr (Sum.inr (72, 22)),
    Sum.inr (Sum.inr (72, 15)),
    Sum.inr (Sum.inr (201, 15)),
    Sum.inr (Sum.inr (136, 22)),
    Sum.inr (Sum.inr (9, 22)),
    Sum.inr (Sum.inr (476, 15)),
    Sum.inr (Sum.inr (349, 15)),
    Sum.inr (Sum.inr (284, 22)),
    Sum.inr (Sum.inr (413, 22)),
    Sum.inr (Sum.inr (471, 15)),
    Sum.inr (Sum.inr (342, 15)),
    Sum.inr (Sum.inr (279, 22)),
    Sum.inr (Sum.inr (406, 22)),
    Sum.inr (Sum.inr (67, 15)),
    Sum.inr (Sum.inr (194, 15)),
    Sum.inr (Sum.inr (131, 22)),
    Sum.inr (Sum.inr (2, 22)),
    Sum.inr (Sum.inr (194, 0)),
    Sum.inr (Sum.inr (342, 0)),
    Sum.inr (Sum.inr (349, 0)),
    Sum.inr (Sum.inr (201, 0)),
    Sum.inr (Sum.inr (67, 8)),
    Sum.inr (Sum.inr (471, 8)),
    Sum.inr (Sum.inr (476, 8)),
    Sum.inr (Sum.inr (72, 8)),
    Sum.inr (Sum.inr (2, 0)),
    Sum.inr (Sum.inr (406, 0)),
    Sum.inr (Sum.inr (413, 0)),
    Sum.inr (Sum.inr (9, 0)),
    Sum.inr (Sum.inr (131, 8)),
    Sum.inr (Sum.inr (279, 8)),
    Sum.inr (Sum.inr (284, 8)),
    Sum.inr (Sum.inr (136, 8)),
    Sum.inr (Sum.inr (136, 0)),
    Sum.inr (Sum.inr (284, 0)),
    Sum.inr (Sum.inr (279, 0)),
    Sum.inr (Sum.inr (131, 0)),
    Sum.inr (Sum.inr (9, 8)),
    Sum.inr (Sum.inr (413, 8)),
    Sum.inr (Sum.inr (406, 8)),
    Sum.inr (Sum.inr (2, 8)),
    Sum.inr (Sum.inr (72, 0)),
    Sum.inr (Sum.inr (476, 0)),
    Sum.inr (Sum.inr (471, 0)),
    Sum.inr (Sum.inr (67, 0)),
    Sum.inr (Sum.inr (201, 8)),
    Sum.inr (Sum.inr (349, 8)),
    Sum.inr (Sum.inr (342, 8)),
    Sum.inr (Sum.inr (194, 8)),
    Sum.inr (Sum.inr (67, 13)),
    Sum.inr (Sum.inr (471, 13)),
    Sum.inr (Sum.inr (476, 13)),
    Sum.inr (Sum.inr (72, 13)),
    Sum.inr (Sum.inr (194, 23)),
    Sum.inr (Sum.inr (342, 23)),
    Sum.inr (Sum.inr (349, 23)),
    Sum.inr (Sum.inr (201, 23)),
    Sum.inr (Sum.inr (131, 13)),
    Sum.inr (Sum.inr (279, 13)),
    Sum.inr (Sum.inr (284, 13)),
    Sum.inr (Sum.inr (136, 13)),
    Sum.inr (Sum.inr (2, 23)),
    Sum.inr (Sum.inr (406, 23)),
    Sum.inr (Sum.inr (413, 23)),
    Sum.inr (Sum.inr (9, 23)),
    Sum.inr (Sum.inr (9, 13)),
    Sum.inr (Sum.inr (413, 13)),
    Sum.inr (Sum.inr (406, 13)),
    Sum.inr (Sum.inr (2, 13)),
    Sum.inr (Sum.inr (136, 23)),
    Sum.inr (Sum.inr (284, 23)),
    Sum.inr (Sum.inr (279, 23)),
    Sum.inr (Sum.inr (131, 23)),
    Sum.inr (Sum.inr (201, 13)),
    Sum.inr (Sum.inr (349, 13)),
    Sum.inr (Sum.inr (342, 13)),
    Sum.inr (Sum.inr (194, 13)),
    Sum.inr (Sum.inr (72, 23)),
    Sum.inr (Sum.inr (476, 23)),
    Sum.inr (Sum.inr (471, 23)),
    Sum.inr (Sum.inr (67, 23)),
    Sum.inr (Sum.inl (163, 20)),
    Sum.inr (Sum.inl (129, 18)),
    Sum.inr (Sum.inl (129, 30)),
    Sum.inr (Sum.inl (163, 28)),
    Sum.inr (Sum.inl (116, 24)),
    Sum.inr (Sum.inl (202, 16)),
    Sum.inr (Sum.inl (202, 28)),
    Sum.inr (Sum.inl (116, 26)),
    Sum.inr (Sum.inl (56, 9)),
    Sum.inr (Sum.inl (60, 18)),
    Sum.inr (Sum.inl (60, 30)),
    Sum.inr (Sum.inl (56, 27)),
    Sum.inr (Sum.inl (222, 36)),
    Sum.inr (Sum.inl (105, 48)),
    Sum.inr (Sum.inl (105, 51)),
    Sum.inr (Sum.inl (222, 38)),
    Sum.inr (Sum.inl (116, 20)),
    Sum.inr (Sum.inl (202, 48)),
    Sum.inr (Sum.inl (202, 60)),
    Sum.inr (Sum.inl (116, 22)),
    Sum.inr (Sum.inl (163, 47)),
    Sum.inr (Sum.inl (129, 16)),
    Sum.inr (Sum.inl (129, 28)),
    Sum.inr (Sum.inl (163, 39)),
    Sum.inr (Sum.inl (222, 12)),
    Sum.inr (Sum.inl (105, 36)),
    Sum.inr (Sum.inl (105, 39)),
    Sum.inr (Sum.inl (222, 14)),
    Sum.inr (Sum.inl (56, 40)),
    Sum.inr (Sum.inl (60, 16)),
    Sum.inr (Sum.inl (60, 28)),
    Sum.inr (Sum.inl (56, 58)),
    Sum.inr (Sum.inl (163, 6)),
    Sum.inr (Sum.inl (129, 61)),
    Sum.inr (Sum.inl (129, 49)),
    Sum.inr (Sum.inl (163, 14)),
    Sum.inr (Sum.inl (116, 55)),
    Sum.inr (Sum.inl (202, 2)),
    Sum.inr (Sum.inl (202, 14)),
    Sum.inr (Sum.inl (116, 53)),
    Sum.inr (Sum.inl (56, 1)),
    Sum.inr (Sum.inl (60, 3)),
    Sum.inr (Sum.inl (60, 15)),
    Sum.inr (Sum.inl (56, 19)),
    Sum.inr (Sum.inl (222, 33)),
    Sum.inr (Sum.inl (105, 16)),
    Sum.inr (Sum.inl (105, 19)),
    Sum.inr (Sum.inl (222, 35)),
    Sum.inr (Sum.inl (116, 59)),
    Sum.inr (Sum.inl (202, 34)),
    Sum.inr (Sum.inl (202, 46)),
    Sum.inr (Sum.inl (116, 57)),
    Sum.inr (Sum.inl (163, 61)),
    Sum.inr (Sum.inl (129, 63)),
    Sum.inr (Sum.inl (129, 51)),
    Sum.inr (Sum.inl (163, 53)),
    Sum.inr (Sum.inl (222, 9)),
    Sum.inr (Sum.inl (105, 4)),
    Sum.inr (Sum.inl (105, 7)),
    Sum.inr (Sum.inl (222, 11)),
    Sum.inr (Sum.inl (56, 32)),
    Sum.inr (Sum.inl (60, 1)),
    Sum.inr (Sum.inl (60, 13)),
    Sum.inr (Sum.inl (56, 50)),
    Sum.inr (Sum.inl (42, 18)),
    Sum.inr (Sum.inl (184, 20)),
    Sum.inr (Sum.inl (42, 30)),
    Sum.inr (Sum.inl (184, 28)),
    Sum.inr (Sum.inl (184, 5)),
    Sum.inr (Sum.inl (42, 61)),
    Sum.inr (Sum.inl (184, 13)),
    Sum.inr (Sum.inl (42, 49)),
    Sum.inr (Sum.inl (74, 13)),
    Sum.inr (Sum.inl (127, 13)),
    Sum.inr (Sum.inl (74, 31)),
    Sum.inr (Sum.inl (127, 1)),
    Sum.inr (Sum.inl (127, 28)),
    Sum.inr (Sum.inl (74, 58)),
    Sum.inr (Sum.inl (127, 16)),
    Sum.inr (Sum.inl (74, 40)),
    Sum.inr (Sum.inl (194, 24)),
    Sum.inr (Sum.inl (218, 16)),
    Sum.inr (Sum.inl (194, 26)),
    Sum.inr (Sum.inl (218, 28)),
    Sum.inr (Sum.inl (218, 1)),
    Sum.inr (Sum.inl (194, 55)),
    Sum.inr (Sum.inl (218, 13)),
    Sum.inr (Sum.inl (194, 53)),
    Sum.inr (Sum.inl (117, 52)),
    Sum.inr (Sum.inl (106, 19)),
    Sum.inr (Sum.inl (117, 55)),
    Sum.inr (Sum.inl (106, 17)),
    Sum.inr (Sum.inl (106, 22)),
    Sum.inr (Sum.inl (117, 43)),
    Sum.inr (Sum.inl (106, 20)),
    Sum.inr (Sum.inl (117, 40)),
    Sum.inr (Sum.inl (194, 20)),
    Sum.inr (Sum.inl (218, 48)),
    Sum.inr (Sum.inl (194, 22)),
    Sum.inr (Sum.inl (218, 60)),
    Sum.inr (Sum.inl (218, 33)),
    Sum.inr (Sum.inl (194, 59)),
    Sum.inr (Sum.inl (218, 45)),
    Sum.inr (Sum.inl (194, 57)),
    Sum.inr (Sum.inl (117, 44)),
    Sum.inr (Sum.inl (106, 35)),
    Sum.inr (Sum.inl (117, 47)),
    Sum.inr (Sum.inl (106, 33)),
    Sum.inr (Sum.inl (106, 38)),
    Sum.inr (Sum.inl (117, 51)),
    Sum.inr (Sum.inl (106, 36)),
    Sum.inr (Sum.inl (117, 48)),
    Sum.inr (Sum.inl (42, 16)),
    Sum.inr (Sum.inl (184, 47)),
    Sum.inr (Sum.inl (42, 28)),
    Sum.inr (Sum.inl (184, 39)),
    Sum.inr (Sum.inl (184, 62)),
    Sum.inr (Sum.inl (42, 63)),
    Sum.inr (Sum.inl (184, 54)),
    Sum.inr (Sum.inl (42, 51)),
    Sum.inr (Sum.inl (74, 44)),
    Sum.inr (Sum.inl (127, 15)),
    Sum.inr (Sum.inl (74, 62)),
    Sum.inr (Sum.inl (127, 3)),
    Sum.inr (Sum.inl (127, 30)),
    Sum.inr (Sum.inl (74, 27)),
    Sum.inr (Sum.inl (127, 18)),
    Sum.inr (Sum.inl (74, 9)),
    Sum.inr (Sum.inl (111, 2)),
    Sum.inr (Sum.inl (54, 29)),
    Sum.inr (Sum.inl (73, 12)),
    Sum.inr (Sum.inl (230, 51)),
    Sum.inr (Sum.inl (111, 60)),
    Sum.inr (Sum.inl (54, 61)),
    Sum.inr (Sum.inl (73, 35)),
    Sum.inr (Sum.inl (230, 17)),
    Sum.inr (Sum.inl (92, 23)),
    Sum.inr (Sum.inl (156, 63)),
    Sum.inr (Sum.inl (176, 45)),
    Sum.inr (Sum.inl (107, 9)),
    Sum.inr (Sum.inl (92, 32)),
    Sum.inr (Sum.inl (156, 29)),
    Sum.inr (Sum.inl (176, 12)),
    Sum.inr (Sum.inl (107, 13)),
    Sum.inr (Sum.inl (73, 14)),
    Sum.inr (Sum.inl (230, 59)),
    Sum.inr (Sum.inl (111, 14)),
    Sum.inr (Sum.inl (54, 17)),
    Sum.inr (Sum.inl (73, 33)),
    Sum.inr (Sum.inl (230, 25)),
    Sum.inr (Sum.inl (111, 48)),
    Sum.inr (Sum.inl (54, 49))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock028Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨7168 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block028_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock028Input a
    let y := generatedSixthXiShortBlock028Output a
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
theorem generatedSixth_xi_short_block028_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock028Input a
    let y := generatedSixthXiShortBlock028Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block028_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block028_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock028Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block028_certificate a).1
    (generatedSixth_xi_short_block028_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
