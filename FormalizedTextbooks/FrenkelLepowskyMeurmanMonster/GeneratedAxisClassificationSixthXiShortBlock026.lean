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
def generatedSixthXiShortBlock026Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (229, 19)),
    Sum.inr (Sum.inl (65, 51)),
    Sum.inr (Sum.inl (49, 44)),
    Sum.inr (Sum.inl (95, 44)),
    Sum.inr (Sum.inl (136, 50)),
    Sum.inr (Sum.inl (189, 53)),
    Sum.inr (Sum.inl (198, 50)),
    Sum.inr (Sum.inl (93, 39)),
    Sum.inr (Sum.inl (198, 9)),
    Sum.inr (Sum.inl (93, 6)),
    Sum.inr (Sum.inl (136, 9)),
    Sum.inr (Sum.inl (189, 36)),
    Sum.inr (Sum.inl (49, 3)),
    Sum.inr (Sum.inl (95, 18)),
    Sum.inr (Sum.inl (229, 40)),
    Sum.inr (Sum.inl (65, 34)),
    Sum.inr (Sum.inl (49, 15)),
    Sum.inr (Sum.inl (95, 30)),
    Sum.inr (Sum.inl (229, 43)),
    Sum.inr (Sum.inl (65, 46)),
    Sum.inr (Sum.inl (198, 11)),
    Sum.inr (Sum.inl (93, 14)),
    Sum.inr (Sum.inl (136, 27)),
    Sum.inr (Sum.inl (189, 38)),
    Sum.inr (Sum.inl (198, 33)),
    Sum.inr (Sum.inl (93, 61)),
    Sum.inr (Sum.inl (136, 40)),
    Sum.inr (Sum.inl (189, 40)),
    Sum.inr (Sum.inl (49, 1)),
    Sum.inr (Sum.inl (95, 2)),
    Sum.inr (Sum.inl (229, 48)),
    Sum.inr (Sum.inl (65, 32)),
    Sum.inr (Sum.inl (49, 13)),
    Sum.inr (Sum.inl (95, 14)),
    Sum.inr (Sum.inl (229, 51)),
    Sum.inr (Sum.inl (65, 44)),
    Sum.inr (Sum.inl (198, 35)),
    Sum.inr (Sum.inl (93, 53)),
    Sum.inr (Sum.inl (136, 58)),
    Sum.inr (Sum.inl (189, 42)),
    Sum.inr (Sum.inl (122, 8)),
    Sum.inr (Sum.inl (228, 47)),
    Sum.inr (Sum.inl (122, 44)),
    Sum.inr (Sum.inl (228, 11)),
    Sum.inr (Sum.inl (69, 32)),
    Sum.inr (Sum.inl (180, 47)),
    Sum.inr (Sum.inl (69, 50)),
    Sum.inr (Sum.inl (180, 15)),
    Sum.inr (Sum.inl (69, 44)),
    Sum.inr (Sum.inl (180, 35)),
    Sum.inr (Sum.inl (69, 62)),
    Sum.inr (Sum.inl (180, 3)),
    Sum.inr (Sum.inl (122, 26)),
    Sum.inr (Sum.inl (228, 39)),
    Sum.inr (Sum.inl (122, 62)),
    Sum.inr (Sum.inl (228, 3)),
    Sum.inr (Sum.inl (228, 62)),
    Sum.inr (Sum.inl (122, 63)),
    Sum.inr (Sum.inl (228, 26)),
    Sum.inr (Sum.inl (122, 27)),
    Sum.inr (Sum.inl (180, 62)),
    Sum.inr (Sum.inl (69, 63)),
    Sum.inr (Sum.inl (180, 30)),
    Sum.inr (Sum.inl (69, 45)),
    Sum.inr (Sum.inl (180, 50)),
    Sum.inr (Sum.inl (69, 51)),
    Sum.inr (Sum.inl (180, 18)),
    Sum.inr (Sum.inl (69, 33)),
    Sum.inr (Sum.inl (228, 54)),
    Sum.inr (Sum.inl (122, 45)),
    Sum.inr (Sum.inl (228, 18)),
    Sum.inr (Sum.inl (122, 9)),
    Sum.inr (Sum.inl (50, 48)),
    Sum.inr (Sum.inl (160, 36)),
    Sum.inr (Sum.inl (50, 57)),
    Sum.inr (Sum.inl (160, 19)),
    Sum.inr (Sum.inl (94, 48)),
    Sum.inr (Sum.inl (96, 47)),
    Sum.inr (Sum.inl (94, 52)),
    Sum.inr (Sum.inl (96, 45)),
    Sum.inr (Sum.inl (94, 51)),
    Sum.inr (Sum.inl (96, 35)),
    Sum.inr (Sum.inl (94, 55)),
    Sum.inr (Sum.inl (96, 33)),
    Sum.inr (Sum.inl (50, 50)),
    Sum.inr (Sum.inl (160, 38)),
    Sum.inr (Sum.inl (50, 59)),
    Sum.inr (Sum.inl (160, 17)),
    Sum.inr (Sum.inl (160, 33)),
    Sum.inr (Sum.inl (50, 31)),
    Sum.inr (Sum.inl (160, 22)),
    Sum.inr (Sum.inl (50, 22)),
    Sum.inr (Sum.inl (96, 62)),
    Sum.inr (Sum.inl (94, 31)),
    Sum.inr (Sum.inl (96, 60)),
    Sum.inr (Sum.inl (94, 27)),
    Sum.inr (Sum.inl (96, 50)),
    Sum.inr (Sum.inl (94, 28)),
    Sum.inr (Sum.inl (96, 48)),
    Sum.inr (Sum.inl (94, 24)),
    Sum.inr (Sum.inl (160, 35)),
    Sum.inr (Sum.inl (50, 29)),
    Sum.inr (Sum.inl (160, 20)),
    Sum.inr (Sum.inl (50, 20)),
    Sum.inr (Sum.inr (194, 21)),
    Sum.inr (Sum.inr (9, 21)),
    Sum.inr (Sum.inr (136, 2)),
    Sum.inr (Sum.inr (67, 2)),
    Sum.inr (Sum.inr (284, 21)),
    Sum.inr (Sum.inr (471, 21)),
    Sum.inr (Sum.inr (342, 2)),
    Sum.inr (Sum.inr (413, 2)),
    Sum.inr (Sum.inr (279, 21)),
    Sum.inr (Sum.inr (476, 21)),
    Sum.inr (Sum.inr (349, 2)),
    Sum.inr (Sum.inr (406, 2)),
    Sum.inr (Sum.inr (201, 21)),
    Sum.inr (Sum.inr (2, 21)),
    Sum.inr (Sum.inr (131, 2)),
    Sum.inr (Sum.inr (72, 2)),
    Sum.inr (Sum.inr (136, 9)),
    Sum.inr (Sum.inr (67, 9)),
    Sum.inr (Sum.inr (194, 14)),
    Sum.inr (Sum.inr (9, 14)),
    Sum.inr (Sum.inr (342, 9)),
    Sum.inr (Sum.inr (413, 9)),
    Sum.inr (Sum.inr (284, 14)),
    Sum.inr (Sum.inr (471, 14)),
    Sum.inr (Sum.inr (349, 9)),
    Sum.inr (Sum.inr (406, 9)),
    Sum.inr (Sum.inr (279, 14)),
    Sum.inr (Sum.inr (476, 14)),
    Sum.inr (Sum.inr (131, 9)),
    Sum.inr (Sum.inr (72, 9)),
    Sum.inr (Sum.inr (201, 14)),
    Sum.inr (Sum.inr (2, 14)),
    Sum.inr (Sum.inr (72, 21)),
    Sum.inr (Sum.inr (131, 21)),
    Sum.inr (Sum.inr (2, 2)),
    Sum.inr (Sum.inr (201, 2)),
    Sum.inr (Sum.inr (406, 21)),
    Sum.inr (Sum.inr (349, 21)),
    Sum.inr (Sum.inr (476, 2)),
    Sum.inr (Sum.inr (279, 2)),
    Sum.inr (Sum.inr (413, 21)),
    Sum.inr (Sum.inr (342, 21)),
    Sum.inr (Sum.inr (471, 2)),
    Sum.inr (Sum.inr (284, 2)),
    Sum.inr (Sum.inr (67, 21)),
    Sum.inr (Sum.inr (136, 21)),
    Sum.inr (Sum.inr (9, 2)),
    Sum.inr (Sum.inr (194, 2)),
    Sum.inr (Sum.inr (2, 9)),
    Sum.inr (Sum.inr (201, 9)),
    Sum.inr (Sum.inr (72, 14)),
    Sum.inr (Sum.inr (131, 14)),
    Sum.inr (Sum.inr (476, 9)),
    Sum.inr (Sum.inr (279, 9)),
    Sum.inr (Sum.inr (406, 14)),
    Sum.inr (Sum.inr (349, 14)),
    Sum.inr (Sum.inr (471, 9)),
    Sum.inr (Sum.inr (284, 9)),
    Sum.inr (Sum.inr (413, 14)),
    Sum.inr (Sum.inr (342, 14)),
    Sum.inr (Sum.inr (9, 9)),
    Sum.inr (Sum.inr (194, 9)),
    Sum.inr (Sum.inr (67, 14)),
    Sum.inr (Sum.inr (136, 14)),
    Sum.inr (Sum.inl (219, 59)),
    Sum.inr (Sum.inl (183, 47)),
    Sum.inr (Sum.inl (183, 35)),
    Sum.inr (Sum.inl (219, 51)),
    Sum.inr (Sum.inl (199, 51)),
    Sum.inr (Sum.inl (62, 45)),
    Sum.inr (Sum.inl (62, 33)),
    Sum.inr (Sum.inl (199, 33)),
    Sum.inr (Sum.inl (85, 40)),
    Sum.inr (Sum.inl (59, 61)),
    Sum.inr (Sum.inl (59, 49)),
    Sum.inr (Sum.inl (85, 42)),
    Sum.inr (Sum.inl (135, 26)),
    Sum.inr (Sum.inl (98, 11)),
    Sum.inr (Sum.inl (98, 8)),
    Sum.inr (Sum.inl (135, 24)),
    Sum.inr (Sum.inl (219, 47)),
    Sum.inr (Sum.inl (183, 63)),
    Sum.inr (Sum.inl (183, 51)),
    Sum.inr (Sum.inl (219, 39)),
    Sum.inr (Sum.inl (199, 27)),
    Sum.inr (Sum.inl (62, 15)),
    Sum.inr (Sum.inl (62, 3)),
    Sum.inr (Sum.inl (199, 9)),
    Sum.inr (Sum.inl (85, 31)),
    Sum.inr (Sum.inl (59, 47)),
    Sum.inr (Sum.inl (59, 35)),
    Sum.inr (Sum.inl (85, 29)),
    Sum.inr (Sum.inl (135, 19)),
    Sum.inr (Sum.inl (98, 27)),
    Sum.inr (Sum.inl (98, 24)),
    Sum.inr (Sum.inl (135, 17)),
    Sum.inr (Sum.inl (85, 12)),
    Sum.inr (Sum.inl (59, 34)),
    Sum.inr (Sum.inl (59, 46)),
    Sum.inr (Sum.inl (85, 14)),
    Sum.inr (Sum.inl (135, 42)),
    Sum.inr (Sum.inl (98, 35)),
    Sum.inr (Sum.inl (98, 32)),
    Sum.inr (Sum.inl (135, 40)),
    Sum.inr (Sum.inl (219, 5)),
    Sum.inr (Sum.inl (183, 17)),
    Sum.inr (Sum.inl (183, 29)),
    Sum.inr (Sum.inl (219, 13)),
    Sum.inr (Sum.inl (199, 13)),
    Sum.inr (Sum.inl (62, 19)),
    Sum.inr (Sum.inl (62, 31)),
    Sum.inr (Sum.inl (199, 31)),
    Sum.inr (Sum.inl (85, 59)),
    Sum.inr (Sum.inl (59, 48)),
    Sum.inr (Sum.inl (59, 60)),
    Sum.inr (Sum.inl (85, 57)),
    Sum.inr (Sum.inl (135, 35)),
    Sum.inr (Sum.inl (98, 51)),
    Sum.inr (Sum.inl (98, 48)),
    Sum.inr (Sum.inl (135, 33)),
    Sum.inr (Sum.inl (219, 17)),
    Sum.inr (Sum.inl (183, 1)),
    Sum.inr (Sum.inl (183, 13)),
    Sum.inr (Sum.inl (219, 25)),
    Sum.inr (Sum.inl (199, 37)),
    Sum.inr (Sum.inl (62, 49)),
    Sum.inr (Sum.inl (62, 61)),
    Sum.inr (Sum.inl (199, 55)),
    Sum.inr (Sum.inr (194, 12)),
    Sum.inr (Sum.inr (9, 20)),
    Sum.inr (Sum.inr (194, 10)),
    Sum.inr (Sum.inr (9, 3)),
    Sum.inr (Sum.inr (284, 20)),
    Sum.inr (Sum.inr (471, 12)),
    Sum.inr (Sum.inr (284, 3)),
    Sum.inr (Sum.inr (471, 10)),
    Sum.inr (Sum.inr (279, 20)),
    Sum.inr (Sum.inr (476, 12)),
    Sum.inr (Sum.inr (279, 3)),
    Sum.inr (Sum.inr (476, 10)),
    Sum.inr (Sum.inr (201, 12)),
    Sum.inr (Sum.inr (2, 20)),
    Sum.inr (Sum.inr (201, 10)),
    Sum.inr (Sum.inr (2, 3)),
    Sum.inr (Sum.inr (194, 3)),
    Sum.inr (Sum.inr (9, 10)),
    Sum.inr (Sum.inr (194, 20)),
    Sum.inr (Sum.inr (9, 12)),
    Sum.inr (Sum.inr (284, 10)),
    Sum.inr (Sum.inr (471, 3)),
    Sum.inr (Sum.inr (284, 12)),
    Sum.inr (Sum.inr (471, 20))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock026Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨6656 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block026_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock026Input a
    let y := generatedSixthXiShortBlock026Output a
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
theorem generatedSixth_xi_short_block026_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock026Input a
    let y := generatedSixthXiShortBlock026Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block026_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block026_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock026Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block026_certificate a).1
    (generatedSixth_xi_short_block026_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
