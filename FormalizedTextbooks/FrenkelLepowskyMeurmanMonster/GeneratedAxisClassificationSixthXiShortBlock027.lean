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
def generatedSixthXiShortBlock027Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (279, 10)),
    Sum.inr (Sum.inr (476, 3)),
    Sum.inr (Sum.inr (279, 12)),
    Sum.inr (Sum.inr (476, 20)),
    Sum.inr (Sum.inr (201, 3)),
    Sum.inr (Sum.inr (2, 10)),
    Sum.inr (Sum.inr (201, 20)),
    Sum.inr (Sum.inr (2, 12)),
    Sum.inr (Sum.inr (72, 20)),
    Sum.inr (Sum.inr (131, 12)),
    Sum.inr (Sum.inr (72, 3)),
    Sum.inr (Sum.inr (131, 10)),
    Sum.inr (Sum.inr (406, 12)),
    Sum.inr (Sum.inr (349, 20)),
    Sum.inr (Sum.inr (406, 10)),
    Sum.inr (Sum.inr (349, 3)),
    Sum.inr (Sum.inr (413, 12)),
    Sum.inr (Sum.inr (342, 20)),
    Sum.inr (Sum.inr (413, 10)),
    Sum.inr (Sum.inr (342, 3)),
    Sum.inr (Sum.inr (67, 20)),
    Sum.inr (Sum.inr (136, 12)),
    Sum.inr (Sum.inr (67, 3)),
    Sum.inr (Sum.inr (136, 10)),
    Sum.inr (Sum.inr (72, 10)),
    Sum.inr (Sum.inr (131, 3)),
    Sum.inr (Sum.inr (72, 12)),
    Sum.inr (Sum.inr (131, 20)),
    Sum.inr (Sum.inr (406, 3)),
    Sum.inr (Sum.inr (349, 10)),
    Sum.inr (Sum.inr (406, 20)),
    Sum.inr (Sum.inr (349, 12)),
    Sum.inr (Sum.inr (413, 3)),
    Sum.inr (Sum.inr (342, 10)),
    Sum.inr (Sum.inr (413, 20)),
    Sum.inr (Sum.inr (342, 12)),
    Sum.inr (Sum.inr (67, 10)),
    Sum.inr (Sum.inr (136, 3)),
    Sum.inr (Sum.inr (67, 12)),
    Sum.inr (Sum.inr (136, 20)),
    Sum.inr (Sum.inl (77, 22)),
    Sum.inr (Sum.inl (162, 35)),
    Sum.inr (Sum.inl (86, 60)),
    Sum.inr (Sum.inl (223, 7)),
    Sum.inr (Sum.inl (162, 38)),
    Sum.inr (Sum.inl (77, 57)),
    Sum.inr (Sum.inl (223, 22)),
    Sum.inr (Sum.inl (86, 35)),
    Sum.inr (Sum.inl (86, 53)),
    Sum.inr (Sum.inl (223, 58)),
    Sum.inr (Sum.inl (77, 54)),
    Sum.inr (Sum.inl (162, 60)),
    Sum.inr (Sum.inl (223, 43)),
    Sum.inr (Sum.inl (86, 42)),
    Sum.inr (Sum.inl (162, 57)),
    Sum.inr (Sum.inl (77, 25)),
    Sum.inr (Sum.inl (77, 28)),
    Sum.inr (Sum.inl (162, 51)),
    Sum.inr (Sum.inl (86, 44)),
    Sum.inr (Sum.inl (223, 15)),
    Sum.inr (Sum.inl (162, 54)),
    Sum.inr (Sum.inl (77, 51)),
    Sum.inr (Sum.inl (223, 30)),
    Sum.inr (Sum.inl (86, 51)),
    Sum.inr (Sum.inl (86, 37)),
    Sum.inr (Sum.inl (223, 50)),
    Sum.inr (Sum.inl (77, 60)),
    Sum.inr (Sum.inl (162, 44)),
    Sum.inr (Sum.inl (223, 35)),
    Sum.inr (Sum.inl (86, 58)),
    Sum.inr (Sum.inl (162, 41)),
    Sum.inr (Sum.inl (77, 19)),
    Sum.inr (Sum.inl (191, 35)),
    Sum.inr (Sum.inl (134, 57)),
    Sum.inr (Sum.inl (44, 26)),
    Sum.inr (Sum.inl (100, 35)),
    Sum.inr (Sum.inl (134, 60)),
    Sum.inr (Sum.inl (191, 30)),
    Sum.inr (Sum.inl (100, 38)),
    Sum.inr (Sum.inl (44, 53)),
    Sum.inr (Sum.inl (44, 19)),
    Sum.inr (Sum.inl (100, 41)),
    Sum.inr (Sum.inl (191, 43)),
    Sum.inr (Sum.inl (134, 38)),
    Sum.inr (Sum.inl (100, 44)),
    Sum.inr (Sum.inl (44, 60)),
    Sum.inr (Sum.inl (134, 35)),
    Sum.inr (Sum.inl (191, 22)),
    Sum.inr (Sum.inl (191, 50)),
    Sum.inr (Sum.inl (134, 51)),
    Sum.inr (Sum.inl (44, 28)),
    Sum.inr (Sum.inl (100, 51)),
    Sum.inr (Sum.inl (134, 54)),
    Sum.inr (Sum.inl (191, 15)),
    Sum.inr (Sum.inl (100, 54)),
    Sum.inr (Sum.inl (44, 51)),
    Sum.inr (Sum.inl (44, 21)),
    Sum.inr (Sum.inl (100, 57)),
    Sum.inr (Sum.inl (191, 58)),
    Sum.inr (Sum.inl (134, 44)),
    Sum.inr (Sum.inl (100, 60)),
    Sum.inr (Sum.inl (44, 58)),
    Sum.inr (Sum.inl (134, 41)),
    Sum.inr (Sum.inl (191, 7)),
    Sum.inr (Sum.inl (200, 32)),
    Sum.inr (Sum.inl (76, 47)),
    Sum.inr (Sum.inl (200, 44)),
    Sum.inr (Sum.inl (76, 39)),
    Sum.inr (Sum.inl (224, 40)),
    Sum.inr (Sum.inl (82, 47)),
    Sum.inr (Sum.inl (224, 42)),
    Sum.inr (Sum.inl (82, 35)),
    Sum.inr (Sum.inl (76, 14)),
    Sum.inr (Sum.inl (200, 15)),
    Sum.inr (Sum.inl (76, 6)),
    Sum.inr (Sum.inl (200, 3)),
    Sum.inr (Sum.inl (82, 46)),
    Sum.inr (Sum.inl (224, 19)),
    Sum.inr (Sum.inl (82, 34)),
    Sum.inr (Sum.inl (224, 17)),
    Sum.inr (Sum.inl (182, 32)),
    Sum.inr (Sum.inl (120, 63)),
    Sum.inr (Sum.inl (182, 50)),
    Sum.inr (Sum.inl (120, 51)),
    Sum.inr (Sum.inl (45, 32)),
    Sum.inr (Sum.inl (101, 31)),
    Sum.inr (Sum.inl (45, 35)),
    Sum.inr (Sum.inl (101, 29)),
    Sum.inr (Sum.inl (120, 46)),
    Sum.inr (Sum.inl (182, 27)),
    Sum.inr (Sum.inl (120, 34)),
    Sum.inr (Sum.inl (182, 9)),
    Sum.inr (Sum.inl (101, 22)),
    Sum.inr (Sum.inl (45, 27)),
    Sum.inr (Sum.inl (101, 20)),
    Sum.inr (Sum.inl (45, 24)),
    Sum.inr (Sum.inl (224, 24)),
    Sum.inr (Sum.inl (82, 48)),
    Sum.inr (Sum.inl (224, 26)),
    Sum.inr (Sum.inl (82, 60)),
    Sum.inr (Sum.inl (200, 33)),
    Sum.inr (Sum.inl (76, 18)),
    Sum.inr (Sum.inl (200, 45)),
    Sum.inr (Sum.inl (76, 26)),
    Sum.inr (Sum.inl (82, 49)),
    Sum.inr (Sum.inl (224, 35)),
    Sum.inr (Sum.inl (82, 61)),
    Sum.inr (Sum.inl (224, 33)),
    Sum.inr (Sum.inl (76, 51)),
    Sum.inr (Sum.inl (200, 14)),
    Sum.inr (Sum.inl (76, 59)),
    Sum.inr (Sum.inl (200, 2)),
    Sum.inr (Sum.inl (45, 8)),
    Sum.inr (Sum.inl (101, 59)),
    Sum.inr (Sum.inl (45, 11)),
    Sum.inr (Sum.inl (101, 57)),
    Sum.inr (Sum.inl (182, 33)),
    Sum.inr (Sum.inl (120, 2)),
    Sum.inr (Sum.inl (182, 51)),
    Sum.inr (Sum.inl (120, 14)),
    Sum.inr (Sum.inl (101, 50)),
    Sum.inr (Sum.inl (45, 51)),
    Sum.inr (Sum.inl (101, 48)),
    Sum.inr (Sum.inl (45, 48)),
    Sum.inr (Sum.inl (120, 19)),
    Sum.inr (Sum.inl (182, 26)),
    Sum.inr (Sum.inl (120, 31)),
    Sum.inr (Sum.inl (182, 8)),
    Sum.inr (Sum.inl (192, 55)),
    Sum.inr (Sum.inl (161, 63)),
    Sum.inr (Sum.inl (121, 48)),
    Sum.inr (Sum.inl (58, 47)),
    Sum.inr (Sum.inl (63, 47)),
    Sum.inr (Sum.inl (220, 63)),
    Sum.inr (Sum.inl (84, 32)),
    Sum.inr (Sum.inl (102, 31)),
    Sum.inr (Sum.inl (63, 44)),
    Sum.inr (Sum.inl (220, 51)),
    Sum.inr (Sum.inl (84, 44)),
    Sum.inr (Sum.inl (102, 19)),
    Sum.inr (Sum.inl (192, 53)),
    Sum.inr (Sum.inl (161, 45)),
    Sum.inr (Sum.inl (121, 50)),
    Sum.inr (Sum.inl (58, 39)),
    Sum.inr (Sum.inl (192, 38)),
    Sum.inr (Sum.inl (161, 27)),
    Sum.inr (Sum.inl (121, 7)),
    Sum.inr (Sum.inl (58, 11)),
    Sum.inr (Sum.inl (63, 39)),
    Sum.inr (Sum.inl (220, 45)),
    Sum.inr (Sum.inl (84, 29)),
    Sum.inr (Sum.inl (102, 15)),
    Sum.inr (Sum.inl (63, 36)),
    Sum.inr (Sum.inl (220, 33)),
    Sum.inr (Sum.inl (84, 17)),
    Sum.inr (Sum.inl (102, 3)),
    Sum.inr (Sum.inl (192, 36)),
    Sum.inr (Sum.inl (161, 9)),
    Sum.inr (Sum.inl (121, 5)),
    Sum.inr (Sum.inl (58, 3)),
    Sum.inr (Sum.inl (121, 33)),
    Sum.inr (Sum.inl (58, 61)),
    Sum.inr (Sum.inl (192, 40)),
    Sum.inr (Sum.inl (161, 55)),
    Sum.inr (Sum.inl (84, 1)),
    Sum.inr (Sum.inl (102, 61)),
    Sum.inr (Sum.inl (63, 48)),
    Sum.inr (Sum.inl (220, 31)),
    Sum.inr (Sum.inl (84, 13)),
    Sum.inr (Sum.inl (102, 49)),
    Sum.inr (Sum.inl (63, 51)),
    Sum.inr (Sum.inl (220, 19)),
    Sum.inr (Sum.inl (121, 35)),
    Sum.inr (Sum.inl (58, 53)),
    Sum.inr (Sum.inl (192, 42)),
    Sum.inr (Sum.inl (161, 37)),
    Sum.inr (Sum.inl (121, 22)),
    Sum.inr (Sum.inl (58, 25)),
    Sum.inr (Sum.inl (192, 57)),
    Sum.inr (Sum.inl (161, 19)),
    Sum.inr (Sum.inl (84, 60)),
    Sum.inr (Sum.inl (102, 45)),
    Sum.inr (Sum.inl (63, 56)),
    Sum.inr (Sum.inl (220, 13)),
    Sum.inr (Sum.inl (84, 48)),
    Sum.inr (Sum.inl (102, 33)),
    Sum.inr (Sum.inl (63, 59)),
    Sum.inr (Sum.inl (220, 1)),
    Sum.inr (Sum.inl (121, 20)),
    Sum.inr (Sum.inl (58, 17)),
    Sum.inr (Sum.inl (192, 59)),
    Sum.inr (Sum.inl (161, 1)),
    Sum.inr (Sum.inr (194, 11)),
    Sum.inr (Sum.inr (67, 11)),
    Sum.inr (Sum.inr (2, 1)),
    Sum.inr (Sum.inr (131, 1)),
    Sum.inr (Sum.inr (342, 11)),
    Sum.inr (Sum.inr (471, 11)),
    Sum.inr (Sum.inr (406, 1)),
    Sum.inr (Sum.inr (279, 1)),
    Sum.inr (Sum.inr (349, 11)),
    Sum.inr (Sum.inr (476, 11)),
    Sum.inr (Sum.inr (413, 1)),
    Sum.inr (Sum.inr (284, 1)),
    Sum.inr (Sum.inr (201, 11)),
    Sum.inr (Sum.inr (72, 11)),
    Sum.inr (Sum.inr (9, 1)),
    Sum.inr (Sum.inr (136, 1)),
    Sum.inr (Sum.inr (136, 11)),
    Sum.inr (Sum.inr (9, 11)),
    Sum.inr (Sum.inr (72, 1)),
    Sum.inr (Sum.inr (201, 1)),
    Sum.inr (Sum.inr (284, 11)),
    Sum.inr (Sum.inr (413, 11)),
    Sum.inr (Sum.inr (476, 1)),
    Sum.inr (Sum.inr (349, 1))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock027Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨6912 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block027_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock027Input a
    let y := generatedSixthXiShortBlock027Output a
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
theorem generatedSixth_xi_short_block027_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock027Input a
    let y := generatedSixthXiShortBlock027Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block027_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block027_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock027Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block027_certificate a).1
    (generatedSixth_xi_short_block027_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
