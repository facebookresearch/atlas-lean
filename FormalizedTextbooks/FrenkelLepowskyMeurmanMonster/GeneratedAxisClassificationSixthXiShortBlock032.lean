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
def generatedSixthXiShortBlock032Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (398, 8)),
    Sum.inr (Sum.inr (271, 23)),
    Sum.inr (Sum.inr (334, 8)),
    Sum.inr (Sum.inr (463, 23)),
    Sum.inr (Sum.inr (26, 8)),
    Sum.inr (Sum.inr (155, 23)),
    Sum.inr (Sum.inr (218, 8)),
    Sum.inr (Sum.inr (91, 23)),
    Sum.inr (Sum.inr (218, 13)),
    Sum.inr (Sum.inr (91, 0)),
    Sum.inr (Sum.inr (26, 13)),
    Sum.inr (Sum.inr (155, 0)),
    Sum.inr (Sum.inr (334, 13)),
    Sum.inr (Sum.inr (463, 0)),
    Sum.inr (Sum.inr (398, 13)),
    Sum.inr (Sum.inr (271, 0)),
    Sum.inr (Sum.inr (325, 13)),
    Sum.inr (Sum.inr (452, 0)),
    Sum.inr (Sum.inr (389, 13)),
    Sum.inr (Sum.inr (260, 0)),
    Sum.inr (Sum.inr (209, 13)),
    Sum.inr (Sum.inr (80, 0)),
    Sum.inr (Sum.inr (17, 13)),
    Sum.inr (Sum.inr (144, 0)),
    Sum.inr (Sum.inr (91, 8)),
    Sum.inr (Sum.inr (218, 23)),
    Sum.inr (Sum.inr (155, 8)),
    Sum.inr (Sum.inr (26, 23)),
    Sum.inr (Sum.inr (463, 8)),
    Sum.inr (Sum.inr (334, 23)),
    Sum.inr (Sum.inr (271, 8)),
    Sum.inr (Sum.inr (398, 23)),
    Sum.inr (Sum.inr (452, 8)),
    Sum.inr (Sum.inr (325, 23)),
    Sum.inr (Sum.inr (260, 8)),
    Sum.inr (Sum.inr (389, 23)),
    Sum.inr (Sum.inr (80, 8)),
    Sum.inr (Sum.inr (209, 23)),
    Sum.inr (Sum.inr (144, 8)),
    Sum.inr (Sum.inr (17, 23)),
    Sum.inr (Sum.inl (224, 10)),
    Sum.inr (Sum.inl (101, 18)),
    Sum.inr (Sum.inl (182, 10)),
    Sum.inr (Sum.inl (76, 24)),
    Sum.inr (Sum.inl (45, 18)),
    Sum.inr (Sum.inl (82, 24)),
    Sum.inr (Sum.inl (200, 40)),
    Sum.inr (Sum.inl (120, 40)),
    Sum.inr (Sum.inl (45, 17)),
    Sum.inr (Sum.inl (82, 20)),
    Sum.inr (Sum.inl (200, 36)),
    Sum.inr (Sum.inl (120, 36)),
    Sum.inr (Sum.inl (224, 8)),
    Sum.inr (Sum.inl (101, 16)),
    Sum.inr (Sum.inl (182, 24)),
    Sum.inr (Sum.inl (76, 16)),
    Sum.inr (Sum.inl (101, 27)),
    Sum.inr (Sum.inl (224, 49)),
    Sum.inr (Sum.inl (76, 57)),
    Sum.inr (Sum.inl (182, 49)),
    Sum.inr (Sum.inl (82, 25)),
    Sum.inr (Sum.inl (45, 41)),
    Sum.inr (Sum.inl (120, 57)),
    Sum.inr (Sum.inl (200, 7)),
    Sum.inr (Sum.inl (82, 21)),
    Sum.inr (Sum.inl (45, 42)),
    Sum.inr (Sum.inl (120, 53)),
    Sum.inr (Sum.inl (200, 11)),
    Sum.inr (Sum.inl (101, 25)),
    Sum.inr (Sum.inl (224, 51)),
    Sum.inr (Sum.inl (76, 49)),
    Sum.inr (Sum.inl (182, 35)),
    Sum.inr (Sum.inl (224, 3)),
    Sum.inr (Sum.inl (101, 61)),
    Sum.inr (Sum.inl (182, 34)),
    Sum.inr (Sum.inl (76, 12)),
    Sum.inr (Sum.inl (45, 2)),
    Sum.inr (Sum.inl (82, 10)),
    Sum.inr (Sum.inl (200, 10)),
    Sum.inr (Sum.inl (120, 8)),
    Sum.inr (Sum.inl (45, 1)),
    Sum.inr (Sum.inl (82, 6)),
    Sum.inr (Sum.inl (200, 6)),
    Sum.inr (Sum.inl (120, 4)),
    Sum.inr (Sum.inl (224, 1)),
    Sum.inr (Sum.inl (101, 63)),
    Sum.inr (Sum.inl (182, 48)),
    Sum.inr (Sum.inl (76, 4)),
    Sum.inr (Sum.inl (101, 52)),
    Sum.inr (Sum.inl (224, 56)),
    Sum.inr (Sum.inl (76, 45)),
    Sum.inr (Sum.inl (182, 25)),
    Sum.inr (Sum.inl (82, 11)),
    Sum.inr (Sum.inl (45, 57)),
    Sum.inr (Sum.inl (120, 25)),
    Sum.inr (Sum.inl (200, 37)),
    Sum.inr (Sum.inl (82, 7)),
    Sum.inr (Sum.inl (45, 58)),
    Sum.inr (Sum.inl (120, 21)),
    Sum.inr (Sum.inl (200, 41)),
    Sum.inr (Sum.inl (101, 54)),
    Sum.inr (Sum.inl (224, 58)),
    Sum.inr (Sum.inl (76, 37)),
    Sum.inr (Sum.inl (182, 11)),
    Sum.inr (Sum.inl (220, 8)),
    Sum.inr (Sum.inl (58, 24)),
    Sum.inr (Sum.inl (220, 4)),
    Sum.inr (Sum.inl (58, 16)),
    Sum.inr (Sum.inl (192, 61)),
    Sum.inr (Sum.inl (84, 40)),
    Sum.inr (Sum.inl (192, 63)),
    Sum.inr (Sum.inl (84, 36)),
    Sum.inr (Sum.inl (161, 38)),
    Sum.inr (Sum.inl (102, 56)),
    Sum.inr (Sum.inl (161, 52)),
    Sum.inr (Sum.inl (102, 52)),
    Sum.inr (Sum.inl (63, 53)),
    Sum.inr (Sum.inl (121, 37)),
    Sum.inr (Sum.inl (63, 54)),
    Sum.inr (Sum.inl (121, 39)),
    Sum.inr (Sum.inl (58, 10)),
    Sum.inr (Sum.inl (220, 40)),
    Sum.inr (Sum.inl (58, 2)),
    Sum.inr (Sum.inl (220, 36)),
    Sum.inr (Sum.inl (84, 9)),
    Sum.inr (Sum.inl (192, 34)),
    Sum.inr (Sum.inl (84, 5)),
    Sum.inr (Sum.inl (192, 32)),
    Sum.inr (Sum.inl (102, 26)),
    Sum.inr (Sum.inl (161, 46)),
    Sum.inr (Sum.inl (102, 22)),
    Sum.inr (Sum.inl (161, 60)),
    Sum.inr (Sum.inl (121, 52)),
    Sum.inr (Sum.inl (63, 42)),
    Sum.inr (Sum.inl (121, 54)),
    Sum.inr (Sum.inl (63, 41)),
    Sum.inr (Sum.inl (192, 49)),
    Sum.inr (Sum.inl (84, 56)),
    Sum.inr (Sum.inl (192, 51)),
    Sum.inr (Sum.inl (84, 52)),
    Sum.inr (Sum.inl (220, 54)),
    Sum.inr (Sum.inl (58, 38)),
    Sum.inr (Sum.inl (220, 58)),
    Sum.inr (Sum.inl (58, 46)),
    Sum.inr (Sum.inl (63, 33)),
    Sum.inr (Sum.inl (121, 1)),
    Sum.inr (Sum.inl (63, 34)),
    Sum.inr (Sum.inl (121, 3)),
    Sum.inr (Sum.inl (161, 24)),
    Sum.inr (Sum.inl (102, 6)),
    Sum.inr (Sum.inl (161, 10)),
    Sum.inr (Sum.inl (102, 10)),
    Sum.inr (Sum.inl (84, 25)),
    Sum.inr (Sum.inl (192, 46)),
    Sum.inr (Sum.inl (84, 21)),
    Sum.inr (Sum.inl (192, 44)),
    Sum.inr (Sum.inl (58, 52)),
    Sum.inr (Sum.inl (220, 22)),
    Sum.inr (Sum.inl (58, 60)),
    Sum.inr (Sum.inl (220, 26)),
    Sum.inr (Sum.inl (121, 16)),
    Sum.inr (Sum.inl (63, 62)),
    Sum.inr (Sum.inl (121, 18)),
    Sum.inr (Sum.inl (63, 61)),
    Sum.inr (Sum.inl (102, 36)),
    Sum.inr (Sum.inl (161, 16)),
    Sum.inr (Sum.inl (102, 40)),
    Sum.inr (Sum.inl (161, 2)),
    Sum.inr (Sum.inl (96, 10)),
    Sum.inr (Sum.inl (96, 21)),
    Sum.inr (Sum.inl (228, 57)),
    Sum.inr (Sum.inl (228, 4)),
    Sum.inr (Sum.inl (180, 53)),
    Sum.inr (Sum.inl (180, 8)),
    Sum.inr (Sum.inl (160, 63)),
    Sum.inr (Sum.inl (160, 15)),
    Sum.inr (Sum.inl (69, 20)),
    Sum.inr (Sum.inl (69, 21)),
    Sum.inr (Sum.inl (50, 46)),
    Sum.inr (Sum.inl (50, 10)),
    Sum.inr (Sum.inl (94, 45)),
    Sum.inr (Sum.inl (94, 5)),
    Sum.inr (Sum.inl (122, 6)),
    Sum.inr (Sum.inl (122, 7)),
    Sum.inr (Sum.inl (228, 49)),
    Sum.inr (Sum.inl (228, 12)),
    Sum.inr (Sum.inl (96, 6)),
    Sum.inr (Sum.inl (96, 25)),
    Sum.inr (Sum.inl (160, 61)),
    Sum.inr (Sum.inl (160, 13)),
    Sum.inr (Sum.inl (180, 57)),
    Sum.inr (Sum.inl (180, 4)),
    Sum.inr (Sum.inl (50, 44)),
    Sum.inr (Sum.inl (50, 8)),
    Sum.inr (Sum.inl (69, 24)),
    Sum.inr (Sum.inl (69, 25)),
    Sum.inr (Sum.inl (122, 20)),
    Sum.inr (Sum.inl (122, 21)),
    Sum.inr (Sum.inl (94, 46)),
    Sum.inr (Sum.inl (94, 6)),
    Sum.inr (Sum.inl (180, 21)),
    Sum.inr (Sum.inl (180, 40)),
    Sum.inr (Sum.inl (160, 8)),
    Sum.inr (Sum.inl (160, 56)),
    Sum.inr (Sum.inl (96, 8)),
    Sum.inr (Sum.inl (96, 23)),
    Sum.inr (Sum.inl (228, 29)),
    Sum.inr (Sum.inl (228, 32)),
    Sum.inr (Sum.inl (94, 41)),
    Sum.inr (Sum.inl (94, 1)),
    Sum.inr (Sum.inl (122, 34)),
    Sum.inr (Sum.inl (122, 35)),
    Sum.inr (Sum.inl (69, 6)),
    Sum.inr (Sum.inl (69, 7)),
    Sum.inr (Sum.inl (50, 39)),
    Sum.inr (Sum.inl (50, 3)),
    Sum.inr (Sum.inl (160, 10)),
    Sum.inr (Sum.inl (160, 58)),
    Sum.inr (Sum.inl (180, 25)),
    Sum.inr (Sum.inl (180, 36)),
    Sum.inr (Sum.inl (228, 21)),
    Sum.inr (Sum.inl (228, 40)),
    Sum.inr (Sum.inl (96, 4)),
    Sum.inr (Sum.inl (96, 27)),
    Sum.inr (Sum.inl (122, 48)),
    Sum.inr (Sum.inl (122, 49)),
    Sum.inr (Sum.inl (94, 42)),
    Sum.inr (Sum.inl (94, 2)),
    Sum.inr (Sum.inl (50, 37)),
    Sum.inr (Sum.inl (50, 1)),
    Sum.inr (Sum.inl (69, 10)),
    Sum.inr (Sum.inl (69, 11)),
    Sum.inr (Sum.inl (47, 6)),
    Sum.inr (Sum.inl (226, 12)),
    Sum.inr (Sum.inl (47, 18)),
    Sum.inr (Sum.inl (226, 40)),
    Sum.inr (Sum.inl (80, 3)),
    Sum.inr (Sum.inl (67, 10)),
    Sum.inr (Sum.inl (80, 61)),
    Sum.inr (Sum.inl (67, 34)),
    Sum.inr (Sum.inl (110, 18)),
    Sum.inr (Sum.inl (197, 20)),
    Sum.inr (Sum.inl (110, 16)),
    Sum.inr (Sum.inl (197, 48)),
    Sum.inr (Sum.inl (190, 18)),
    Sum.inr (Sum.inl (123, 18)),
    Sum.inr (Sum.inl (190, 16)),
    Sum.inr (Sum.inl (123, 16)),
    Sum.inr (Sum.inl (110, 6)),
    Sum.inr (Sum.inl (197, 12)),
    Sum.inr (Sum.inl (110, 4)),
    Sum.inr (Sum.inl (197, 40)),
    Sum.inr (Sum.inl (190, 6)),
    Sum.inr (Sum.inl (123, 10)),
    Sum.inr (Sum.inl (190, 4)),
    Sum.inr (Sum.inl (123, 8))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock032Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨8192 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block032_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock032Input a
    let y := generatedSixthXiShortBlock032Output a
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
theorem generatedSixth_xi_short_block032_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock032Input a
    let y := generatedSixthXiShortBlock032Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block032_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block032_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock032Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block032_certificate a).1
    (generatedSixth_xi_short_block032_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
