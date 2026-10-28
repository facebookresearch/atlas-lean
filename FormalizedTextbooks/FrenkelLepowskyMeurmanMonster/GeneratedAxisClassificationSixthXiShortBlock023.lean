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
def generatedSixthXiShortBlock023Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (425, 10)),
    Sum.inr (Sum.inr (483, 3)),
    Sum.inr (Sum.inr (425, 20)),
    Sum.inr (Sum.inr (483, 12)),
    Sum.inr (Sum.inr (124, 3)),
    Sum.inr (Sum.inr (54, 10)),
    Sum.inr (Sum.inr (124, 12)),
    Sum.inr (Sum.inr (54, 20)),
    Sum.inr (Sum.inr (253, 12)),
    Sum.inr (Sum.inr (183, 20)),
    Sum.inr (Sum.inr (253, 3)),
    Sum.inr (Sum.inr (183, 10)),
    Sum.inr (Sum.inr (296, 20)),
    Sum.inr (Sum.inr (354, 12)),
    Sum.inr (Sum.inr (296, 10)),
    Sum.inr (Sum.inr (354, 3)),
    Sum.inr (Sum.inr (291, 20)),
    Sum.inr (Sum.inr (361, 12)),
    Sum.inr (Sum.inr (291, 10)),
    Sum.inr (Sum.inr (361, 3)),
    Sum.inr (Sum.inr (246, 12)),
    Sum.inr (Sum.inr (188, 20)),
    Sum.inr (Sum.inr (246, 3)),
    Sum.inr (Sum.inr (188, 10)),
    Sum.inr (Sum.inr (253, 10)),
    Sum.inr (Sum.inr (183, 3)),
    Sum.inr (Sum.inr (253, 20)),
    Sum.inr (Sum.inr (183, 12)),
    Sum.inr (Sum.inr (296, 3)),
    Sum.inr (Sum.inr (354, 10)),
    Sum.inr (Sum.inr (296, 12)),
    Sum.inr (Sum.inr (354, 20)),
    Sum.inr (Sum.inr (291, 3)),
    Sum.inr (Sum.inr (361, 10)),
    Sum.inr (Sum.inr (291, 12)),
    Sum.inr (Sum.inr (361, 20)),
    Sum.inr (Sum.inr (246, 10)),
    Sum.inr (Sum.inr (188, 3)),
    Sum.inr (Sum.inr (246, 20)),
    Sum.inr (Sum.inr (188, 12)),
    Sum.inr (Sum.inl (161, 4)),
    Sum.inr (Sum.inl (121, 60)),
    Sum.inr (Sum.inl (192, 35)),
    Sum.inr (Sum.inl (58, 48)),
    Sum.inr (Sum.inl (63, 35)),
    Sum.inr (Sum.inl (102, 48)),
    Sum.inr (Sum.inl (220, 16)),
    Sum.inr (Sum.inl (84, 15)),
    Sum.inr (Sum.inl (63, 32)),
    Sum.inr (Sum.inl (102, 60)),
    Sum.inr (Sum.inl (220, 28)),
    Sum.inr (Sum.inl (84, 3)),
    Sum.inr (Sum.inl (161, 22)),
    Sum.inr (Sum.inl (121, 62)),
    Sum.inr (Sum.inl (192, 33)),
    Sum.inr (Sum.inl (58, 56)),
    Sum.inr (Sum.inl (161, 58)),
    Sum.inr (Sum.inl (121, 24)),
    Sum.inr (Sum.inl (192, 47)),
    Sum.inr (Sum.inl (58, 14)),
    Sum.inr (Sum.inl (63, 55)),
    Sum.inr (Sum.inl (102, 14)),
    Sum.inr (Sum.inl (220, 46)),
    Sum.inr (Sum.inl (84, 31)),
    Sum.inr (Sum.inl (63, 52)),
    Sum.inr (Sum.inl (102, 2)),
    Sum.inr (Sum.inl (220, 34)),
    Sum.inr (Sum.inl (84, 19)),
    Sum.inr (Sum.inl (161, 40)),
    Sum.inr (Sum.inl (121, 26)),
    Sum.inr (Sum.inl (192, 45)),
    Sum.inr (Sum.inl (58, 6)),
    Sum.inr (Sum.inl (121, 45)),
    Sum.inr (Sum.inl (161, 12)),
    Sum.inr (Sum.inl (58, 34)),
    Sum.inr (Sum.inl (192, 60)),
    Sum.inr (Sum.inl (102, 18)),
    Sum.inr (Sum.inl (63, 60)),
    Sum.inr (Sum.inl (84, 46)),
    Sum.inr (Sum.inl (220, 48)),
    Sum.inr (Sum.inl (102, 30)),
    Sum.inr (Sum.inl (63, 63)),
    Sum.inr (Sum.inl (84, 34)),
    Sum.inr (Sum.inl (220, 60)),
    Sum.inr (Sum.inl (121, 47)),
    Sum.inr (Sum.inl (161, 30)),
    Sum.inr (Sum.inl (58, 42)),
    Sum.inr (Sum.inl (192, 62)),
    Sum.inr (Sum.inl (121, 9)),
    Sum.inr (Sum.inl (161, 50)),
    Sum.inr (Sum.inl (58, 28)),
    Sum.inr (Sum.inl (192, 48)),
    Sum.inr (Sum.inl (102, 44)),
    Sum.inr (Sum.inl (63, 40)),
    Sum.inr (Sum.inl (84, 62)),
    Sum.inr (Sum.inl (220, 14)),
    Sum.inr (Sum.inl (102, 32)),
    Sum.inr (Sum.inl (63, 43)),
    Sum.inr (Sum.inl (84, 50)),
    Sum.inr (Sum.inl (220, 2)),
    Sum.inr (Sum.inl (121, 11)),
    Sum.inr (Sum.inl (161, 32)),
    Sum.inr (Sum.inl (58, 20)),
    Sum.inr (Sum.inl (192, 50)),
    Sum.inr (Sum.inl (62, 37)),
    Sum.inr (Sum.inl (219, 19)),
    Sum.inr (Sum.inl (62, 41)),
    Sum.inr (Sum.inl (219, 27)),
    Sum.inr (Sum.inl (135, 39)),
    Sum.inr (Sum.inl (59, 53)),
    Sum.inr (Sum.inl (135, 37)),
    Sum.inr (Sum.inl (59, 57)),
    Sum.inr (Sum.inl (199, 25)),
    Sum.inr (Sum.inl (183, 23)),
    Sum.inr (Sum.inl (199, 11)),
    Sum.inr (Sum.inl (183, 27)),
    Sum.inr (Sum.inl (98, 38)),
    Sum.inr (Sum.inl (85, 13)),
    Sum.inr (Sum.inl (98, 37)),
    Sum.inr (Sum.inl (85, 15)),
    Sum.inr (Sum.inl (219, 49)),
    Sum.inr (Sum.inl (62, 53)),
    Sum.inr (Sum.inl (219, 57)),
    Sum.inr (Sum.inl (62, 57)),
    Sum.inr (Sum.inl (59, 52)),
    Sum.inr (Sum.inl (135, 28)),
    Sum.inr (Sum.inl (59, 56)),
    Sum.inr (Sum.inl (135, 30)),
    Sum.inr (Sum.inl (183, 53)),
    Sum.inr (Sum.inl (199, 29)),
    Sum.inr (Sum.inl (183, 57)),
    Sum.inr (Sum.inl (199, 15)),
    Sum.inr (Sum.inl (85, 28)),
    Sum.inr (Sum.inl (98, 29)),
    Sum.inr (Sum.inl (85, 30)),
    Sum.inr (Sum.inl (98, 30)),
    Sum.inr (Sum.inl (135, 23)),
    Sum.inr (Sum.inl (59, 42)),
    Sum.inr (Sum.inl (135, 21)),
    Sum.inr (Sum.inl (59, 38)),
    Sum.inr (Sum.inl (62, 27)),
    Sum.inr (Sum.inl (219, 45)),
    Sum.inr (Sum.inl (62, 23)),
    Sum.inr (Sum.inl (219, 37)),
    Sum.inr (Sum.inl (98, 14)),
    Sum.inr (Sum.inl (85, 41)),
    Sum.inr (Sum.inl (98, 13)),
    Sum.inr (Sum.inl (85, 43)),
    Sum.inr (Sum.inl (199, 39)),
    Sum.inr (Sum.inl (183, 41)),
    Sum.inr (Sum.inl (199, 53)),
    Sum.inr (Sum.inl (183, 37)),
    Sum.inr (Sum.inl (59, 43)),
    Sum.inr (Sum.inl (135, 44)),
    Sum.inr (Sum.inl (59, 39)),
    Sum.inr (Sum.inl (135, 46)),
    Sum.inr (Sum.inl (219, 15)),
    Sum.inr (Sum.inl (62, 11)),
    Sum.inr (Sum.inl (219, 7)),
    Sum.inr (Sum.inl (62, 7)),
    Sum.inr (Sum.inl (85, 56)),
    Sum.inr (Sum.inl (98, 53)),
    Sum.inr (Sum.inl (85, 58)),
    Sum.inr (Sum.inl (98, 54)),
    Sum.inr (Sum.inl (183, 11)),
    Sum.inr (Sum.inl (199, 35)),
    Sum.inr (Sum.inl (183, 7)),
    Sum.inr (Sum.inl (199, 49)),
    Sum.inr (Sum.inl (134, 61)),
    Sum.inr (Sum.inl (100, 24)),
    Sum.inr (Sum.inl (162, 47)),
    Sum.inr (Sum.inl (223, 55)),
    Sum.inr (Sum.inl (162, 37)),
    Sum.inr (Sum.inl (223, 19)),
    Sum.inr (Sum.inl (134, 45)),
    Sum.inr (Sum.inl (100, 7)),
    Sum.inr (Sum.inl (100, 18)),
    Sum.inr (Sum.inl (134, 34)),
    Sum.inr (Sum.inl (223, 10)),
    Sum.inr (Sum.inl (162, 48)),
    Sum.inr (Sum.inl (223, 46)),
    Sum.inr (Sum.inl (162, 58)),
    Sum.inr (Sum.inl (100, 13)),
    Sum.inr (Sum.inl (134, 50)),
    Sum.inr (Sum.inl (134, 55)),
    Sum.inr (Sum.inl (100, 8)),
    Sum.inr (Sum.inl (162, 63)),
    Sum.inr (Sum.inl (223, 63)),
    Sum.inr (Sum.inl (162, 53)),
    Sum.inr (Sum.inl (223, 27)),
    Sum.inr (Sum.inl (134, 39)),
    Sum.inr (Sum.inl (100, 23)),
    Sum.inr (Sum.inl (100, 2)),
    Sum.inr (Sum.inl (134, 40)),
    Sum.inr (Sum.inl (223, 2)),
    Sum.inr (Sum.inl (162, 32)),
    Sum.inr (Sum.inl (223, 38)),
    Sum.inr (Sum.inl (162, 42)),
    Sum.inr (Sum.inl (100, 29)),
    Sum.inr (Sum.inl (134, 56)),
    Sum.inr (Sum.inl (191, 60)),
    Sum.inr (Sum.inl (44, 37)),
    Sum.inr (Sum.inl (77, 45)),
    Sum.inr (Sum.inl (86, 7)),
    Sum.inr (Sum.inl (77, 40)),
    Sum.inr (Sum.inl (86, 1)),
    Sum.inr (Sum.inl (191, 24)),
    Sum.inr (Sum.inl (44, 5)),
    Sum.inr (Sum.inl (44, 44)),
    Sum.inr (Sum.inl (191, 52)),
    Sum.inr (Sum.inl (86, 14)),
    Sum.inr (Sum.inl (77, 13)),
    Sum.inr (Sum.inl (86, 8)),
    Sum.inr (Sum.inl (77, 8)),
    Sum.inr (Sum.inl (44, 12)),
    Sum.inr (Sum.inl (191, 16)),
    Sum.inr (Sum.inl (191, 45)),
    Sum.inr (Sum.inl (44, 35)),
    Sum.inr (Sum.inl (77, 39)),
    Sum.inr (Sum.inl (86, 23)),
    Sum.inr (Sum.inl (77, 34)),
    Sum.inr (Sum.inl (86, 17)),
    Sum.inr (Sum.inl (191, 9)),
    Sum.inr (Sum.inl (44, 3)),
    Sum.inr (Sum.inl (44, 42)),
    Sum.inr (Sum.inl (191, 37)),
    Sum.inr (Sum.inl (86, 30)),
    Sum.inr (Sum.inl (77, 7)),
    Sum.inr (Sum.inl (86, 24)),
    Sum.inr (Sum.inl (77, 2)),
    Sum.inr (Sum.inl (44, 10)),
    Sum.inr (Sum.inl (191, 1)),
    Sum.inr (Sum.inr (119, 11)),
    Sum.inr (Sum.inr (253, 1)),
    Sum.inr (Sum.inr (61, 11)),
    Sum.inr (Sum.inr (183, 1)),
    Sum.inr (Sum.inr (418, 11)),
    Sum.inr (Sum.inr (296, 1)),
    Sum.inr (Sum.inr (488, 11)),
    Sum.inr (Sum.inr (354, 1)),
    Sum.inr (Sum.inr (425, 11)),
    Sum.inr (Sum.inr (291, 1)),
    Sum.inr (Sum.inr (483, 11)),
    Sum.inr (Sum.inr (361, 1)),
    Sum.inr (Sum.inr (124, 11)),
    Sum.inr (Sum.inr (246, 1)),
    Sum.inr (Sum.inr (54, 11)),
    Sum.inr (Sum.inr (188, 1)),
    Sum.inr (Sum.inr (188, 11)),
    Sum.inr (Sum.inr (54, 1)),
    Sum.inr (Sum.inr (246, 11)),
    Sum.inr (Sum.inr (124, 1)),
    Sum.inr (Sum.inr (361, 11)),
    Sum.inr (Sum.inr (483, 1)),
    Sum.inr (Sum.inr (291, 11)),
    Sum.inr (Sum.inr (425, 1))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock023Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨5888 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block023_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock023Input a
    let y := generatedSixthXiShortBlock023Output a
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
theorem generatedSixth_xi_short_block023_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock023Input a
    let y := generatedSixthXiShortBlock023Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block023_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block023_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock023Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block023_certificate a).1
    (generatedSixth_xi_short_block023_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
