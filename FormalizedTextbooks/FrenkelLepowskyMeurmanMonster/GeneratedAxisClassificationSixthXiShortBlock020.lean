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
def generatedSixthXiShortBlock020Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (286, 8)),
    Sum.inr (Sum.inr (351, 23)),
    Sum.inr (Sum.inr (404, 8)),
    Sum.inr (Sum.inr (469, 23)),
    Sum.inr (Sum.inr (74, 8)),
    Sum.inr (Sum.inr (11, 23)),
    Sum.inr (Sum.inr (192, 8)),
    Sum.inr (Sum.inr (129, 23)),
    Sum.inr (Sum.inr (192, 13)),
    Sum.inr (Sum.inr (129, 0)),
    Sum.inr (Sum.inr (74, 13)),
    Sum.inr (Sum.inr (11, 0)),
    Sum.inr (Sum.inr (404, 13)),
    Sum.inr (Sum.inr (469, 0)),
    Sum.inr (Sum.inr (286, 13)),
    Sum.inr (Sum.inr (351, 0)),
    Sum.inr (Sum.inr (415, 13)),
    Sum.inr (Sum.inr (478, 0)),
    Sum.inr (Sum.inr (277, 13)),
    Sum.inr (Sum.inr (340, 0)),
    Sum.inr (Sum.inr (203, 13)),
    Sum.inr (Sum.inr (138, 0)),
    Sum.inr (Sum.inr (65, 13)),
    Sum.inr (Sum.inr (0, 0)),
    Sum.inr (Sum.inr (129, 8)),
    Sum.inr (Sum.inr (192, 23)),
    Sum.inr (Sum.inr (11, 8)),
    Sum.inr (Sum.inr (74, 23)),
    Sum.inr (Sum.inr (469, 8)),
    Sum.inr (Sum.inr (404, 23)),
    Sum.inr (Sum.inr (351, 8)),
    Sum.inr (Sum.inr (286, 23)),
    Sum.inr (Sum.inr (478, 8)),
    Sum.inr (Sum.inr (415, 23)),
    Sum.inr (Sum.inr (340, 8)),
    Sum.inr (Sum.inr (277, 23)),
    Sum.inr (Sum.inr (138, 8)),
    Sum.inr (Sum.inr (203, 23)),
    Sum.inr (Sum.inr (0, 8)),
    Sum.inr (Sum.inr (65, 23)),
    Sum.inr (Sum.inl (225, 0)),
    Sum.inr (Sum.inl (225, 59)),
    Sum.inr (Sum.inl (124, 53)),
    Sum.inr (Sum.inl (124, 20)),
    Sum.inr (Sum.inl (78, 33)),
    Sum.inr (Sum.inl (78, 0)),
    Sum.inr (Sum.inl (139, 34)),
    Sum.inr (Sum.inl (139, 13)),
    Sum.inr (Sum.inl (78, 45)),
    Sum.inr (Sum.inl (78, 12)),
    Sum.inr (Sum.inl (139, 46)),
    Sum.inr (Sum.inl (139, 1)),
    Sum.inr (Sum.inl (225, 18)),
    Sum.inr (Sum.inl (225, 41)),
    Sum.inr (Sum.inl (124, 61)),
    Sum.inr (Sum.inl (124, 28)),
    Sum.inr (Sum.inl (155, 53)),
    Sum.inr (Sum.inl (155, 36)),
    Sum.inr (Sum.inl (55, 57)),
    Sum.inr (Sum.inl (55, 2)),
    Sum.inr (Sum.inl (177, 40)),
    Sum.inr (Sum.inl (177, 19)),
    Sum.inr (Sum.inl (72, 12)),
    Sum.inr (Sum.inl (72, 13)),
    Sum.inr (Sum.inl (177, 43)),
    Sum.inr (Sum.inl (177, 16)),
    Sum.inr (Sum.inl (72, 0)),
    Sum.inr (Sum.inl (72, 1)),
    Sum.inr (Sum.inl (155, 55)),
    Sum.inr (Sum.inl (155, 38)),
    Sum.inr (Sum.inl (55, 59)),
    Sum.inr (Sum.inl (55, 0)),
    Sum.inr (Sum.inl (124, 33)),
    Sum.inr (Sum.inl (124, 0)),
    Sum.inr (Sum.inl (225, 40)),
    Sum.inr (Sum.inl (225, 19)),
    Sum.inr (Sum.inl (139, 0)),
    Sum.inr (Sum.inl (139, 47)),
    Sum.inr (Sum.inl (78, 49)),
    Sum.inr (Sum.inl (78, 16)),
    Sum.inr (Sum.inl (139, 12)),
    Sum.inr (Sum.inl (139, 35)),
    Sum.inr (Sum.inl (78, 61)),
    Sum.inr (Sum.inl (78, 28)),
    Sum.inr (Sum.inl (124, 41)),
    Sum.inr (Sum.inl (124, 8)),
    Sum.inr (Sum.inl (225, 58)),
    Sum.inr (Sum.inl (225, 1)),
    Sum.inr (Sum.inl (55, 40)),
    Sum.inr (Sum.inl (55, 19)),
    Sum.inr (Sum.inl (155, 2)),
    Sum.inr (Sum.inl (155, 19)),
    Sum.inr (Sum.inl (72, 46)),
    Sum.inr (Sum.inl (72, 47)),
    Sum.inr (Sum.inl (177, 56)),
    Sum.inr (Sum.inl (177, 3)),
    Sum.inr (Sum.inl (72, 34)),
    Sum.inr (Sum.inl (72, 35)),
    Sum.inr (Sum.inl (177, 59)),
    Sum.inr (Sum.inl (177, 0)),
    Sum.inr (Sum.inl (55, 42)),
    Sum.inr (Sum.inl (55, 17)),
    Sum.inr (Sum.inl (155, 0)),
    Sum.inr (Sum.inl (155, 17)),
    Sum.inr (Sum.inl (156, 0)),
    Sum.inr (Sum.inl (230, 20)),
    Sum.inr (Sum.inl (156, 12)),
    Sum.inr (Sum.inl (230, 28)),
    Sum.inr (Sum.inl (176, 0)),
    Sum.inr (Sum.inl (111, 34)),
    Sum.inr (Sum.inl (176, 2)),
    Sum.inr (Sum.inl (111, 46)),
    Sum.inr (Sum.inl (230, 0)),
    Sum.inr (Sum.inl (156, 16)),
    Sum.inr (Sum.inl (230, 8)),
    Sum.inr (Sum.inl (156, 28)),
    Sum.inr (Sum.inl (111, 0)),
    Sum.inr (Sum.inl (176, 55)),
    Sum.inr (Sum.inl (111, 12)),
    Sum.inr (Sum.inl (176, 53)),
    Sum.inr (Sum.inl (107, 0)),
    Sum.inr (Sum.inl (54, 18)),
    Sum.inr (Sum.inl (107, 18)),
    Sum.inr (Sum.inl (54, 30)),
    Sum.inr (Sum.inl (92, 0)),
    Sum.inr (Sum.inl (73, 9)),
    Sum.inr (Sum.inl (92, 3)),
    Sum.inr (Sum.inl (73, 11)),
    Sum.inr (Sum.inl (54, 0)),
    Sum.inr (Sum.inl (107, 40)),
    Sum.inr (Sum.inl (54, 12)),
    Sum.inr (Sum.inl (107, 58)),
    Sum.inr (Sum.inl (73, 0)),
    Sum.inr (Sum.inl (92, 16)),
    Sum.inr (Sum.inl (73, 2)),
    Sum.inr (Sum.inl (92, 19)),
    Sum.inr (Sum.inl (176, 20)),
    Sum.inr (Sum.inl (111, 50)),
    Sum.inr (Sum.inl (176, 22)),
    Sum.inr (Sum.inl (111, 62)),
    Sum.inr (Sum.inl (156, 62)),
    Sum.inr (Sum.inl (230, 42)),
    Sum.inr (Sum.inl (156, 50)),
    Sum.inr (Sum.inl (230, 34)),
    Sum.inr (Sum.inl (111, 16)),
    Sum.inr (Sum.inl (176, 35)),
    Sum.inr (Sum.inl (111, 28)),
    Sum.inr (Sum.inl (176, 33)),
    Sum.inr (Sum.inl (230, 62)),
    Sum.inr (Sum.inl (156, 46)),
    Sum.inr (Sum.inl (230, 54)),
    Sum.inr (Sum.inl (156, 34)),
    Sum.inr (Sum.inl (92, 36)),
    Sum.inr (Sum.inl (73, 45)),
    Sum.inr (Sum.inl (92, 39)),
    Sum.inr (Sum.inl (73, 47)),
    Sum.inr (Sum.inl (107, 62)),
    Sum.inr (Sum.inl (54, 44)),
    Sum.inr (Sum.inl (107, 44)),
    Sum.inr (Sum.inl (54, 32)),
    Sum.inr (Sum.inl (73, 36)),
    Sum.inr (Sum.inl (92, 52)),
    Sum.inr (Sum.inl (73, 38)),
    Sum.inr (Sum.inl (92, 55)),
    Sum.inr (Sum.inl (54, 62)),
    Sum.inr (Sum.inl (107, 22)),
    Sum.inr (Sum.inl (54, 50)),
    Sum.inr (Sum.inl (107, 4)),
    Sum.inr (Sum.inl (218, 0)),
    Sum.inr (Sum.inl (127, 2)),
    Sum.inr (Sum.inl (106, 2)),
    Sum.inr (Sum.inl (184, 51)),
    Sum.inr (Sum.inl (218, 61)),
    Sum.inr (Sum.inl (127, 29)),
    Sum.inr (Sum.inl (106, 53)),
    Sum.inr (Sum.inl (184, 17)),
    Sum.inr (Sum.inl (117, 31)),
    Sum.inr (Sum.inl (42, 45)),
    Sum.inr (Sum.inl (194, 45)),
    Sum.inr (Sum.inl (74, 4)),
    Sum.inr (Sum.inl (117, 27)),
    Sum.inr (Sum.inl (42, 12)),
    Sum.inr (Sum.inl (194, 12)),
    Sum.inr (Sum.inl (74, 0)),
    Sum.inr (Sum.inl (106, 0)),
    Sum.inr (Sum.inl (184, 59)),
    Sum.inr (Sum.inl (218, 12)),
    Sum.inr (Sum.inl (127, 14)),
    Sum.inr (Sum.inl (106, 55)),
    Sum.inr (Sum.inl (184, 25)),
    Sum.inr (Sum.inl (218, 49)),
    Sum.inr (Sum.inl (127, 17)),
    Sum.inr (Sum.inl (194, 47)),
    Sum.inr (Sum.inl (74, 22)),
    Sum.inr (Sum.inl (117, 28)),
    Sum.inr (Sum.inl (42, 33)),
    Sum.inr (Sum.inl (194, 14)),
    Sum.inr (Sum.inl (74, 18)),
    Sum.inr (Sum.inl (117, 24)),
    Sum.inr (Sum.inl (42, 0)),
    Sum.inr (Sum.inl (127, 0)),
    Sum.inr (Sum.inl (218, 32)),
    Sum.inr (Sum.inl (184, 8)),
    Sum.inr (Sum.inl (106, 50)),
    Sum.inr (Sum.inl (127, 31)),
    Sum.inr (Sum.inl (218, 29)),
    Sum.inr (Sum.inl (184, 42)),
    Sum.inr (Sum.inl (106, 5)),
    Sum.inr (Sum.inl (42, 47)),
    Sum.inr (Sum.inl (117, 7)),
    Sum.inr (Sum.inl (74, 37)),
    Sum.inr (Sum.inl (194, 33)),
    Sum.inr (Sum.inl (42, 14)),
    Sum.inr (Sum.inl (117, 3)),
    Sum.inr (Sum.inl (74, 33)),
    Sum.inr (Sum.inl (194, 0)),
    Sum.inr (Sum.inl (184, 0)),
    Sum.inr (Sum.inl (106, 48)),
    Sum.inr (Sum.inl (127, 12)),
    Sum.inr (Sum.inl (218, 44)),
    Sum.inr (Sum.inl (184, 34)),
    Sum.inr (Sum.inl (106, 7)),
    Sum.inr (Sum.inl (127, 19)),
    Sum.inr (Sum.inl (218, 17)),
    Sum.inr (Sum.inl (74, 55)),
    Sum.inr (Sum.inl (194, 35)),
    Sum.inr (Sum.inl (42, 35)),
    Sum.inr (Sum.inl (117, 4)),
    Sum.inr (Sum.inl (74, 51)),
    Sum.inr (Sum.inl (194, 2)),
    Sum.inr (Sum.inl (42, 2)),
    Sum.inr (Sum.inl (117, 0)),
    Sum.inr (Sum.inl (217, 0)),
    Sum.inr (Sum.inl (201, 0)),
    Sum.inr (Sum.inl (217, 36)),
    Sum.inr (Sum.inl (201, 36)),
    Sum.inr (Sum.inl (43, 0)),
    Sum.inr (Sum.inl (164, 0)),
    Sum.inr (Sum.inl (43, 18)),
    Sum.inr (Sum.inl (164, 32)),
    Sum.inr (Sum.inl (43, 12)),
    Sum.inr (Sum.inl (164, 12)),
    Sum.inr (Sum.inl (43, 30)),
    Sum.inr (Sum.inl (164, 44)),
    Sum.inr (Sum.inl (217, 18)),
    Sum.inr (Sum.inl (201, 8)),
    Sum.inr (Sum.inl (217, 54)),
    Sum.inr (Sum.inl (201, 44)),
    Sum.inr (Sum.inl (130, 0)),
    Sum.inr (Sum.inl (90, 0)),
    Sum.inr (Sum.inl (130, 9)),
    Sum.inr (Sum.inl (90, 47)),
    Sum.inr (Sum.inl (115, 0)),
    Sum.inr (Sum.inl (75, 0)),
    Sum.inr (Sum.inl (115, 8)),
    Sum.inr (Sum.inl (75, 2))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock020Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨5120 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block020_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock020Input a
    let y := generatedSixthXiShortBlock020Output a
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
theorem generatedSixth_xi_short_block020_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock020Input a
    let y := generatedSixthXiShortBlock020Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block020_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block020_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock020Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block020_certificate a).1
    (generatedSixth_xi_short_block020_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
