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
def generatedSixthXiShortBlock022Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (159, 58)),
    Sum.inr (Sum.inl (51, 52)),
    Sum.inr (Sum.inl (137, 43)),
    Sum.inr (Sum.inl (79, 27)),
    Sum.inr (Sum.inl (68, 51)),
    Sum.inr (Sum.inl (181, 43)),
    Sum.inr (Sum.inl (227, 15)),
    Sum.inr (Sum.inl (109, 15)),
    Sum.inr (Sum.inl (181, 15)),
    Sum.inr (Sum.inl (68, 39)),
    Sum.inr (Sum.inl (109, 50)),
    Sum.inr (Sum.inl (227, 14)),
    Sum.inr (Sum.inl (51, 27)),
    Sum.inr (Sum.inl (159, 46)),
    Sum.inr (Sum.inl (79, 38)),
    Sum.inr (Sum.inl (137, 42)),
    Sum.inr (Sum.inl (51, 23)),
    Sum.inr (Sum.inl (159, 45)),
    Sum.inr (Sum.inl (79, 42)),
    Sum.inr (Sum.inl (137, 38)),
    Sum.inr (Sum.inl (181, 13)),
    Sum.inr (Sum.inl (68, 37)),
    Sum.inr (Sum.inl (109, 58)),
    Sum.inr (Sum.inl (227, 28)),
    Sum.inr (Sum.inl (181, 56)),
    Sum.inr (Sum.inl (68, 46)),
    Sum.inr (Sum.inl (109, 22)),
    Sum.inr (Sum.inl (227, 42)),
    Sum.inr (Sum.inl (51, 25)),
    Sum.inr (Sum.inl (159, 38)),
    Sum.inr (Sum.inl (79, 54)),
    Sum.inr (Sum.inl (137, 56)),
    Sum.inr (Sum.inl (51, 21)),
    Sum.inr (Sum.inl (159, 37)),
    Sum.inr (Sum.inl (79, 58)),
    Sum.inr (Sum.inl (137, 52)),
    Sum.inr (Sum.inl (181, 58)),
    Sum.inr (Sum.inl (68, 44)),
    Sum.inr (Sum.inl (109, 30)),
    Sum.inr (Sum.inl (227, 56)),
    Sum.inr (Sum.inl (197, 4)),
    Sum.inr (Sum.inl (226, 32)),
    Sum.inr (Sum.inl (197, 28)),
    Sum.inr (Sum.inl (226, 56)),
    Sum.inr (Sum.inl (67, 55)),
    Sum.inr (Sum.inl (123, 63)),
    Sum.inr (Sum.inl (67, 53)),
    Sum.inr (Sum.inl (123, 39)),
    Sum.inr (Sum.inl (47, 36)),
    Sum.inr (Sum.inl (110, 32)),
    Sum.inr (Sum.inl (47, 38)),
    Sum.inr (Sum.inl (110, 52)),
    Sum.inr (Sum.inl (190, 61)),
    Sum.inr (Sum.inl (80, 31)),
    Sum.inr (Sum.inl (190, 41)),
    Sum.inr (Sum.inl (80, 29)),
    Sum.inr (Sum.inl (67, 35)),
    Sum.inr (Sum.inl (123, 27)),
    Sum.inr (Sum.inl (67, 33)),
    Sum.inr (Sum.inl (123, 3)),
    Sum.inr (Sum.inl (197, 58)),
    Sum.inr (Sum.inl (226, 30)),
    Sum.inr (Sum.inl (197, 34)),
    Sum.inr (Sum.inl (226, 6)),
    Sum.inr (Sum.inl (190, 28)),
    Sum.inr (Sum.inl (80, 11)),
    Sum.inr (Sum.inl (190, 8)),
    Sum.inr (Sum.inl (80, 9)),
    Sum.inr (Sum.inl (47, 26)),
    Sum.inr (Sum.inl (110, 30)),
    Sum.inr (Sum.inl (47, 24)),
    Sum.inr (Sum.inl (110, 10)),
    Sum.inr (Sum.inl (47, 12)),
    Sum.inr (Sum.inl (110, 8)),
    Sum.inr (Sum.inl (47, 14)),
    Sum.inr (Sum.inl (110, 28)),
    Sum.inr (Sum.inl (190, 10)),
    Sum.inr (Sum.inl (80, 55)),
    Sum.inr (Sum.inl (190, 30)),
    Sum.inr (Sum.inl (80, 53)),
    Sum.inr (Sum.inl (197, 6)),
    Sum.inr (Sum.inl (226, 34)),
    Sum.inr (Sum.inl (197, 30)),
    Sum.inr (Sum.inl (226, 58)),
    Sum.inr (Sum.inl (67, 9)),
    Sum.inr (Sum.inl (123, 1)),
    Sum.inr (Sum.inl (67, 11)),
    Sum.inr (Sum.inl (123, 25)),
    Sum.inr (Sum.inl (190, 43)),
    Sum.inr (Sum.inl (80, 35)),
    Sum.inr (Sum.inl (190, 63)),
    Sum.inr (Sum.inl (80, 33)),
    Sum.inr (Sum.inl (47, 50)),
    Sum.inr (Sum.inl (110, 54)),
    Sum.inr (Sum.inl (47, 48)),
    Sum.inr (Sum.inl (110, 34)),
    Sum.inr (Sum.inl (67, 29)),
    Sum.inr (Sum.inl (123, 37)),
    Sum.inr (Sum.inl (67, 31)),
    Sum.inr (Sum.inl (123, 61)),
    Sum.inr (Sum.inl (197, 56)),
    Sum.inr (Sum.inl (226, 28)),
    Sum.inr (Sum.inl (197, 32)),
    Sum.inr (Sum.inl (226, 4)),
    Sum.inr (Sum.inr (119, 2)),
    Sum.inr (Sum.inr (418, 2)),
    Sum.inr (Sum.inr (425, 2)),
    Sum.inr (Sum.inr (124, 2)),
    Sum.inr (Sum.inr (61, 9)),
    Sum.inr (Sum.inr (488, 9)),
    Sum.inr (Sum.inr (483, 9)),
    Sum.inr (Sum.inr (54, 9)),
    Sum.inr (Sum.inr (253, 2)),
    Sum.inr (Sum.inr (296, 2)),
    Sum.inr (Sum.inr (291, 2)),
    Sum.inr (Sum.inr (246, 2)),
    Sum.inr (Sum.inr (183, 9)),
    Sum.inr (Sum.inr (354, 9)),
    Sum.inr (Sum.inr (361, 9)),
    Sum.inr (Sum.inr (188, 9)),
    Sum.inr (Sum.inr (188, 2)),
    Sum.inr (Sum.inr (361, 2)),
    Sum.inr (Sum.inr (354, 2)),
    Sum.inr (Sum.inr (183, 2)),
    Sum.inr (Sum.inr (246, 9)),
    Sum.inr (Sum.inr (291, 9)),
    Sum.inr (Sum.inr (296, 9)),
    Sum.inr (Sum.inr (253, 9)),
    Sum.inr (Sum.inr (54, 2)),
    Sum.inr (Sum.inr (483, 2)),
    Sum.inr (Sum.inr (488, 2)),
    Sum.inr (Sum.inr (61, 2)),
    Sum.inr (Sum.inr (124, 9)),
    Sum.inr (Sum.inr (425, 9)),
    Sum.inr (Sum.inr (418, 9)),
    Sum.inr (Sum.inr (119, 9)),
    Sum.inr (Sum.inr (61, 14)),
    Sum.inr (Sum.inr (488, 14)),
    Sum.inr (Sum.inr (483, 14)),
    Sum.inr (Sum.inr (54, 14)),
    Sum.inr (Sum.inr (119, 21)),
    Sum.inr (Sum.inr (418, 21)),
    Sum.inr (Sum.inr (425, 21)),
    Sum.inr (Sum.inr (124, 21)),
    Sum.inr (Sum.inr (183, 14)),
    Sum.inr (Sum.inr (354, 14)),
    Sum.inr (Sum.inr (361, 14)),
    Sum.inr (Sum.inr (188, 14)),
    Sum.inr (Sum.inr (253, 21)),
    Sum.inr (Sum.inr (296, 21)),
    Sum.inr (Sum.inr (291, 21)),
    Sum.inr (Sum.inr (246, 21)),
    Sum.inr (Sum.inr (246, 14)),
    Sum.inr (Sum.inr (291, 14)),
    Sum.inr (Sum.inr (296, 14)),
    Sum.inr (Sum.inr (253, 14)),
    Sum.inr (Sum.inr (188, 21)),
    Sum.inr (Sum.inr (361, 21)),
    Sum.inr (Sum.inr (354, 21)),
    Sum.inr (Sum.inr (183, 21)),
    Sum.inr (Sum.inr (124, 14)),
    Sum.inr (Sum.inr (425, 14)),
    Sum.inr (Sum.inr (418, 14)),
    Sum.inr (Sum.inr (119, 14)),
    Sum.inr (Sum.inr (54, 21)),
    Sum.inr (Sum.inr (483, 21)),
    Sum.inr (Sum.inr (488, 21)),
    Sum.inr (Sum.inr (61, 21)),
    Sum.inr (Sum.inl (182, 2)),
    Sum.inr (Sum.inl (182, 57)),
    Sum.inr (Sum.inl (76, 22)),
    Sum.inr (Sum.inl (76, 55)),
    Sum.inr (Sum.inl (120, 38)),
    Sum.inr (Sum.inl (120, 55)),
    Sum.inr (Sum.inl (200, 8)),
    Sum.inr (Sum.inl (200, 39)),
    Sum.inr (Sum.inl (120, 42)),
    Sum.inr (Sum.inl (120, 59)),
    Sum.inr (Sum.inl (200, 4)),
    Sum.inr (Sum.inl (200, 43)),
    Sum.inr (Sum.inl (182, 16)),
    Sum.inr (Sum.inl (182, 43)),
    Sum.inr (Sum.inl (76, 30)),
    Sum.inr (Sum.inl (76, 63)),
    Sum.inr (Sum.inl (76, 2)),
    Sum.inr (Sum.inl (76, 35)),
    Sum.inr (Sum.inl (182, 42)),
    Sum.inr (Sum.inl (182, 17)),
    Sum.inr (Sum.inl (200, 42)),
    Sum.inr (Sum.inl (200, 5)),
    Sum.inr (Sum.inl (120, 6)),
    Sum.inr (Sum.inl (120, 23)),
    Sum.inr (Sum.inl (200, 38)),
    Sum.inr (Sum.inl (200, 9)),
    Sum.inr (Sum.inl (120, 10)),
    Sum.inr (Sum.inl (120, 27)),
    Sum.inr (Sum.inl (76, 10)),
    Sum.inr (Sum.inl (76, 43)),
    Sum.inr (Sum.inl (182, 56)),
    Sum.inr (Sum.inl (182, 3)),
    Sum.inr (Sum.inl (101, 43)),
    Sum.inr (Sum.inl (101, 34)),
    Sum.inr (Sum.inl (224, 34)),
    Sum.inr (Sum.inl (224, 25)),
    Sum.inr (Sum.inl (45, 34)),
    Sum.inr (Sum.inl (45, 25)),
    Sum.inr (Sum.inl (82, 54)),
    Sum.inr (Sum.inl (82, 55)),
    Sum.inr (Sum.inl (45, 33)),
    Sum.inr (Sum.inl (45, 26)),
    Sum.inr (Sum.inl (82, 58)),
    Sum.inr (Sum.inl (82, 59)),
    Sum.inr (Sum.inl (101, 41)),
    Sum.inr (Sum.inl (101, 32)),
    Sum.inr (Sum.inl (224, 32)),
    Sum.inr (Sum.inl (224, 27)),
    Sum.inr (Sum.inl (224, 43)),
    Sum.inr (Sum.inl (224, 16)),
    Sum.inr (Sum.inl (101, 4)),
    Sum.inr (Sum.inl (101, 13)),
    Sum.inr (Sum.inl (82, 36)),
    Sum.inr (Sum.inl (82, 37)),
    Sum.inr (Sum.inl (45, 50)),
    Sum.inr (Sum.inl (45, 9)),
    Sum.inr (Sum.inl (82, 40)),
    Sum.inr (Sum.inl (82, 41)),
    Sum.inr (Sum.inl (45, 49)),
    Sum.inr (Sum.inl (45, 10)),
    Sum.inr (Sum.inl (224, 41)),
    Sum.inr (Sum.inl (224, 18)),
    Sum.inr (Sum.inl (101, 6)),
    Sum.inr (Sum.inl (101, 15)),
    Sum.inr (Sum.inr (119, 20)),
    Sum.inr (Sum.inr (61, 12)),
    Sum.inr (Sum.inr (119, 10)),
    Sum.inr (Sum.inr (61, 3)),
    Sum.inr (Sum.inr (418, 12)),
    Sum.inr (Sum.inr (488, 20)),
    Sum.inr (Sum.inr (418, 3)),
    Sum.inr (Sum.inr (488, 10)),
    Sum.inr (Sum.inr (425, 12)),
    Sum.inr (Sum.inr (483, 20)),
    Sum.inr (Sum.inr (425, 3)),
    Sum.inr (Sum.inr (483, 10)),
    Sum.inr (Sum.inr (124, 20)),
    Sum.inr (Sum.inr (54, 12)),
    Sum.inr (Sum.inr (124, 10)),
    Sum.inr (Sum.inr (54, 3)),
    Sum.inr (Sum.inr (119, 3)),
    Sum.inr (Sum.inr (61, 10)),
    Sum.inr (Sum.inr (119, 12)),
    Sum.inr (Sum.inr (61, 20)),
    Sum.inr (Sum.inr (418, 10)),
    Sum.inr (Sum.inr (488, 3)),
    Sum.inr (Sum.inr (418, 20)),
    Sum.inr (Sum.inr (488, 12))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock022Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨5632 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block022_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock022Input a
    let y := generatedSixthXiShortBlock022Output a
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
theorem generatedSixth_xi_short_block022_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock022Input a
    let y := generatedSixthXiShortBlock022Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block022_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block022_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock022Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block022_certificate a).1
    (generatedSixth_xi_short_block022_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
