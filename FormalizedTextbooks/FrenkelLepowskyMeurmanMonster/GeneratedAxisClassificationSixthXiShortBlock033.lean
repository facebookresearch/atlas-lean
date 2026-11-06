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
def generatedSixthXiShortBlock033Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (47, 4)),
    Sum.inr (Sum.inl (226, 20)),
    Sum.inr (Sum.inl (47, 16)),
    Sum.inr (Sum.inl (226, 48)),
    Sum.inr (Sum.inl (80, 1)),
    Sum.inr (Sum.inl (67, 8)),
    Sum.inr (Sum.inl (80, 63)),
    Sum.inr (Sum.inl (67, 32)),
    Sum.inr (Sum.inl (80, 23)),
    Sum.inr (Sum.inl (67, 30)),
    Sum.inr (Sum.inl (80, 41)),
    Sum.inr (Sum.inl (67, 54)),
    Sum.inr (Sum.inl (47, 56)),
    Sum.inr (Sum.inl (226, 50)),
    Sum.inr (Sum.inl (47, 44)),
    Sum.inr (Sum.inl (226, 22)),
    Sum.inr (Sum.inl (190, 51)),
    Sum.inr (Sum.inl (123, 54)),
    Sum.inr (Sum.inl (190, 49)),
    Sum.inr (Sum.inl (123, 52)),
    Sum.inr (Sum.inl (110, 44)),
    Sum.inr (Sum.inl (197, 42)),
    Sum.inr (Sum.inl (110, 46)),
    Sum.inr (Sum.inl (197, 14)),
    Sum.inr (Sum.inl (190, 39)),
    Sum.inr (Sum.inl (123, 46)),
    Sum.inr (Sum.inl (190, 37)),
    Sum.inr (Sum.inl (123, 44)),
    Sum.inr (Sum.inl (110, 56)),
    Sum.inr (Sum.inl (197, 50)),
    Sum.inr (Sum.inl (110, 58)),
    Sum.inr (Sum.inl (197, 22)),
    Sum.inr (Sum.inl (80, 21)),
    Sum.inr (Sum.inl (67, 28)),
    Sum.inr (Sum.inl (80, 43)),
    Sum.inr (Sum.inl (67, 52)),
    Sum.inr (Sum.inl (47, 58)),
    Sum.inr (Sum.inl (226, 42)),
    Sum.inr (Sum.inl (47, 46)),
    Sum.inr (Sum.inl (226, 14)),
    Sum.inr (Sum.inl (177, 10)),
    Sum.inr (Sum.inl (155, 6)),
    Sum.inr (Sum.inl (225, 2)),
    Sum.inr (Sum.inl (78, 55)),
    Sum.inr (Sum.inl (55, 27)),
    Sum.inr (Sum.inl (72, 58)),
    Sum.inr (Sum.inl (139, 42)),
    Sum.inr (Sum.inl (124, 35)),
    Sum.inr (Sum.inl (177, 9)),
    Sum.inr (Sum.inl (155, 4)),
    Sum.inr (Sum.inl (225, 16)),
    Sum.inr (Sum.inl (78, 59)),
    Sum.inr (Sum.inl (55, 25)),
    Sum.inr (Sum.inl (72, 54)),
    Sum.inr (Sum.inl (139, 38)),
    Sum.inr (Sum.inl (124, 43)),
    Sum.inr (Sum.inl (55, 10)),
    Sum.inr (Sum.inl (72, 24)),
    Sum.inr (Sum.inl (139, 8)),
    Sum.inr (Sum.inl (124, 55)),
    Sum.inr (Sum.inl (177, 26)),
    Sum.inr (Sum.inl (155, 49)),
    Sum.inr (Sum.inl (225, 42)),
    Sum.inr (Sum.inl (78, 39)),
    Sum.inr (Sum.inl (55, 8)),
    Sum.inr (Sum.inl (72, 20)),
    Sum.inr (Sum.inl (139, 4)),
    Sum.inr (Sum.inl (124, 63)),
    Sum.inr (Sum.inl (177, 25)),
    Sum.inr (Sum.inl (155, 51)),
    Sum.inr (Sum.inl (225, 56)),
    Sum.inr (Sum.inl (78, 43)),
    Sum.inr (Sum.inl (155, 23)),
    Sum.inr (Sum.inl (177, 49)),
    Sum.inr (Sum.inl (78, 22)),
    Sum.inr (Sum.inl (225, 57)),
    Sum.inr (Sum.inl (72, 59)),
    Sum.inr (Sum.inl (55, 32)),
    Sum.inr (Sum.inl (124, 2)),
    Sum.inr (Sum.inl (139, 5)),
    Sum.inr (Sum.inl (155, 21)),
    Sum.inr (Sum.inl (177, 50)),
    Sum.inr (Sum.inl (78, 26)),
    Sum.inr (Sum.inl (225, 43)),
    Sum.inr (Sum.inl (72, 55)),
    Sum.inr (Sum.inl (55, 34)),
    Sum.inr (Sum.inl (124, 10)),
    Sum.inr (Sum.inl (139, 9)),
    Sum.inr (Sum.inl (72, 25)),
    Sum.inr (Sum.inl (55, 49)),
    Sum.inr (Sum.inl (124, 22)),
    Sum.inr (Sum.inl (139, 39)),
    Sum.inr (Sum.inl (155, 32)),
    Sum.inr (Sum.inl (177, 33)),
    Sum.inr (Sum.inl (78, 6)),
    Sum.inr (Sum.inl (225, 17)),
    Sum.inr (Sum.inl (72, 21)),
    Sum.inr (Sum.inl (55, 51)),
    Sum.inr (Sum.inl (124, 30)),
    Sum.inr (Sum.inl (139, 43)),
    Sum.inr (Sum.inl (155, 34)),
    Sum.inr (Sum.inl (177, 34)),
    Sum.inr (Sum.inl (78, 10)),
    Sum.inr (Sum.inl (225, 3)),
    Sum.inr (Sum.inl (216, 55)),
    Sum.inr (Sum.inl (138, 36)),
    Sum.inr (Sum.inl (216, 31)),
    Sum.inr (Sum.inl (138, 31)),
    Sum.inr (Sum.inl (108, 61)),
    Sum.inr (Sum.inl (154, 31)),
    Sum.inr (Sum.inl (108, 63)),
    Sum.inr (Sum.inl (154, 63)),
    Sum.inr (Sum.inl (108, 49)),
    Sum.inr (Sum.inl (154, 19)),
    Sum.inr (Sum.inl (108, 51)),
    Sum.inr (Sum.inl (154, 51)),
    Sum.inr (Sum.inl (216, 53)),
    Sum.inr (Sum.inl (138, 44)),
    Sum.inr (Sum.inl (216, 29)),
    Sum.inr (Sum.inl (138, 23)),
    Sum.inr (Sum.inl (91, 54)),
    Sum.inr (Sum.inl (186, 19)),
    Sum.inr (Sum.inl (91, 23)),
    Sum.inr (Sum.inl (186, 7)),
    Sum.inr (Sum.inl (41, 43)),
    Sum.inr (Sum.inl (125, 13)),
    Sum.inr (Sum.inl (41, 15)),
    Sum.inr (Sum.inl (125, 15)),
    Sum.inr (Sum.inl (41, 40)),
    Sum.inr (Sum.inl (125, 1)),
    Sum.inr (Sum.inl (41, 12)),
    Sum.inr (Sum.inl (125, 3)),
    Sum.inr (Sum.inl (91, 36)),
    Sum.inr (Sum.inl (186, 17)),
    Sum.inr (Sum.inl (91, 5)),
    Sum.inr (Sum.inl (186, 5)),
    Sum.inr (Sum.inl (138, 6)),
    Sum.inr (Sum.inl (216, 24)),
    Sum.inr (Sum.inl (138, 61)),
    Sum.inr (Sum.inl (216, 48)),
    Sum.inr (Sum.inl (154, 34)),
    Sum.inr (Sum.inl (108, 34)),
    Sum.inr (Sum.inl (154, 2)),
    Sum.inr (Sum.inl (108, 32)),
    Sum.inr (Sum.inl (154, 46)),
    Sum.inr (Sum.inl (108, 46)),
    Sum.inr (Sum.inl (154, 14)),
    Sum.inr (Sum.inl (108, 44)),
    Sum.inr (Sum.inl (138, 14)),
    Sum.inr (Sum.inl (216, 26)),
    Sum.inr (Sum.inl (138, 53)),
    Sum.inr (Sum.inl (216, 50)),
    Sum.inr (Sum.inl (186, 50)),
    Sum.inr (Sum.inl (91, 50)),
    Sum.inr (Sum.inl (186, 38)),
    Sum.inr (Sum.inl (91, 19)),
    Sum.inr (Sum.inl (125, 44)),
    Sum.inr (Sum.inl (41, 35)),
    Sum.inr (Sum.inl (125, 46)),
    Sum.inr (Sum.inl (41, 7)),
    Sum.inr (Sum.inl (125, 32)),
    Sum.inr (Sum.inl (41, 32)),
    Sum.inr (Sum.inl (125, 34)),
    Sum.inr (Sum.inl (41, 4)),
    Sum.inr (Sum.inl (186, 48)),
    Sum.inr (Sum.inl (91, 32)),
    Sum.inr (Sum.inl (186, 36)),
    Sum.inr (Sum.inl (91, 1)),
    Sum.inr (Sum.inr (62, 21)),
    Sum.inr (Sum.inr (62, 9)),
    Sum.inr (Sum.inr (116, 14)),
    Sum.inr (Sum.inr (116, 2)),
    Sum.inr (Sum.inr (417, 14)),
    Sum.inr (Sum.inr (417, 2)),
    Sum.inr (Sum.inr (491, 21)),
    Sum.inr (Sum.inr (491, 9)),
    Sum.inr (Sum.inr (426, 14)),
    Sum.inr (Sum.inr (426, 2)),
    Sum.inr (Sum.inr (480, 21)),
    Sum.inr (Sum.inr (480, 9)),
    Sum.inr (Sum.inr (53, 21)),
    Sum.inr (Sum.inr (53, 9)),
    Sum.inr (Sum.inr (127, 14)),
    Sum.inr (Sum.inr (127, 2)),
    Sum.inr (Sum.inr (191, 14)),
    Sum.inr (Sum.inr (191, 2)),
    Sum.inr (Sum.inr (245, 21)),
    Sum.inr (Sum.inr (245, 9)),
    Sum.inr (Sum.inr (288, 21)),
    Sum.inr (Sum.inr (288, 9)),
    Sum.inr (Sum.inr (362, 14)),
    Sum.inr (Sum.inr (362, 2)),
    Sum.inr (Sum.inr (299, 21)),
    Sum.inr (Sum.inr (299, 9)),
    Sum.inr (Sum.inr (353, 14)),
    Sum.inr (Sum.inr (353, 2)),
    Sum.inr (Sum.inr (180, 14)),
    Sum.inr (Sum.inr (180, 2)),
    Sum.inr (Sum.inr (254, 21)),
    Sum.inr (Sum.inr (254, 9)),
    Sum.inr (Sum.inr (62, 2)),
    Sum.inr (Sum.inr (62, 14)),
    Sum.inr (Sum.inr (116, 9)),
    Sum.inr (Sum.inr (116, 21)),
    Sum.inr (Sum.inr (417, 9)),
    Sum.inr (Sum.inr (417, 21)),
    Sum.inr (Sum.inr (491, 2)),
    Sum.inr (Sum.inr (491, 14)),
    Sum.inr (Sum.inr (426, 9)),
    Sum.inr (Sum.inr (426, 21)),
    Sum.inr (Sum.inr (480, 2)),
    Sum.inr (Sum.inr (480, 14)),
    Sum.inr (Sum.inr (53, 2)),
    Sum.inr (Sum.inr (53, 14)),
    Sum.inr (Sum.inr (127, 9)),
    Sum.inr (Sum.inr (127, 21)),
    Sum.inr (Sum.inr (191, 9)),
    Sum.inr (Sum.inr (191, 21)),
    Sum.inr (Sum.inr (245, 2)),
    Sum.inr (Sum.inr (245, 14)),
    Sum.inr (Sum.inr (288, 2)),
    Sum.inr (Sum.inr (288, 14)),
    Sum.inr (Sum.inr (362, 9)),
    Sum.inr (Sum.inr (362, 21)),
    Sum.inr (Sum.inr (299, 2)),
    Sum.inr (Sum.inr (299, 14)),
    Sum.inr (Sum.inr (353, 9)),
    Sum.inr (Sum.inr (353, 21)),
    Sum.inr (Sum.inr (180, 9)),
    Sum.inr (Sum.inr (180, 21)),
    Sum.inr (Sum.inr (254, 2)),
    Sum.inr (Sum.inr (254, 14)),
    Sum.inr (Sum.inl (194, 18)),
    Sum.inr (Sum.inl (184, 24)),
    Sum.inr (Sum.inl (194, 30)),
    Sum.inr (Sum.inl (184, 35)),
    Sum.inr (Sum.inl (42, 24)),
    Sum.inr (Sum.inl (218, 24)),
    Sum.inr (Sum.inl (42, 26)),
    Sum.inr (Sum.inl (218, 56)),
    Sum.inr (Sum.inl (42, 20)),
    Sum.inr (Sum.inl (218, 20)),
    Sum.inr (Sum.inl (42, 22)),
    Sum.inr (Sum.inl (218, 52)),
    Sum.inr (Sum.inl (194, 16)),
    Sum.inr (Sum.inl (184, 16)),
    Sum.inr (Sum.inl (194, 28)),
    Sum.inr (Sum.inl (184, 43)),
    Sum.inr (Sum.inl (184, 9)),
    Sum.inr (Sum.inl (194, 61)),
    Sum.inr (Sum.inl (184, 50)),
    Sum.inr (Sum.inl (194, 49)),
    Sum.inr (Sum.inl (218, 9)),
    Sum.inr (Sum.inl (42, 55)),
    Sum.inr (Sum.inl (218, 41)),
    Sum.inr (Sum.inl (42, 53))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock033Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨8448 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block033_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock033Input a
    let y := generatedSixthXiShortBlock033Output a
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
theorem generatedSixth_xi_short_block033_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock033Input a
    let y := generatedSixthXiShortBlock033Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block033_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block033_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock033Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block033_certificate a).1
    (generatedSixth_xi_short_block033_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
