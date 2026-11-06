/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortNumbering
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFoldedPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressMaskEight

/-! Original sparse masks and full signed phases certify a bounded part of actual short support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Candidate sparse outputs are checked against the original full binary and phase action. -/
def generatedSixthXiShortBlock036Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (59, 55)),
    Sum.inr (Sum.inl (85, 21)),
    Sum.inr (Sum.inl (59, 59)),
    Sum.inr (Sum.inl (85, 23)),
    Sum.inr (Sum.inl (135, 25)),
    Sum.inr (Sum.inl (98, 9)),
    Sum.inr (Sum.inl (135, 27)),
    Sum.inr (Sum.inl (98, 10)),
    Sum.inr (Sum.inl (85, 6)),
    Sum.inr (Sum.inl (59, 58)),
    Sum.inr (Sum.inl (85, 4)),
    Sum.inr (Sum.inl (59, 54)),
    Sum.inr (Sum.inl (98, 49)),
    Sum.inr (Sum.inl (135, 32)),
    Sum.inr (Sum.inl (98, 50)),
    Sum.inr (Sum.inl (135, 34)),
    Sum.inr (Sum.inl (59, 40)),
    Sum.inr (Sum.inl (85, 49)),
    Sum.inr (Sum.inl (59, 36)),
    Sum.inr (Sum.inl (85, 51)),
    Sum.inr (Sum.inl (135, 41)),
    Sum.inr (Sum.inl (98, 33)),
    Sum.inr (Sum.inl (135, 43)),
    Sum.inr (Sum.inl (98, 34)),
    Sum.inr (Sum.inl (183, 9)),
    Sum.inr (Sum.inl (219, 29)),
    Sum.inr (Sum.inl (183, 5)),
    Sum.inr (Sum.inl (219, 21)),
    Sum.inr (Sum.inl (199, 7)),
    Sum.inr (Sum.inl (62, 59)),
    Sum.inr (Sum.inl (199, 21)),
    Sum.inr (Sum.inl (62, 55)),
    Sum.inr (Sum.inl (219, 9)),
    Sum.inr (Sum.inl (183, 25)),
    Sum.inr (Sum.inl (219, 1)),
    Sum.inr (Sum.inl (183, 21)),
    Sum.inr (Sum.inl (62, 25)),
    Sum.inr (Sum.inl (199, 47)),
    Sum.inr (Sum.inl (62, 21)),
    Sum.inr (Sum.inl (199, 61)),
    Sum.inr (Sum.inl (95, 55)),
    Sum.inr (Sum.inl (65, 5)),
    Sum.inr (Sum.inl (189, 15)),
    Sum.inr (Sum.inl (93, 27)),
    Sum.inr (Sum.inl (229, 29)),
    Sum.inr (Sum.inl (49, 53)),
    Sum.inr (Sum.inl (198, 63)),
    Sum.inr (Sum.inl (136, 6)),
    Sum.inr (Sum.inl (95, 21)),
    Sum.inr (Sum.inl (65, 26)),
    Sum.inr (Sum.inl (189, 16)),
    Sum.inr (Sum.inl (93, 9)),
    Sum.inr (Sum.inl (229, 61)),
    Sum.inr (Sum.inl (49, 20)),
    Sum.inr (Sum.inl (198, 46)),
    Sum.inr (Sum.inl (136, 14)),
    Sum.inr (Sum.inl (189, 13)),
    Sum.inr (Sum.inl (93, 19)),
    Sum.inr (Sum.inl (95, 59)),
    Sum.inr (Sum.inl (65, 9)),
    Sum.inr (Sum.inl (198, 61)),
    Sum.inr (Sum.inl (136, 20)),
    Sum.inr (Sum.inl (229, 30)),
    Sum.inr (Sum.inl (49, 57)),
    Sum.inr (Sum.inl (189, 18)),
    Sum.inr (Sum.inl (93, 1)),
    Sum.inr (Sum.inl (95, 25)),
    Sum.inr (Sum.inl (65, 22)),
    Sum.inr (Sum.inl (198, 44)),
    Sum.inr (Sum.inl (136, 28)),
    Sum.inr (Sum.inl (229, 62)),
    Sum.inr (Sum.inl (49, 24)),
    Sum.inr (Sum.inl (65, 7)),
    Sum.inr (Sum.inl (95, 39)),
    Sum.inr (Sum.inl (93, 32)),
    Sum.inr (Sum.inl (189, 3)),
    Sum.inr (Sum.inl (49, 55)),
    Sum.inr (Sum.inl (229, 5)),
    Sum.inr (Sum.inl (136, 39)),
    Sum.inr (Sum.inl (198, 23)),
    Sum.inr (Sum.inl (65, 24)),
    Sum.inr (Sum.inl (95, 5)),
    Sum.inr (Sum.inl (93, 50)),
    Sum.inr (Sum.inl (189, 28)),
    Sum.inr (Sum.inl (49, 22)),
    Sum.inr (Sum.inl (229, 37)),
    Sum.inr (Sum.inl (136, 47)),
    Sum.inr (Sum.inl (198, 6)),
    Sum.inr (Sum.inl (93, 40)),
    Sum.inr (Sum.inl (189, 1)),
    Sum.inr (Sum.inl (65, 11)),
    Sum.inr (Sum.inl (95, 43)),
    Sum.inr (Sum.inl (136, 53)),
    Sum.inr (Sum.inl (198, 21)),
    Sum.inr (Sum.inl (49, 59)),
    Sum.inr (Sum.inl (229, 6)),
    Sum.inr (Sum.inl (93, 58)),
    Sum.inr (Sum.inl (189, 30)),
    Sum.inr (Sum.inl (65, 20)),
    Sum.inr (Sum.inl (95, 9)),
    Sum.inr (Sum.inl (136, 61)),
    Sum.inr (Sum.inl (198, 4)),
    Sum.inr (Sum.inl (49, 26)),
    Sum.inr (Sum.inl (229, 38)),
    Sum.inr (Sum.inl (181, 6)),
    Sum.inr (Sum.inl (181, 34)),
    Sum.inr (Sum.inl (109, 46)),
    Sum.inr (Sum.inl (109, 19)),
    Sum.inr (Sum.inl (79, 10)),
    Sum.inr (Sum.inl (79, 55)),
    Sum.inr (Sum.inl (51, 26)),
    Sum.inr (Sum.inl (51, 53)),
    Sum.inr (Sum.inl (79, 6)),
    Sum.inr (Sum.inl (79, 59)),
    Sum.inr (Sum.inl (51, 22)),
    Sum.inr (Sum.inl (51, 57)),
    Sum.inr (Sum.inl (181, 4)),
    Sum.inr (Sum.inl (181, 32)),
    Sum.inr (Sum.inl (109, 38)),
    Sum.inr (Sum.inl (109, 27)),
    Sum.inr (Sum.inl (109, 10)),
    Sum.inr (Sum.inl (109, 55)),
    Sum.inr (Sum.inl (181, 49)),
    Sum.inr (Sum.inl (181, 21)),
    Sum.inr (Sum.inl (51, 24)),
    Sum.inr (Sum.inl (51, 55)),
    Sum.inr (Sum.inl (79, 26)),
    Sum.inr (Sum.inl (79, 39)),
    Sum.inr (Sum.inl (51, 20)),
    Sum.inr (Sum.inl (51, 59)),
    Sum.inr (Sum.inl (79, 22)),
    Sum.inr (Sum.inl (79, 43)),
    Sum.inr (Sum.inl (109, 2)),
    Sum.inr (Sum.inl (109, 63)),
    Sum.inr (Sum.inl (181, 51)),
    Sum.inr (Sum.inl (181, 23)),
    Sum.inr (Sum.inl (227, 3)),
    Sum.inr (Sum.inl (227, 2)),
    Sum.inr (Sum.inl (68, 15)),
    Sum.inr (Sum.inl (68, 27)),
    Sum.inr (Sum.inl (159, 6)),
    Sum.inr (Sum.inl (159, 18)),
    Sum.inr (Sum.inl (137, 27)),
    Sum.inr (Sum.inl (137, 26)),
    Sum.inr (Sum.inl (159, 5)),
    Sum.inr (Sum.inl (159, 17)),
    Sum.inr (Sum.inl (137, 23)),
    Sum.inr (Sum.inl (137, 22)),
    Sum.inr (Sum.inl (227, 17)),
    Sum.inr (Sum.inl (227, 16)),
    Sum.inr (Sum.inl (68, 13)),
    Sum.inr (Sum.inl (68, 25)),
    Sum.inr (Sum.inl (68, 6)),
    Sum.inr (Sum.inl (68, 18)),
    Sum.inr (Sum.inl (227, 39)),
    Sum.inr (Sum.inl (227, 38)),
    Sum.inr (Sum.inl (137, 9)),
    Sum.inr (Sum.inl (137, 8)),
    Sum.inr (Sum.inl (159, 14)),
    Sum.inr (Sum.inl (159, 26)),
    Sum.inr (Sum.inl (137, 5)),
    Sum.inr (Sum.inl (137, 4)),
    Sum.inr (Sum.inl (159, 13)),
    Sum.inr (Sum.inl (159, 25)),
    Sum.inr (Sum.inl (68, 4)),
    Sum.inr (Sum.inl (68, 16)),
    Sum.inr (Sum.inl (227, 53)),
    Sum.inr (Sum.inl (227, 52)),
    Sum.inr (Sum.inl (41, 22)),
    Sum.inr (Sum.inl (216, 49)),
    Sum.inr (Sum.inl (186, 46)),
    Sum.inr (Sum.inl (154, 7)),
    Sum.inr (Sum.inl (91, 42)),
    Sum.inr (Sum.inl (108, 39)),
    Sum.inr (Sum.inl (125, 56)),
    Sum.inr (Sum.inl (138, 7)),
    Sum.inr (Sum.inl (41, 21)),
    Sum.inr (Sum.inl (216, 51)),
    Sum.inr (Sum.inl (186, 44)),
    Sum.inr (Sum.inl (154, 11)),
    Sum.inr (Sum.inl (91, 56)),
    Sum.inr (Sum.inl (108, 43)),
    Sum.inr (Sum.inl (125, 52)),
    Sum.inr (Sum.inl (138, 15)),
    Sum.inr (Sum.inl (216, 52)),
    Sum.inr (Sum.inl (41, 57)),
    Sum.inr (Sum.inl (154, 22)),
    Sum.inr (Sum.inl (186, 25)),
    Sum.inr (Sum.inl (108, 54)),
    Sum.inr (Sum.inl (91, 29)),
    Sum.inr (Sum.inl (138, 22)),
    Sum.inr (Sum.inl (125, 23)),
    Sum.inr (Sum.inl (216, 54)),
    Sum.inr (Sum.inl (41, 58)),
    Sum.inr (Sum.inl (154, 26)),
    Sum.inr (Sum.inl (186, 27)),
    Sum.inr (Sum.inl (108, 58)),
    Sum.inr (Sum.inl (91, 15)),
    Sum.inr (Sum.inl (138, 30)),
    Sum.inr (Sum.inl (125, 27)),
    Sum.inr (Sum.inl (186, 15)),
    Sum.inr (Sum.inl (154, 58)),
    Sum.inr (Sum.inl (41, 30)),
    Sum.inr (Sum.inl (216, 30)),
    Sum.inr (Sum.inl (125, 25)),
    Sum.inr (Sum.inl (138, 37)),
    Sum.inr (Sum.inl (91, 46)),
    Sum.inr (Sum.inl (108, 56)),
    Sum.inr (Sum.inl (186, 13)),
    Sum.inr (Sum.inl (154, 54)),
    Sum.inr (Sum.inl (41, 29)),
    Sum.inr (Sum.inl (216, 28)),
    Sum.inr (Sum.inl (125, 21)),
    Sum.inr (Sum.inl (138, 45)),
    Sum.inr (Sum.inl (91, 60)),
    Sum.inr (Sum.inl (108, 52)),
    Sum.inr (Sum.inl (154, 43)),
    Sum.inr (Sum.inl (186, 56)),
    Sum.inr (Sum.inl (216, 27)),
    Sum.inr (Sum.inl (41, 49)),
    Sum.inr (Sum.inl (138, 52)),
    Sum.inr (Sum.inl (125, 54)),
    Sum.inr (Sum.inl (108, 41)),
    Sum.inr (Sum.inl (91, 25)),
    Sum.inr (Sum.inl (154, 39)),
    Sum.inr (Sum.inl (186, 58)),
    Sum.inr (Sum.inl (216, 25)),
    Sum.inr (Sum.inl (41, 50)),
    Sum.inr (Sum.inl (138, 60)),
    Sum.inr (Sum.inl (125, 58)),
    Sum.inr (Sum.inl (108, 37)),
    Sum.inr (Sum.inl (91, 11)),
    Sum.inr (Sum.inl (155, 20)),
    Sum.inr (Sum.inl (155, 48)),
    Sum.inr (Sum.inl (124, 54)),
    Sum.inr (Sum.inl (124, 11)),
    Sum.inr (Sum.inl (78, 34)),
    Sum.inr (Sum.inl (78, 31)),
    Sum.inr (Sum.inl (72, 50)),
    Sum.inr (Sum.inl (72, 29)),
    Sum.inr (Sum.inl (78, 46)),
    Sum.inr (Sum.inl (78, 19)),
    Sum.inr (Sum.inl (72, 62)),
    Sum.inr (Sum.inl (72, 17)),
    Sum.inr (Sum.inl (155, 22)),
    Sum.inr (Sum.inl (155, 50)),
    Sum.inr (Sum.inl (124, 62)),
    Sum.inr (Sum.inl (124, 3)),
    Sum.inr (Sum.inl (225, 62)),
    Sum.inr (Sum.inl (225, 63)),
    Sum.inr (Sum.inl (55, 38)),
    Sum.inr (Sum.inl (55, 14)),
    Sum.inr (Sum.inl (177, 55)),
    Sum.inr (Sum.inl (177, 31)),
    Sum.inr (Sum.inl (139, 28)),
    Sum.inr (Sum.inl (139, 29))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock036Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨9216 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block036_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock036Input a
    let y := generatedSixthXiShortBlock036Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedPhase
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block036_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock036Input a
    let y := generatedSixthXiShortBlock036Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block036_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block036_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock036Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block036_certificate a).1
    (generatedSixth_xi_short_block036_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
