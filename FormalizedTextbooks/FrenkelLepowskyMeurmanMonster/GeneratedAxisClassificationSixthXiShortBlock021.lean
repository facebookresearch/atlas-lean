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
def generatedSixthXiShortBlock021Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (115, 3)),
    Sum.inr (Sum.inl (75, 12)),
    Sum.inr (Sum.inl (115, 11)),
    Sum.inr (Sum.inl (75, 14)),
    Sum.inr (Sum.inl (130, 2)),
    Sum.inr (Sum.inl (90, 2)),
    Sum.inr (Sum.inl (130, 11)),
    Sum.inr (Sum.inl (90, 45)),
    Sum.inr (Sum.inl (201, 18)),
    Sum.inr (Sum.inl (217, 8)),
    Sum.inr (Sum.inl (201, 54)),
    Sum.inr (Sum.inl (217, 44)),
    Sum.inr (Sum.inl (164, 18)),
    Sum.inr (Sum.inl (43, 32)),
    Sum.inr (Sum.inl (164, 50)),
    Sum.inr (Sum.inl (43, 50)),
    Sum.inr (Sum.inl (164, 30)),
    Sum.inr (Sum.inl (43, 44)),
    Sum.inr (Sum.inl (164, 62)),
    Sum.inr (Sum.inl (43, 62)),
    Sum.inr (Sum.inl (201, 26)),
    Sum.inr (Sum.inl (217, 26)),
    Sum.inr (Sum.inl (201, 62)),
    Sum.inr (Sum.inl (217, 62)),
    Sum.inr (Sum.inl (90, 9)),
    Sum.inr (Sum.inl (130, 31)),
    Sum.inr (Sum.inl (90, 38)),
    Sum.inr (Sum.inl (130, 22)),
    Sum.inr (Sum.inl (75, 33)),
    Sum.inr (Sum.inl (115, 31)),
    Sum.inr (Sum.inl (75, 35)),
    Sum.inr (Sum.inl (115, 23)),
    Sum.inr (Sum.inl (75, 45)),
    Sum.inr (Sum.inl (115, 28)),
    Sum.inr (Sum.inl (75, 47)),
    Sum.inr (Sum.inl (115, 20)),
    Sum.inr (Sum.inl (90, 11)),
    Sum.inr (Sum.inl (130, 29)),
    Sum.inr (Sum.inl (90, 36)),
    Sum.inr (Sum.inl (130, 20)),
    Sum.inr (Sum.inl (45, 0)),
    Sum.inr (Sum.inl (101, 0)),
    Sum.inr (Sum.inl (182, 0)),
    Sum.inr (Sum.inl (120, 0)),
    Sum.inr (Sum.inl (224, 0)),
    Sum.inr (Sum.inl (82, 0)),
    Sum.inr (Sum.inl (200, 0)),
    Sum.inr (Sum.inl (76, 0)),
    Sum.inr (Sum.inl (45, 3)),
    Sum.inr (Sum.inl (101, 2)),
    Sum.inr (Sum.inl (182, 18)),
    Sum.inr (Sum.inl (120, 12)),
    Sum.inr (Sum.inl (224, 2)),
    Sum.inr (Sum.inl (82, 12)),
    Sum.inr (Sum.inl (200, 12)),
    Sum.inr (Sum.inl (76, 8)),
    Sum.inr (Sum.inl (224, 9)),
    Sum.inr (Sum.inl (82, 18)),
    Sum.inr (Sum.inl (200, 34)),
    Sum.inr (Sum.inl (76, 20)),
    Sum.inr (Sum.inl (45, 16)),
    Sum.inr (Sum.inl (101, 47)),
    Sum.inr (Sum.inl (182, 40)),
    Sum.inr (Sum.inl (120, 32)),
    Sum.inr (Sum.inl (224, 11)),
    Sum.inr (Sum.inl (82, 30)),
    Sum.inr (Sum.inl (200, 46)),
    Sum.inr (Sum.inl (76, 28)),
    Sum.inr (Sum.inl (45, 19)),
    Sum.inr (Sum.inl (101, 45)),
    Sum.inr (Sum.inl (182, 58)),
    Sum.inr (Sum.inl (120, 44)),
    Sum.inr (Sum.inl (101, 9)),
    Sum.inr (Sum.inl (45, 59)),
    Sum.inr (Sum.inl (120, 17)),
    Sum.inr (Sum.inl (182, 59)),
    Sum.inr (Sum.inl (82, 1)),
    Sum.inr (Sum.inl (224, 59)),
    Sum.inr (Sum.inl (76, 33)),
    Sum.inr (Sum.inl (200, 47)),
    Sum.inr (Sum.inl (101, 11)),
    Sum.inr (Sum.inl (45, 56)),
    Sum.inr (Sum.inl (120, 29)),
    Sum.inr (Sum.inl (182, 41)),
    Sum.inr (Sum.inl (82, 13)),
    Sum.inr (Sum.inl (224, 57)),
    Sum.inr (Sum.inl (76, 41)),
    Sum.inr (Sum.inl (200, 35)),
    Sum.inr (Sum.inl (82, 19)),
    Sum.inr (Sum.inl (224, 50)),
    Sum.inr (Sum.inl (76, 53)),
    Sum.inr (Sum.inl (200, 13)),
    Sum.inr (Sum.inl (101, 38)),
    Sum.inr (Sum.inl (45, 43)),
    Sum.inr (Sum.inl (120, 49)),
    Sum.inr (Sum.inl (182, 19)),
    Sum.inr (Sum.inl (82, 31)),
    Sum.inr (Sum.inl (224, 48)),
    Sum.inr (Sum.inl (76, 61)),
    Sum.inr (Sum.inl (200, 1)),
    Sum.inr (Sum.inl (101, 36)),
    Sum.inr (Sum.inl (45, 40)),
    Sum.inr (Sum.inl (120, 61)),
    Sum.inr (Sum.inl (182, 1)),
    Sum.inr (Sum.inl (100, 0)),
    Sum.inr (Sum.inl (162, 31)),
    Sum.inr (Sum.inl (134, 21)),
    Sum.inr (Sum.inl (223, 8)),
    Sum.inr (Sum.inl (162, 21)),
    Sum.inr (Sum.inl (100, 31)),
    Sum.inr (Sum.inl (223, 44)),
    Sum.inr (Sum.inl (134, 5)),
    Sum.inr (Sum.inl (134, 31)),
    Sum.inr (Sum.inl (223, 0)),
    Sum.inr (Sum.inl (100, 16)),
    Sum.inr (Sum.inl (162, 15)),
    Sum.inr (Sum.inl (223, 36)),
    Sum.inr (Sum.inl (134, 15)),
    Sum.inr (Sum.inl (162, 5)),
    Sum.inr (Sum.inl (100, 15)),
    Sum.inr (Sum.inl (191, 53)),
    Sum.inr (Sum.inl (86, 31)),
    Sum.inr (Sum.inl (44, 41)),
    Sum.inr (Sum.inl (77, 5)),
    Sum.inr (Sum.inl (86, 25)),
    Sum.inr (Sum.inl (191, 17)),
    Sum.inr (Sum.inl (77, 0)),
    Sum.inr (Sum.inl (44, 9)),
    Sum.inr (Sum.inl (44, 47)),
    Sum.inr (Sum.inl (77, 15)),
    Sum.inr (Sum.inl (191, 36)),
    Sum.inr (Sum.inl (86, 15)),
    Sum.inr (Sum.inl (77, 10)),
    Sum.inr (Sum.inl (44, 15)),
    Sum.inr (Sum.inl (86, 9)),
    Sum.inr (Sum.inl (191, 0)),
    Sum.inr (Sum.inl (100, 10)),
    Sum.inr (Sum.inl (162, 0)),
    Sum.inr (Sum.inl (134, 10)),
    Sum.inr (Sum.inl (223, 53)),
    Sum.inr (Sum.inl (162, 10)),
    Sum.inr (Sum.inl (100, 21)),
    Sum.inr (Sum.inl (223, 17)),
    Sum.inr (Sum.inl (134, 26)),
    Sum.inr (Sum.inl (134, 0)),
    Sum.inr (Sum.inl (223, 61)),
    Sum.inr (Sum.inl (100, 26)),
    Sum.inr (Sum.inl (162, 16)),
    Sum.inr (Sum.inl (223, 25)),
    Sum.inr (Sum.inl (134, 16)),
    Sum.inr (Sum.inl (162, 26)),
    Sum.inr (Sum.inl (100, 5)),
    Sum.inr (Sum.inl (191, 61)),
    Sum.inr (Sum.inl (86, 22)),
    Sum.inr (Sum.inl (44, 32)),
    Sum.inr (Sum.inl (77, 37)),
    Sum.inr (Sum.inl (86, 16)),
    Sum.inr (Sum.inl (191, 25)),
    Sum.inr (Sum.inl (77, 32)),
    Sum.inr (Sum.inl (44, 0)),
    Sum.inr (Sum.inl (44, 38)),
    Sum.inr (Sum.inl (77, 47)),
    Sum.inr (Sum.inl (191, 44)),
    Sum.inr (Sum.inl (86, 6)),
    Sum.inr (Sum.inl (77, 42)),
    Sum.inr (Sum.inl (44, 6)),
    Sum.inr (Sum.inl (86, 0)),
    Sum.inr (Sum.inl (191, 8)),
    Sum.inr (Sum.inl (55, 9)),
    Sum.inr (Sum.inl (155, 12)),
    Sum.inr (Sum.inl (225, 8)),
    Sum.inr (Sum.inl (124, 59)),
    Sum.inr (Sum.inl (177, 24)),
    Sum.inr (Sum.inl (72, 18)),
    Sum.inr (Sum.inl (139, 2)),
    Sum.inr (Sum.inl (78, 47)),
    Sum.inr (Sum.inl (177, 27)),
    Sum.inr (Sum.inl (72, 30)),
    Sum.inr (Sum.inl (139, 14)),
    Sum.inr (Sum.inl (78, 35)),
    Sum.inr (Sum.inl (55, 11)),
    Sum.inr (Sum.inl (155, 14)),
    Sum.inr (Sum.inl (225, 26)),
    Sum.inr (Sum.inl (124, 51)),
    Sum.inr (Sum.inl (55, 24)),
    Sum.inr (Sum.inl (155, 59)),
    Sum.inr (Sum.inl (225, 32)),
    Sum.inr (Sum.inl (124, 47)),
    Sum.inr (Sum.inl (177, 8)),
    Sum.inr (Sum.inl (72, 48)),
    Sum.inr (Sum.inl (139, 32)),
    Sum.inr (Sum.inl (78, 63)),
    Sum.inr (Sum.inl (177, 11)),
    Sum.inr (Sum.inl (72, 60)),
    Sum.inr (Sum.inl (139, 44)),
    Sum.inr (Sum.inl (78, 51)),
    Sum.inr (Sum.inl (55, 26)),
    Sum.inr (Sum.inl (155, 57)),
    Sum.inr (Sum.inl (225, 50)),
    Sum.inr (Sum.inl (124, 39)),
    Sum.inr (Sum.inl (155, 29)),
    Sum.inr (Sum.inl (55, 50)),
    Sum.inr (Sum.inl (124, 26)),
    Sum.inr (Sum.inl (225, 51)),
    Sum.inr (Sum.inl (72, 19)),
    Sum.inr (Sum.inl (177, 35)),
    Sum.inr (Sum.inl (78, 14)),
    Sum.inr (Sum.inl (139, 45)),
    Sum.inr (Sum.inl (72, 31)),
    Sum.inr (Sum.inl (177, 32)),
    Sum.inr (Sum.inl (78, 2)),
    Sum.inr (Sum.inl (139, 33)),
    Sum.inr (Sum.inl (155, 31)),
    Sum.inr (Sum.inl (55, 48)),
    Sum.inr (Sum.inl (124, 18)),
    Sum.inr (Sum.inl (225, 33)),
    Sum.inr (Sum.inl (155, 42)),
    Sum.inr (Sum.inl (55, 35)),
    Sum.inr (Sum.inl (124, 14)),
    Sum.inr (Sum.inl (225, 27)),
    Sum.inr (Sum.inl (72, 49)),
    Sum.inr (Sum.inl (177, 51)),
    Sum.inr (Sum.inl (78, 30)),
    Sum.inr (Sum.inl (139, 15)),
    Sum.inr (Sum.inl (72, 61)),
    Sum.inr (Sum.inl (177, 48)),
    Sum.inr (Sum.inl (78, 18)),
    Sum.inr (Sum.inl (139, 3)),
    Sum.inr (Sum.inl (155, 40)),
    Sum.inr (Sum.inl (55, 33)),
    Sum.inr (Sum.inl (124, 6)),
    Sum.inr (Sum.inl (225, 9)),
    Sum.inr (Sum.inl (68, 56)),
    Sum.inr (Sum.inl (181, 30)),
    Sum.inr (Sum.inl (227, 57)),
    Sum.inr (Sum.inl (109, 35)),
    Sum.inr (Sum.inl (159, 49)),
    Sum.inr (Sum.inl (51, 58)),
    Sum.inr (Sum.inl (137, 53)),
    Sum.inr (Sum.inl (79, 7)),
    Sum.inr (Sum.inl (159, 50)),
    Sum.inr (Sum.inl (51, 54)),
    Sum.inr (Sum.inl (137, 57)),
    Sum.inr (Sum.inl (79, 11)),
    Sum.inr (Sum.inl (68, 58)),
    Sum.inr (Sum.inl (181, 28)),
    Sum.inr (Sum.inl (227, 43)),
    Sum.inr (Sum.inl (109, 43)),
    Sum.inr (Sum.inl (68, 49)),
    Sum.inr (Sum.inl (181, 41)),
    Sum.inr (Sum.inl (227, 29)),
    Sum.inr (Sum.inl (109, 7)),
    Sum.inr (Sum.inl (159, 57)),
    Sum.inr (Sum.inl (51, 56)),
    Sum.inr (Sum.inl (137, 39)),
    Sum.inr (Sum.inl (79, 23))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock021Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨5376 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block021_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock021Input a
    let y := generatedSixthXiShortBlock021Output a
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
theorem generatedSixth_xi_short_block021_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock021Input a
    let y := generatedSixthXiShortBlock021Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block021_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block021_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock021Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block021_certificate a).1
    (generatedSixth_xi_short_block021_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
