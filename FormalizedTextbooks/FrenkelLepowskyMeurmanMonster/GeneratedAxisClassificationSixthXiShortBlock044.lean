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
def generatedSixthXiShortBlock044Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (297, 12)),
    Sum.inr (Sum.inr (419, 20)),
    Sum.inr (Sum.inr (297, 10)),
    Sum.inr (Sum.inr (419, 3)),
    Sum.inr (Sum.inr (252, 20)),
    Sum.inr (Sum.inr (118, 12)),
    Sum.inr (Sum.inr (252, 3)),
    Sum.inr (Sum.inr (118, 10)),
    Sum.inr (Sum.inr (189, 3)),
    Sum.inr (Sum.inr (55, 10)),
    Sum.inr (Sum.inr (189, 20)),
    Sum.inr (Sum.inr (55, 12)),
    Sum.inr (Sum.inr (360, 10)),
    Sum.inr (Sum.inr (482, 3)),
    Sum.inr (Sum.inr (360, 12)),
    Sum.inr (Sum.inr (482, 20)),
    Sum.inr (Sum.inr (355, 10)),
    Sum.inr (Sum.inr (489, 3)),
    Sum.inr (Sum.inr (355, 12)),
    Sum.inr (Sum.inr (489, 20)),
    Sum.inr (Sum.inr (182, 3)),
    Sum.inr (Sum.inr (60, 10)),
    Sum.inr (Sum.inr (182, 20)),
    Sum.inr (Sum.inr (60, 12)),
    Sum.inr (Sum.inr (247, 10)),
    Sum.inr (Sum.inr (125, 3)),
    Sum.inr (Sum.inr (247, 12)),
    Sum.inr (Sum.inr (125, 20)),
    Sum.inr (Sum.inr (290, 3)),
    Sum.inr (Sum.inr (424, 10)),
    Sum.inr (Sum.inr (290, 20)),
    Sum.inr (Sum.inr (424, 12)),
    Sum.inr (Sum.inr (297, 3)),
    Sum.inr (Sum.inr (419, 10)),
    Sum.inr (Sum.inr (297, 20)),
    Sum.inr (Sum.inr (419, 12)),
    Sum.inr (Sum.inr (252, 10)),
    Sum.inr (Sum.inr (118, 3)),
    Sum.inr (Sum.inr (252, 12)),
    Sum.inr (Sum.inr (118, 20)),
    Sum.inr (Sum.inl (168, 61)),
    Sum.inl 83,
    Sum.inr (Sum.inl (168, 41)),
    Sum.inl 48,
    Sum.inr (Sum.inl (168, 47)),
    Sum.inl 63,
    Sum.inr (Sum.inl (168, 45)),
    Sum.inl 66,
    Sum.inl 413,
    Sum.inr (Sum.inl (168, 34)),
    Sum.inl 146,
    Sum.inr (Sum.inl (168, 54)),
    Sum.inl 371,
    Sum.inr (Sum.inl (168, 48)),
    Sum.inl 396,
    Sum.inr (Sum.inl (168, 50)),
    Sum.inr (Sum.inl (168, 59)),
    Sum.inl 67,
    Sum.inr (Sum.inl (168, 57)),
    Sum.inl 62,
    Sum.inr (Sum.inl (168, 63)),
    Sum.inl 49,
    Sum.inr (Sum.inl (168, 43)),
    Sum.inl 82,
    Sum.inl 397,
    Sum.inr (Sum.inl (168, 36)),
    Sum.inl 370,
    Sum.inr (Sum.inl (168, 38)),
    Sum.inl 147,
    Sum.inr (Sum.inl (168, 32)),
    Sum.inl 412,
    Sum.inr (Sum.inl (168, 52)),
    Sum.inl 489,
    Sum.inr (Sum.inl (168, 10)),
    Sum.inl 154,
    Sum.inr (Sum.inl (168, 30)),
    Sum.inl 379,
    Sum.inr (Sum.inl (168, 24)),
    Sum.inl 424,
    Sum.inr (Sum.inl (168, 26)),
    Sum.inr (Sum.inl (168, 3)),
    Sum.inl 543,
    Sum.inr (Sum.inl (168, 23)),
    Sum.inl 168,
    Sum.inr (Sum.inl (168, 17)),
    Sum.inl 393,
    Sum.inr (Sum.inl (168, 19)),
    Sum.inl 438,
    Sum.inl 425,
    Sum.inr (Sum.inl (168, 12)),
    Sum.inl 378,
    Sum.inr (Sum.inl (168, 14)),
    Sum.inl 155,
    Sum.inr (Sum.inl (168, 8)),
    Sum.inl 488,
    Sum.inr (Sum.inl (168, 28)),
    Sum.inr (Sum.inl (168, 5)),
    Sum.inl 439,
    Sum.inr (Sum.inl (168, 7)),
    Sum.inl 392,
    Sum.inr (Sum.inl (168, 1)),
    Sum.inl 169,
    Sum.inr (Sum.inl (168, 21)),
    Sum.inl 542,
    Sum.inr (Sum.inl (169, 34)),
    Sum.inl 39,
    Sum.inr (Sum.inl (169, 58)),
    Sum.inl 4,
    Sum.inl 335,
    Sum.inr (Sum.inl (169, 61)),
    Sum.inl 140,
    Sum.inr (Sum.inl (169, 37)),
    Sum.inr (Sum.inl (169, 48)),
    Sum.inl 19,
    Sum.inr (Sum.inl (169, 50)),
    Sum.inl 22,
    Sum.inl 315,
    Sum.inr (Sum.inl (169, 47)),
    Sum.inl 318,
    Sum.inr (Sum.inl (169, 45)),
    Sum.inr (Sum.inl (169, 40)),
    Sum.inl 23,
    Sum.inr (Sum.inl (169, 42)),
    Sum.inl 18,
    Sum.inl 319,
    Sum.inr (Sum.inl (169, 55)),
    Sum.inl 314,
    Sum.inr (Sum.inl (169, 53)),
    Sum.inr (Sum.inl (169, 32)),
    Sum.inl 5,
    Sum.inr (Sum.inl (169, 56)),
    Sum.inl 38,
    Sum.inl 141,
    Sum.inr (Sum.inl (169, 63)),
    Sum.inl 334,
    Sum.inr (Sum.inl (169, 39)),
    Sum.inl 454,
    Sum.inr (Sum.inl (169, 25)),
    Sum.inl 151,
    Sum.inr (Sum.inl (169, 1)),
    Sum.inr (Sum.inl (169, 28)),
    Sum.inl 544,
    Sum.inr (Sum.inl (169, 4)),
    Sum.inl 171,
    Sum.inl 374,
    Sum.inr (Sum.inl (169, 11)),
    Sum.inl 421,
    Sum.inr (Sum.inl (169, 9)),
    Sum.inr (Sum.inl (169, 14)),
    Sum.inl 394,
    Sum.inr (Sum.inl (169, 12)),
    Sum.inl 441,
    Sum.inl 420,
    Sum.inr (Sum.inl (169, 19)),
    Sum.inl 375,
    Sum.inr (Sum.inl (169, 17)),
    Sum.inr (Sum.inl (169, 22)),
    Sum.inl 440,
    Sum.inr (Sum.inl (169, 20)),
    Sum.inl 395,
    Sum.inl 150,
    Sum.inr (Sum.inl (169, 27)),
    Sum.inl 455,
    Sum.inr (Sum.inl (169, 3)),
    Sum.inr (Sum.inl (169, 30)),
    Sum.inl 170,
    Sum.inr (Sum.inl (169, 6)),
    Sum.inl 545,
    Sum.inr (Sum.inr (255, 10)),
    Sum.inr (Sum.inr (52, 20)),
    Sum.inr (Sum.inr (255, 12)),
    Sum.inr (Sum.inr (52, 3)),
    Sum.inr (Sum.inr (298, 20)),
    Sum.inr (Sum.inr (481, 10)),
    Sum.inr (Sum.inr (298, 3)),
    Sum.inr (Sum.inr (481, 12)),
    Sum.inr (Sum.inr (289, 20)),
    Sum.inr (Sum.inr (490, 10)),
    Sum.inr (Sum.inr (289, 3)),
    Sum.inr (Sum.inr (490, 12)),
    Sum.inr (Sum.inr (244, 10)),
    Sum.inr (Sum.inr (63, 20)),
    Sum.inr (Sum.inr (244, 12)),
    Sum.inr (Sum.inr (63, 3)),
    Sum.inr (Sum.inr (255, 3)),
    Sum.inr (Sum.inr (52, 12)),
    Sum.inr (Sum.inr (255, 20)),
    Sum.inr (Sum.inr (52, 10)),
    Sum.inr (Sum.inr (298, 12)),
    Sum.inr (Sum.inr (481, 3)),
    Sum.inr (Sum.inr (298, 10)),
    Sum.inr (Sum.inr (481, 20)),
    Sum.inr (Sum.inr (289, 12)),
    Sum.inr (Sum.inr (490, 3)),
    Sum.inr (Sum.inr (289, 10)),
    Sum.inr (Sum.inr (490, 20)),
    Sum.inr (Sum.inr (244, 3)),
    Sum.inr (Sum.inr (63, 12)),
    Sum.inr (Sum.inr (244, 20)),
    Sum.inr (Sum.inr (63, 10)),
    Sum.inr (Sum.inr (181, 20)),
    Sum.inr (Sum.inr (126, 10)),
    Sum.inr (Sum.inr (181, 3)),
    Sum.inr (Sum.inr (126, 12)),
    Sum.inr (Sum.inr (352, 10)),
    Sum.inr (Sum.inr (427, 20)),
    Sum.inr (Sum.inr (352, 12)),
    Sum.inr (Sum.inr (427, 3)),
    Sum.inr (Sum.inr (363, 10)),
    Sum.inr (Sum.inr (416, 20)),
    Sum.inr (Sum.inr (363, 12)),
    Sum.inr (Sum.inr (416, 3)),
    Sum.inr (Sum.inr (190, 20)),
    Sum.inr (Sum.inr (117, 10)),
    Sum.inr (Sum.inr (190, 3)),
    Sum.inr (Sum.inr (117, 12)),
    Sum.inr (Sum.inr (181, 12)),
    Sum.inr (Sum.inr (126, 3)),
    Sum.inr (Sum.inr (181, 10)),
    Sum.inr (Sum.inr (126, 20)),
    Sum.inr (Sum.inr (352, 3)),
    Sum.inr (Sum.inr (427, 12)),
    Sum.inr (Sum.inr (352, 20)),
    Sum.inr (Sum.inr (427, 10)),
    Sum.inr (Sum.inr (363, 3)),
    Sum.inr (Sum.inr (416, 12)),
    Sum.inr (Sum.inr (363, 20)),
    Sum.inr (Sum.inr (416, 10)),
    Sum.inr (Sum.inr (190, 12)),
    Sum.inr (Sum.inr (117, 3)),
    Sum.inr (Sum.inr (190, 10)),
    Sum.inr (Sum.inr (117, 20)),
    Sum.inr (Sum.inr (497, 10)),
    Sum.inr (Sum.inr (36, 3)),
    Sum.inr (Sum.inr (506, 10)),
    Sum.inr (Sum.inr (47, 3)),
    Sum.inr (Sum.inr (239, 10)),
    Sum.inr (Sum.inr (314, 3)),
    Sum.inr (Sum.inr (228, 10)),
    Sum.inr (Sum.inr (305, 3)),
    Sum.inr (Sum.inr (110, 10)),
    Sum.inr (Sum.inr (443, 3)),
    Sum.inr (Sum.inr (101, 10)),
    Sum.inr (Sum.inr (432, 3)),
    Sum.inr (Sum.inr (368, 10)),
    Sum.inr (Sum.inr (165, 3)),
    Sum.inr (Sum.inr (379, 10)),
    Sum.inr (Sum.inr (174, 3)),
    Sum.inr (Sum.inr (174, 10)),
    Sum.inr (Sum.inr (379, 3)),
    Sum.inr (Sum.inr (165, 10)),
    Sum.inr (Sum.inr (368, 3)),
    Sum.inr (Sum.inr (432, 10)),
    Sum.inr (Sum.inr (101, 3)),
    Sum.inr (Sum.inr (443, 10)),
    Sum.inr (Sum.inr (110, 3))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock044Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨11264 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block044_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock044Input a
    let y := generatedSixthXiShortBlock044Output a
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
theorem generatedSixth_xi_short_block044_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock044Input a
    let y := generatedSixthXiShortBlock044Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block044_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block044_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock044Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block044_certificate a).1
    (generatedSixth_xi_short_block044_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
