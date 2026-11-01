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
def generatedSixthXiShortBlock038Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (313, 14)),
    Sum.inr (Sum.inr (166, 2)),
    Sum.inr (Sum.inr (306, 14)),
    Sum.inr (Sum.inr (173, 2)),
    Sum.inr (Sum.inr (166, 9)),
    Sum.inr (Sum.inr (313, 21)),
    Sum.inr (Sum.inr (173, 9)),
    Sum.inr (Sum.inr (306, 21)),
    Sum.inr (Sum.inr (173, 14)),
    Sum.inr (Sum.inr (306, 2)),
    Sum.inr (Sum.inr (166, 14)),
    Sum.inr (Sum.inr (313, 2)),
    Sum.inr (Sum.inr (306, 9)),
    Sum.inr (Sum.inr (173, 21)),
    Sum.inr (Sum.inr (313, 9)),
    Sum.inr (Sum.inr (166, 21)),
    Sum.inr (Sum.inr (376, 14)),
    Sum.inr (Sum.inr (231, 2)),
    Sum.inr (Sum.inr (371, 14)),
    Sum.inr (Sum.inr (236, 2)),
    Sum.inr (Sum.inr (231, 9)),
    Sum.inr (Sum.inr (376, 21)),
    Sum.inr (Sum.inr (236, 9)),
    Sum.inr (Sum.inr (371, 21)),
    Sum.inr (Sum.inr (435, 14)),
    Sum.inr (Sum.inr (44, 2)),
    Sum.inr (Sum.inr (440, 14)),
    Sum.inr (Sum.inr (39, 2)),
    Sum.inr (Sum.inr (44, 9)),
    Sum.inr (Sum.inr (435, 21)),
    Sum.inr (Sum.inr (39, 9)),
    Sum.inr (Sum.inr (440, 21)),
    Sum.inr (Sum.inr (102, 14)),
    Sum.inr (Sum.inr (505, 2)),
    Sum.inr (Sum.inr (109, 14)),
    Sum.inr (Sum.inr (498, 2)),
    Sum.inr (Sum.inr (505, 9)),
    Sum.inr (Sum.inr (102, 21)),
    Sum.inr (Sum.inr (498, 9)),
    Sum.inr (Sum.inr (109, 21)),
    Sum.inr (Sum.inr (189, 9)),
    Sum.inr (Sum.inr (125, 21)),
    Sum.inr (Sum.inr (189, 14)),
    Sum.inr (Sum.inr (125, 2)),
    Sum.inr (Sum.inr (290, 21)),
    Sum.inr (Sum.inr (482, 9)),
    Sum.inr (Sum.inr (290, 2)),
    Sum.inr (Sum.inr (482, 14)),
    Sum.inr (Sum.inr (297, 21)),
    Sum.inr (Sum.inr (489, 9)),
    Sum.inr (Sum.inr (297, 2)),
    Sum.inr (Sum.inr (489, 14)),
    Sum.inr (Sum.inr (182, 9)),
    Sum.inr (Sum.inr (118, 21)),
    Sum.inr (Sum.inr (182, 14)),
    Sum.inr (Sum.inr (118, 2)),
    Sum.inr (Sum.inr (247, 21)),
    Sum.inr (Sum.inr (55, 9)),
    Sum.inr (Sum.inr (247, 2)),
    Sum.inr (Sum.inr (55, 14)),
    Sum.inr (Sum.inr (360, 9)),
    Sum.inr (Sum.inr (424, 21)),
    Sum.inr (Sum.inr (360, 14)),
    Sum.inr (Sum.inr (424, 2)),
    Sum.inr (Sum.inr (355, 9)),
    Sum.inr (Sum.inr (419, 21)),
    Sum.inr (Sum.inr (355, 14)),
    Sum.inr (Sum.inr (419, 2)),
    Sum.inr (Sum.inr (252, 21)),
    Sum.inr (Sum.inr (60, 9)),
    Sum.inr (Sum.inr (252, 2)),
    Sum.inr (Sum.inr (60, 14)),
    Sum.inr (Sum.inr (189, 2)),
    Sum.inr (Sum.inr (125, 14)),
    Sum.inr (Sum.inr (189, 21)),
    Sum.inr (Sum.inr (125, 9)),
    Sum.inr (Sum.inr (290, 14)),
    Sum.inr (Sum.inr (482, 2)),
    Sum.inr (Sum.inr (290, 9)),
    Sum.inr (Sum.inr (482, 21)),
    Sum.inr (Sum.inr (297, 14)),
    Sum.inr (Sum.inr (489, 2)),
    Sum.inr (Sum.inr (297, 9)),
    Sum.inr (Sum.inr (489, 21)),
    Sum.inr (Sum.inr (182, 2)),
    Sum.inr (Sum.inr (118, 14)),
    Sum.inr (Sum.inr (182, 21)),
    Sum.inr (Sum.inr (118, 9)),
    Sum.inr (Sum.inr (247, 14)),
    Sum.inr (Sum.inr (55, 2)),
    Sum.inr (Sum.inr (247, 9)),
    Sum.inr (Sum.inr (55, 21)),
    Sum.inr (Sum.inr (360, 2)),
    Sum.inr (Sum.inr (424, 14)),
    Sum.inr (Sum.inr (360, 21)),
    Sum.inr (Sum.inr (424, 9)),
    Sum.inr (Sum.inr (355, 2)),
    Sum.inr (Sum.inr (419, 14)),
    Sum.inr (Sum.inr (355, 21)),
    Sum.inr (Sum.inr (419, 9)),
    Sum.inr (Sum.inr (252, 14)),
    Sum.inr (Sum.inr (60, 2)),
    Sum.inr (Sum.inr (252, 9)),
    Sum.inr (Sum.inr (60, 21)),
    Sum.inr (Sum.inl (145, 59)),
    Sum.inl 85,
    Sum.inr (Sum.inl (145, 47)),
    Sum.inl 47,
    Sum.inr (Sum.inl (145, 41)),
    Sum.inl 60,
    Sum.inr (Sum.inl (145, 43)),
    Sum.inl 70,
    Sum.inl 415,
    Sum.inr (Sum.inl (145, 36)),
    Sum.inl 107,
    Sum.inr (Sum.inl (145, 48)),
    Sum.inl 344,
    Sum.inr (Sum.inl (145, 54)),
    Sum.inl 400,
    Sum.inr (Sum.inl (145, 52)),
    Sum.inr (Sum.inl (145, 61)),
    Sum.inl 71,
    Sum.inr (Sum.inl (145, 63)),
    Sum.inl 61,
    Sum.inr (Sum.inl (145, 57)),
    Sum.inl 46,
    Sum.inr (Sum.inl (145, 45)),
    Sum.inl 84,
    Sum.inl 401,
    Sum.inr (Sum.inl (145, 34)),
    Sum.inl 345,
    Sum.inr (Sum.inl (145, 32)),
    Sum.inl 106,
    Sum.inr (Sum.inl (145, 38)),
    Sum.inl 414,
    Sum.inr (Sum.inl (145, 50)),
    Sum.inl 491,
    Sum.inr (Sum.inl (145, 12)),
    Sum.inl 115,
    Sum.inr (Sum.inl (145, 24)),
    Sum.inl 352,
    Sum.inr (Sum.inl (145, 30)),
    Sum.inl 462,
    Sum.inr (Sum.inl (145, 28)),
    Sum.inr (Sum.inl (145, 5)),
    Sum.inl 547,
    Sum.inr (Sum.inl (145, 17)),
    Sum.inl 129,
    Sum.inr (Sum.inl (145, 23)),
    Sum.inl 366,
    Sum.inr (Sum.inl (145, 21)),
    Sum.inl 476,
    Sum.inl 463,
    Sum.inr (Sum.inl (145, 10)),
    Sum.inl 353,
    Sum.inr (Sum.inl (145, 8)),
    Sum.inl 114,
    Sum.inr (Sum.inl (145, 14)),
    Sum.inl 490,
    Sum.inr (Sum.inl (145, 26)),
    Sum.inr (Sum.inl (145, 3)),
    Sum.inl 477,
    Sum.inr (Sum.inl (145, 1)),
    Sum.inl 367,
    Sum.inr (Sum.inl (145, 7)),
    Sum.inl 128,
    Sum.inr (Sum.inl (145, 19)),
    Sum.inl 546,
    Sum.inr (Sum.inl (146, 24)),
    Sum.inl 41,
    Sum.inr (Sum.inl (146, 48)),
    Sum.inl 3,
    Sum.inl 337,
    Sum.inr (Sum.inl (146, 55)),
    Sum.inl 101,
    Sum.inr (Sum.inl (146, 31)),
    Sum.inr (Sum.inl (146, 58)),
    Sum.inl 16,
    Sum.inr (Sum.inl (146, 56)),
    Sum.inl 26,
    Sum.inl 312,
    Sum.inr (Sum.inl (146, 21)),
    Sum.inl 322,
    Sum.inr (Sum.inl (146, 23)),
    Sum.inl 456,
    Sum.inr (Sum.inl (146, 35)),
    Sum.inl 110,
    Sum.inr (Sum.inl (146, 11)),
    Sum.inr (Sum.inl (146, 38)),
    Sum.inl 548,
    Sum.inr (Sum.inl (146, 14)),
    Sum.inl 130,
    Sum.inl 349,
    Sum.inr (Sum.inl (146, 1)),
    Sum.inl 443,
    Sum.inr (Sum.inl (146, 3)),
    Sum.inr (Sum.inl (146, 4)),
    Sum.inl 369,
    Sum.inr (Sum.inl (146, 6)),
    Sum.inl 479,
    Sum.inr (Sum.inl (146, 18)),
    Sum.inl 27,
    Sum.inr (Sum.inl (146, 16)),
    Sum.inl 17,
    Sum.inl 323,
    Sum.inr (Sum.inl (146, 61)),
    Sum.inl 313,
    Sum.inr (Sum.inl (146, 63)),
    Sum.inr (Sum.inl (146, 26)),
    Sum.inl 2,
    Sum.inr (Sum.inl (146, 50)),
    Sum.inl 40,
    Sum.inl 100,
    Sum.inr (Sum.inl (146, 53)),
    Sum.inl 336,
    Sum.inr (Sum.inl (146, 29)),
    Sum.inl 442,
    Sum.inr (Sum.inl (146, 41)),
    Sum.inl 348,
    Sum.inr (Sum.inl (146, 43)),
    Sum.inr (Sum.inl (146, 44)),
    Sum.inl 478,
    Sum.inr (Sum.inl (146, 46)),
    Sum.inl 368,
    Sum.inl 111,
    Sum.inr (Sum.inl (146, 33)),
    Sum.inl 457,
    Sum.inr (Sum.inl (146, 9)),
    Sum.inr (Sum.inl (146, 36)),
    Sum.inl 131,
    Sum.inr (Sum.inl (146, 12)),
    Sum.inl 549,
    Sum.inr (Sum.inr (255, 14)),
    Sum.inr (Sum.inr (126, 21)),
    Sum.inr (Sum.inr (255, 9)),
    Sum.inr (Sum.inr (126, 2)),
    Sum.inr (Sum.inr (352, 21)),
    Sum.inr (Sum.inr (481, 14)),
    Sum.inr (Sum.inr (352, 2)),
    Sum.inr (Sum.inr (481, 9)),
    Sum.inr (Sum.inr (363, 21)),
    Sum.inr (Sum.inr (490, 14)),
    Sum.inr (Sum.inr (363, 2)),
    Sum.inr (Sum.inr (490, 9)),
    Sum.inr (Sum.inr (244, 14)),
    Sum.inr (Sum.inr (117, 21)),
    Sum.inr (Sum.inr (244, 9)),
    Sum.inr (Sum.inr (117, 2)),
    Sum.inr (Sum.inr (255, 2)),
    Sum.inr (Sum.inr (126, 9)),
    Sum.inr (Sum.inr (255, 21)),
    Sum.inr (Sum.inr (126, 14)),
    Sum.inr (Sum.inr (352, 9)),
    Sum.inr (Sum.inr (481, 2)),
    Sum.inr (Sum.inr (352, 14)),
    Sum.inr (Sum.inr (481, 21))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock038Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨9728 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block038_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock038Input a
    let y := generatedSixthXiShortBlock038Output a
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
theorem generatedSixth_xi_short_block038_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock038Input a
    let y := generatedSixthXiShortBlock038Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block038_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block038_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock038Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block038_certificate a).1
    (generatedSixth_xi_short_block038_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
