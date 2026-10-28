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
def generatedSixthXiShortBlock043Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (222, 58)),
    Sum.inr (Sum.inl (202, 41)),
    Sum.inr (Sum.inl (105, 30)),
    Sum.inr (Sum.inl (116, 15)),
    Sum.inr (Sum.inl (60, 40)),
    Sum.inr (Sum.inl (163, 9)),
    Sum.inr (Sum.inl (56, 6)),
    Sum.inr (Sum.inl (129, 9)),
    Sum.inr (Sum.inl (116, 3)),
    Sum.inr (Sum.inl (105, 10)),
    Sum.inr (Sum.inl (202, 9)),
    Sum.inr (Sum.inl (222, 18)),
    Sum.inr (Sum.inl (129, 11)),
    Sum.inr (Sum.inl (56, 39)),
    Sum.inr (Sum.inl (163, 50)),
    Sum.inr (Sum.inl (60, 42)),
    Sum.inr (Sum.inl (116, 1)),
    Sum.inr (Sum.inl (105, 9)),
    Sum.inr (Sum.inl (202, 5)),
    Sum.inr (Sum.inl (222, 16)),
    Sum.inr (Sum.inl (129, 7)),
    Sum.inr (Sum.inl (56, 53)),
    Sum.inr (Sum.inl (163, 58)),
    Sum.inr (Sum.inl (60, 38)),
    Sum.inr (Sum.inl (202, 27)),
    Sum.inr (Sum.inl (222, 23)),
    Sum.inr (Sum.inl (116, 44)),
    Sum.inr (Sum.inl (105, 42)),
    Sum.inr (Sum.inl (163, 32)),
    Sum.inr (Sum.inl (60, 59)),
    Sum.inr (Sum.inl (129, 36)),
    Sum.inr (Sum.inl (56, 47)),
    Sum.inr (Sum.inl (202, 23)),
    Sum.inr (Sum.inl (222, 21)),
    Sum.inr (Sum.inl (116, 46)),
    Sum.inr (Sum.inl (105, 41)),
    Sum.inr (Sum.inl (163, 40)),
    Sum.inr (Sum.inl (60, 55)),
    Sum.inr (Sum.inl (129, 40)),
    Sum.inr (Sum.inl (56, 61)),
    Sum.inr (Sum.inl (130, 17)),
    Sum.inr (Sum.inl (217, 59)),
    Sum.inr (Sum.inl (90, 48)),
    Sum.inr (Sum.inl (201, 59)),
    Sum.inr (Sum.inl (115, 24)),
    Sum.inr (Sum.inl (43, 61)),
    Sum.inr (Sum.inl (75, 61)),
    Sum.inr (Sum.inl (164, 31)),
    Sum.inr (Sum.inl (115, 27)),
    Sum.inr (Sum.inl (43, 49)),
    Sum.inr (Sum.inl (75, 49)),
    Sum.inr (Sum.inl (164, 19)),
    Sum.inr (Sum.inl (130, 19)),
    Sum.inr (Sum.inl (217, 41)),
    Sum.inr (Sum.inl (90, 50)),
    Sum.inr (Sum.inl (201, 51)),
    Sum.inr (Sum.inl (90, 57)),
    Sum.inr (Sum.inl (201, 41)),
    Sum.inr (Sum.inl (130, 14)),
    Sum.inr (Sum.inl (217, 51)),
    Sum.inr (Sum.inl (75, 28)),
    Sum.inr (Sum.inl (164, 13)),
    Sum.inr (Sum.inl (115, 7)),
    Sum.inr (Sum.inl (43, 29)),
    Sum.inr (Sum.inl (75, 16)),
    Sum.inr (Sum.inl (164, 1)),
    Sum.inr (Sum.inl (115, 4)),
    Sum.inr (Sum.inl (43, 17)),
    Sum.inr (Sum.inl (90, 59)),
    Sum.inr (Sum.inl (201, 33)),
    Sum.inr (Sum.inl (130, 12)),
    Sum.inr (Sum.inl (217, 33)),
    Sum.inr (Sum.inl (130, 24)),
    Sum.inr (Sum.inl (217, 31)),
    Sum.inr (Sum.inl (90, 31)),
    Sum.inr (Sum.inl (201, 31)),
    Sum.inr (Sum.inl (115, 16)),
    Sum.inr (Sum.inl (43, 47)),
    Sum.inr (Sum.inl (75, 63)),
    Sum.inr (Sum.inl (164, 63)),
    Sum.inr (Sum.inl (115, 19)),
    Sum.inr (Sum.inl (43, 35)),
    Sum.inr (Sum.inl (75, 51)),
    Sum.inr (Sum.inl (164, 51)),
    Sum.inr (Sum.inl (130, 26)),
    Sum.inr (Sum.inl (217, 13)),
    Sum.inr (Sum.inl (90, 29)),
    Sum.inr (Sum.inl (201, 23)),
    Sum.inr (Sum.inl (90, 22)),
    Sum.inr (Sum.inl (201, 13)),
    Sum.inr (Sum.inl (130, 7)),
    Sum.inr (Sum.inl (217, 23)),
    Sum.inr (Sum.inl (75, 30)),
    Sum.inr (Sum.inl (164, 45)),
    Sum.inr (Sum.inl (115, 15)),
    Sum.inr (Sum.inl (43, 15)),
    Sum.inr (Sum.inl (75, 18)),
    Sum.inr (Sum.inl (164, 33)),
    Sum.inr (Sum.inl (115, 12)),
    Sum.inr (Sum.inl (43, 3)),
    Sum.inr (Sum.inl (90, 20)),
    Sum.inr (Sum.inl (201, 5)),
    Sum.inr (Sum.inl (130, 5)),
    Sum.inr (Sum.inl (217, 5)),
    Sum.inr (Sum.inr (137, 20)),
    Sum.inr (Sum.inr (3, 12)),
    Sum.inr (Sum.inr (137, 10)),
    Sum.inr (Sum.inr (3, 3)),
    Sum.inr (Sum.inr (343, 12)),
    Sum.inr (Sum.inr (477, 20)),
    Sum.inr (Sum.inr (343, 3)),
    Sum.inr (Sum.inr (477, 10)),
    Sum.inr (Sum.inr (348, 12)),
    Sum.inr (Sum.inr (470, 20)),
    Sum.inr (Sum.inr (348, 3)),
    Sum.inr (Sum.inr (470, 10)),
    Sum.inr (Sum.inr (130, 20)),
    Sum.inr (Sum.inr (8, 12)),
    Sum.inr (Sum.inr (130, 10)),
    Sum.inr (Sum.inr (8, 3)),
    Sum.inr (Sum.inr (66, 12)),
    Sum.inr (Sum.inr (200, 20)),
    Sum.inr (Sum.inr (66, 3)),
    Sum.inr (Sum.inr (200, 10)),
    Sum.inr (Sum.inr (412, 20)),
    Sum.inr (Sum.inr (278, 12)),
    Sum.inr (Sum.inr (412, 10)),
    Sum.inr (Sum.inr (278, 3)),
    Sum.inr (Sum.inr (407, 20)),
    Sum.inr (Sum.inr (285, 12)),
    Sum.inr (Sum.inr (407, 10)),
    Sum.inr (Sum.inr (285, 3)),
    Sum.inr (Sum.inr (73, 12)),
    Sum.inr (Sum.inr (195, 20)),
    Sum.inr (Sum.inr (73, 3)),
    Sum.inr (Sum.inr (195, 10)),
    Sum.inr (Sum.inr (137, 3)),
    Sum.inr (Sum.inr (3, 10)),
    Sum.inr (Sum.inr (137, 12)),
    Sum.inr (Sum.inr (3, 20)),
    Sum.inr (Sum.inr (343, 10)),
    Sum.inr (Sum.inr (477, 3)),
    Sum.inr (Sum.inr (343, 20)),
    Sum.inr (Sum.inr (477, 12)),
    Sum.inr (Sum.inr (348, 10)),
    Sum.inr (Sum.inr (470, 3)),
    Sum.inr (Sum.inr (348, 20)),
    Sum.inr (Sum.inr (470, 12)),
    Sum.inr (Sum.inr (130, 3)),
    Sum.inr (Sum.inr (8, 10)),
    Sum.inr (Sum.inr (130, 12)),
    Sum.inr (Sum.inr (8, 20)),
    Sum.inr (Sum.inr (66, 10)),
    Sum.inr (Sum.inr (200, 3)),
    Sum.inr (Sum.inr (66, 20)),
    Sum.inr (Sum.inr (200, 12)),
    Sum.inr (Sum.inr (412, 3)),
    Sum.inr (Sum.inr (278, 10)),
    Sum.inr (Sum.inr (412, 12)),
    Sum.inr (Sum.inr (278, 20)),
    Sum.inr (Sum.inr (407, 3)),
    Sum.inr (Sum.inr (285, 10)),
    Sum.inr (Sum.inr (407, 12)),
    Sum.inr (Sum.inr (285, 20)),
    Sum.inr (Sum.inr (73, 10)),
    Sum.inr (Sum.inr (195, 3)),
    Sum.inr (Sum.inr (73, 20)),
    Sum.inr (Sum.inr (195, 12)),
    Sum.inr (Sum.inr (498, 12)),
    Sum.inr (Sum.inr (39, 3)),
    Sum.inr (Sum.inr (505, 12)),
    Sum.inr (Sum.inr (44, 3)),
    Sum.inr (Sum.inr (39, 10)),
    Sum.inr (Sum.inr (498, 20)),
    Sum.inr (Sum.inr (44, 10)),
    Sum.inr (Sum.inr (505, 20)),
    Sum.inr (Sum.inr (236, 12)),
    Sum.inr (Sum.inr (313, 3)),
    Sum.inr (Sum.inr (231, 12)),
    Sum.inr (Sum.inr (306, 3)),
    Sum.inr (Sum.inr (313, 10)),
    Sum.inr (Sum.inr (236, 20)),
    Sum.inr (Sum.inr (306, 10)),
    Sum.inr (Sum.inr (231, 20)),
    Sum.inr (Sum.inr (109, 12)),
    Sum.inr (Sum.inr (440, 3)),
    Sum.inr (Sum.inr (102, 12)),
    Sum.inr (Sum.inr (435, 3)),
    Sum.inr (Sum.inr (440, 10)),
    Sum.inr (Sum.inr (109, 20)),
    Sum.inr (Sum.inr (435, 10)),
    Sum.inr (Sum.inr (102, 20)),
    Sum.inr (Sum.inr (371, 12)),
    Sum.inr (Sum.inr (166, 3)),
    Sum.inr (Sum.inr (376, 12)),
    Sum.inr (Sum.inr (173, 3)),
    Sum.inr (Sum.inr (166, 10)),
    Sum.inr (Sum.inr (371, 20)),
    Sum.inr (Sum.inr (173, 10)),
    Sum.inr (Sum.inr (376, 20)),
    Sum.inr (Sum.inr (173, 12)),
    Sum.inr (Sum.inr (376, 3)),
    Sum.inr (Sum.inr (166, 12)),
    Sum.inr (Sum.inr (371, 3)),
    Sum.inr (Sum.inr (376, 10)),
    Sum.inr (Sum.inr (173, 20)),
    Sum.inr (Sum.inr (371, 10)),
    Sum.inr (Sum.inr (166, 20)),
    Sum.inr (Sum.inr (435, 12)),
    Sum.inr (Sum.inr (102, 3)),
    Sum.inr (Sum.inr (440, 12)),
    Sum.inr (Sum.inr (109, 3)),
    Sum.inr (Sum.inr (102, 10)),
    Sum.inr (Sum.inr (435, 20)),
    Sum.inr (Sum.inr (109, 10)),
    Sum.inr (Sum.inr (440, 20)),
    Sum.inr (Sum.inr (306, 12)),
    Sum.inr (Sum.inr (231, 3)),
    Sum.inr (Sum.inr (313, 12)),
    Sum.inr (Sum.inr (236, 3)),
    Sum.inr (Sum.inr (231, 10)),
    Sum.inr (Sum.inr (306, 20)),
    Sum.inr (Sum.inr (236, 10)),
    Sum.inr (Sum.inr (313, 20)),
    Sum.inr (Sum.inr (44, 12)),
    Sum.inr (Sum.inr (505, 3)),
    Sum.inr (Sum.inr (39, 12)),
    Sum.inr (Sum.inr (498, 3)),
    Sum.inr (Sum.inr (505, 10)),
    Sum.inr (Sum.inr (44, 20)),
    Sum.inr (Sum.inr (498, 10)),
    Sum.inr (Sum.inr (39, 20)),
    Sum.inr (Sum.inr (189, 12)),
    Sum.inr (Sum.inr (55, 20)),
    Sum.inr (Sum.inr (189, 10)),
    Sum.inr (Sum.inr (55, 3)),
    Sum.inr (Sum.inr (360, 20)),
    Sum.inr (Sum.inr (482, 12)),
    Sum.inr (Sum.inr (360, 3)),
    Sum.inr (Sum.inr (482, 10)),
    Sum.inr (Sum.inr (355, 20)),
    Sum.inr (Sum.inr (489, 12)),
    Sum.inr (Sum.inr (355, 3)),
    Sum.inr (Sum.inr (489, 10)),
    Sum.inr (Sum.inr (182, 12)),
    Sum.inr (Sum.inr (60, 20)),
    Sum.inr (Sum.inr (182, 10)),
    Sum.inr (Sum.inr (60, 3)),
    Sum.inr (Sum.inr (247, 20)),
    Sum.inr (Sum.inr (125, 12)),
    Sum.inr (Sum.inr (247, 3)),
    Sum.inr (Sum.inr (125, 10)),
    Sum.inr (Sum.inr (290, 12)),
    Sum.inr (Sum.inr (424, 20)),
    Sum.inr (Sum.inr (290, 10)),
    Sum.inr (Sum.inr (424, 3))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock043Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨11008 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block043_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock043Input a
    let y := generatedSixthXiShortBlock043Output a
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
theorem generatedSixth_xi_short_block043_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock043Input a
    let y := generatedSixthXiShortBlock043Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block043_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block043_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock043Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block043_certificate a).1
    (generatedSixth_xi_short_block043_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
