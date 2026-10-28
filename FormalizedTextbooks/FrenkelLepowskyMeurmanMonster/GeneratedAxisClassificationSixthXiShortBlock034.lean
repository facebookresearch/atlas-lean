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
def generatedSixthXiShortBlock034Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (218, 5)),
    Sum.inr (Sum.inl (42, 59)),
    Sum.inr (Sum.inl (218, 37)),
    Sum.inr (Sum.inl (42, 57)),
    Sum.inr (Sum.inl (184, 1)),
    Sum.inr (Sum.inl (194, 63)),
    Sum.inr (Sum.inl (184, 58)),
    Sum.inr (Sum.inl (194, 51)),
    Sum.inr (Sum.inl (74, 14)),
    Sum.inr (Sum.inl (106, 49)),
    Sum.inr (Sum.inl (74, 47)),
    Sum.inr (Sum.inl (106, 1)),
    Sum.inr (Sum.inl (117, 38)),
    Sum.inr (Sum.inl (127, 7)),
    Sum.inr (Sum.inl (117, 62)),
    Sum.inr (Sum.inl (127, 5)),
    Sum.inr (Sum.inl (117, 37)),
    Sum.inr (Sum.inl (127, 11)),
    Sum.inr (Sum.inl (117, 61)),
    Sum.inr (Sum.inl (127, 9)),
    Sum.inr (Sum.inl (74, 28)),
    Sum.inr (Sum.inl (106, 51)),
    Sum.inr (Sum.inl (74, 61)),
    Sum.inr (Sum.inl (106, 3)),
    Sum.inr (Sum.inl (106, 52)),
    Sum.inr (Sum.inl (74, 57)),
    Sum.inr (Sum.inl (106, 4)),
    Sum.inr (Sum.inl (74, 24)),
    Sum.inr (Sum.inl (127, 22)),
    Sum.inr (Sum.inl (117, 57)),
    Sum.inr (Sum.inl (127, 20)),
    Sum.inr (Sum.inl (117, 33)),
    Sum.inr (Sum.inl (127, 26)),
    Sum.inr (Sum.inl (117, 58)),
    Sum.inr (Sum.inl (127, 24)),
    Sum.inr (Sum.inl (117, 34)),
    Sum.inr (Sum.inl (106, 54)),
    Sum.inr (Sum.inl (74, 43)),
    Sum.inr (Sum.inl (106, 6)),
    Sum.inr (Sum.inl (74, 10)),
    Sum.inr (Sum.inr (62, 3)),
    Sum.inr (Sum.inr (491, 20)),
    Sum.inr (Sum.inr (480, 20)),
    Sum.inr (Sum.inr (53, 3)),
    Sum.inr (Sum.inr (245, 20)),
    Sum.inr (Sum.inr (288, 3)),
    Sum.inr (Sum.inr (299, 3)),
    Sum.inr (Sum.inr (254, 20)),
    Sum.inr (Sum.inr (62, 12)),
    Sum.inr (Sum.inr (491, 10)),
    Sum.inr (Sum.inr (480, 10)),
    Sum.inr (Sum.inr (53, 12)),
    Sum.inr (Sum.inr (245, 10)),
    Sum.inr (Sum.inr (288, 12)),
    Sum.inr (Sum.inr (299, 12)),
    Sum.inr (Sum.inr (254, 10)),
    Sum.inr (Sum.inr (62, 10)),
    Sum.inr (Sum.inr (491, 12)),
    Sum.inr (Sum.inr (480, 12)),
    Sum.inr (Sum.inr (53, 10)),
    Sum.inr (Sum.inr (245, 12)),
    Sum.inr (Sum.inr (288, 10)),
    Sum.inr (Sum.inr (299, 10)),
    Sum.inr (Sum.inr (254, 12)),
    Sum.inr (Sum.inr (62, 20)),
    Sum.inr (Sum.inr (491, 3)),
    Sum.inr (Sum.inr (480, 3)),
    Sum.inr (Sum.inr (53, 20)),
    Sum.inr (Sum.inr (245, 3)),
    Sum.inr (Sum.inr (288, 20)),
    Sum.inr (Sum.inr (299, 20)),
    Sum.inr (Sum.inr (254, 3)),
    Sum.inr (Sum.inr (180, 20)),
    Sum.inr (Sum.inr (353, 3)),
    Sum.inr (Sum.inr (362, 3)),
    Sum.inr (Sum.inr (191, 20)),
    Sum.inr (Sum.inr (127, 3)),
    Sum.inr (Sum.inr (426, 20)),
    Sum.inr (Sum.inr (417, 20)),
    Sum.inr (Sum.inr (116, 3)),
    Sum.inr (Sum.inr (180, 10)),
    Sum.inr (Sum.inr (353, 12)),
    Sum.inr (Sum.inr (362, 12)),
    Sum.inr (Sum.inr (191, 10)),
    Sum.inr (Sum.inr (127, 12)),
    Sum.inr (Sum.inr (426, 10)),
    Sum.inr (Sum.inr (417, 10)),
    Sum.inr (Sum.inr (116, 12)),
    Sum.inr (Sum.inr (180, 12)),
    Sum.inr (Sum.inr (353, 10)),
    Sum.inr (Sum.inr (362, 10)),
    Sum.inr (Sum.inr (191, 12)),
    Sum.inr (Sum.inr (127, 10)),
    Sum.inr (Sum.inr (426, 12)),
    Sum.inr (Sum.inr (417, 12)),
    Sum.inr (Sum.inr (116, 10)),
    Sum.inr (Sum.inr (180, 3)),
    Sum.inr (Sum.inr (353, 20)),
    Sum.inr (Sum.inr (362, 20)),
    Sum.inr (Sum.inr (191, 3)),
    Sum.inr (Sum.inr (127, 20)),
    Sum.inr (Sum.inr (426, 3)),
    Sum.inr (Sum.inr (417, 3)),
    Sum.inr (Sum.inr (116, 20)),
    Sum.inr (Sum.inl (222, 59)),
    Sum.inr (Sum.inl (163, 48)),
    Sum.inr (Sum.inl (222, 19)),
    Sum.inr (Sum.inl (163, 11)),
    Sum.inr (Sum.inl (60, 47)),
    Sum.inr (Sum.inl (202, 47)),
    Sum.inr (Sum.inl (60, 45)),
    Sum.inr (Sum.inl (202, 15)),
    Sum.inr (Sum.inl (60, 35)),
    Sum.inr (Sum.inl (202, 35)),
    Sum.inr (Sum.inl (60, 33)),
    Sum.inr (Sum.inl (202, 3)),
    Sum.inr (Sum.inl (222, 57)),
    Sum.inr (Sum.inl (163, 56)),
    Sum.inr (Sum.inl (222, 17)),
    Sum.inr (Sum.inl (163, 3)),
    Sum.inr (Sum.inl (56, 63)),
    Sum.inr (Sum.inl (116, 31)),
    Sum.inr (Sum.inl (56, 30)),
    Sum.inr (Sum.inl (116, 19)),
    Sum.inr (Sum.inl (105, 63)),
    Sum.inr (Sum.inl (129, 31)),
    Sum.inr (Sum.inl (105, 43)),
    Sum.inr (Sum.inl (129, 29)),
    Sum.inr (Sum.inl (105, 60)),
    Sum.inr (Sum.inl (129, 19)),
    Sum.inr (Sum.inl (105, 40)),
    Sum.inr (Sum.inl (129, 17)),
    Sum.inr (Sum.inl (56, 45)),
    Sum.inr (Sum.inl (116, 29)),
    Sum.inr (Sum.inl (56, 12)),
    Sum.inr (Sum.inl (116, 17)),
    Sum.inr (Sum.inl (163, 17)),
    Sum.inr (Sum.inl (222, 20)),
    Sum.inr (Sum.inl (163, 42)),
    Sum.inr (Sum.inl (222, 60)),
    Sum.inr (Sum.inl (202, 17)),
    Sum.inr (Sum.inl (60, 48)),
    Sum.inr (Sum.inl (202, 49)),
    Sum.inr (Sum.inl (60, 50)),
    Sum.inr (Sum.inl (202, 29)),
    Sum.inr (Sum.inl (60, 60)),
    Sum.inr (Sum.inl (202, 61)),
    Sum.inr (Sum.inl (60, 62)),
    Sum.inr (Sum.inl (163, 25)),
    Sum.inr (Sum.inl (222, 22)),
    Sum.inr (Sum.inl (163, 34)),
    Sum.inr (Sum.inl (222, 62)),
    Sum.inr (Sum.inl (116, 62)),
    Sum.inr (Sum.inl (56, 4)),
    Sum.inr (Sum.inl (116, 50)),
    Sum.inr (Sum.inl (56, 37)),
    Sum.inr (Sum.inl (129, 62)),
    Sum.inr (Sum.inl (105, 8)),
    Sum.inr (Sum.inl (129, 60)),
    Sum.inr (Sum.inl (105, 28)),
    Sum.inr (Sum.inl (129, 50)),
    Sum.inr (Sum.inl (105, 11)),
    Sum.inr (Sum.inl (129, 48)),
    Sum.inr (Sum.inl (105, 31)),
    Sum.inr (Sum.inl (116, 60)),
    Sum.inr (Sum.inl (56, 22)),
    Sum.inr (Sum.inl (116, 48)),
    Sum.inr (Sum.inl (56, 55)),
    Sum.inr (Sum.inl (164, 24)),
    Sum.inr (Sum.inl (201, 60)),
    Sum.inr (Sum.inl (164, 20)),
    Sum.inr (Sum.inl (201, 52)),
    Sum.inr (Sum.inl (90, 10)),
    Sum.inr (Sum.inl (75, 42)),
    Sum.inr (Sum.inl (90, 8)),
    Sum.inr (Sum.inl (75, 38)),
    Sum.inr (Sum.inl (201, 24)),
    Sum.inr (Sum.inl (164, 56)),
    Sum.inr (Sum.inl (201, 16)),
    Sum.inr (Sum.inl (164, 52)),
    Sum.inr (Sum.inl (75, 40)),
    Sum.inr (Sum.inl (90, 37)),
    Sum.inr (Sum.inl (75, 36)),
    Sum.inr (Sum.inl (90, 39)),
    Sum.inr (Sum.inl (90, 46)),
    Sum.inr (Sum.inl (75, 5)),
    Sum.inr (Sum.inl (90, 44)),
    Sum.inr (Sum.inl (75, 9)),
    Sum.inr (Sum.inl (164, 38)),
    Sum.inr (Sum.inl (201, 2)),
    Sum.inr (Sum.inl (164, 42)),
    Sum.inr (Sum.inl (201, 10)),
    Sum.inr (Sum.inl (75, 7)),
    Sum.inr (Sum.inl (90, 1)),
    Sum.inr (Sum.inl (75, 11)),
    Sum.inr (Sum.inl (90, 3)),
    Sum.inr (Sum.inl (201, 38)),
    Sum.inr (Sum.inl (164, 6)),
    Sum.inr (Sum.inl (201, 46)),
    Sum.inr (Sum.inl (164, 10)),
    Sum.inr (Sum.inl (217, 2)),
    Sum.inr (Sum.inl (43, 26)),
    Sum.inr (Sum.inl (217, 16)),
    Sum.inr (Sum.inl (43, 22)),
    Sum.inr (Sum.inl (115, 61)),
    Sum.inr (Sum.inl (130, 52)),
    Sum.inr (Sum.inl (115, 62)),
    Sum.inr (Sum.inl (130, 54)),
    Sum.inr (Sum.inl (43, 8)),
    Sum.inr (Sum.inl (217, 38)),
    Sum.inr (Sum.inl (43, 4)),
    Sum.inr (Sum.inl (217, 52)),
    Sum.inr (Sum.inl (130, 61)),
    Sum.inr (Sum.inl (115, 53)),
    Sum.inr (Sum.inl (130, 63)),
    Sum.inr (Sum.inl (115, 54)),
    Sum.inr (Sum.inl (115, 41)),
    Sum.inr (Sum.inl (130, 32)),
    Sum.inr (Sum.inl (115, 42)),
    Sum.inr (Sum.inl (130, 34)),
    Sum.inr (Sum.inl (217, 60)),
    Sum.inr (Sum.inl (43, 36)),
    Sum.inr (Sum.inl (217, 46)),
    Sum.inr (Sum.inl (43, 40)),
    Sum.inr (Sum.inl (130, 41)),
    Sum.inr (Sum.inl (115, 33)),
    Sum.inr (Sum.inl (130, 43)),
    Sum.inr (Sum.inl (115, 34)),
    Sum.inr (Sum.inl (43, 54)),
    Sum.inr (Sum.inl (217, 24)),
    Sum.inr (Sum.inl (43, 58)),
    Sum.inr (Sum.inl (217, 10)),
    Sum.inr (Sum.inl (89, 47)),
    Sum.inr (Sum.inl (113, 48)),
    Sum.inr (Sum.inl (61, 13)),
    Sum.inr (Sum.inl (193, 7)),
    Sum.inr (Sum.inl (221, 63)),
    Sum.inr (Sum.inl (185, 31)),
    Sum.inr (Sum.inl (57, 45)),
    Sum.inr (Sum.inl (131, 13)),
    Sum.inr (Sum.inl (89, 13)),
    Sum.inr (Sum.inl (113, 11)),
    Sum.inr (Sum.inl (61, 9)),
    Sum.inr (Sum.inl (193, 3)),
    Sum.inr (Sum.inl (221, 29)),
    Sum.inr (Sum.inl (185, 13)),
    Sum.inr (Sum.inl (57, 12)),
    Sum.inr (Sum.inl (131, 5)),
    Sum.inr (Sum.inl (61, 31)),
    Sum.inr (Sum.inl (193, 31)),
    Sum.inr (Sum.inl (89, 43)),
    Sum.inr (Sum.inl (113, 56)),
    Sum.inr (Sum.inl (57, 63)),
    Sum.inr (Sum.inl (131, 31)),
    Sum.inr (Sum.inl (221, 43)),
    Sum.inr (Sum.inl (185, 23))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock034Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨8704 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block034_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock034Input a
    let y := generatedSixthXiShortBlock034Output a
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
theorem generatedSixth_xi_short_block034_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock034Input a
    let y := generatedSixthXiShortBlock034Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block034_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block034_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock034Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block034_certificate a).1
    (generatedSixth_xi_short_block034_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
