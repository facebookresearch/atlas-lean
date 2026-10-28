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
def generatedSixthXiShortBlock024Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (354, 11)),
    Sum.inr (Sum.inr (488, 1)),
    Sum.inr (Sum.inr (296, 11)),
    Sum.inr (Sum.inr (418, 1)),
    Sum.inr (Sum.inr (183, 11)),
    Sum.inr (Sum.inr (61, 1)),
    Sum.inr (Sum.inr (253, 11)),
    Sum.inr (Sum.inr (119, 1)),
    Sum.inr (Sum.inr (253, 15)),
    Sum.inr (Sum.inr (119, 22)),
    Sum.inr (Sum.inr (183, 15)),
    Sum.inr (Sum.inr (61, 22)),
    Sum.inr (Sum.inr (296, 15)),
    Sum.inr (Sum.inr (418, 22)),
    Sum.inr (Sum.inr (354, 15)),
    Sum.inr (Sum.inr (488, 22)),
    Sum.inr (Sum.inr (291, 15)),
    Sum.inr (Sum.inr (425, 22)),
    Sum.inr (Sum.inr (361, 15)),
    Sum.inr (Sum.inr (483, 22)),
    Sum.inr (Sum.inr (246, 15)),
    Sum.inr (Sum.inr (124, 22)),
    Sum.inr (Sum.inr (188, 15)),
    Sum.inr (Sum.inr (54, 22)),
    Sum.inr (Sum.inr (54, 15)),
    Sum.inr (Sum.inr (188, 22)),
    Sum.inr (Sum.inr (124, 15)),
    Sum.inr (Sum.inr (246, 22)),
    Sum.inr (Sum.inr (483, 15)),
    Sum.inr (Sum.inr (361, 22)),
    Sum.inr (Sum.inr (425, 15)),
    Sum.inr (Sum.inr (291, 22)),
    Sum.inr (Sum.inr (488, 15)),
    Sum.inr (Sum.inr (354, 22)),
    Sum.inr (Sum.inr (418, 15)),
    Sum.inr (Sum.inr (296, 22)),
    Sum.inr (Sum.inr (61, 15)),
    Sum.inr (Sum.inr (183, 22)),
    Sum.inr (Sum.inr (119, 15)),
    Sum.inr (Sum.inr (253, 22)),
    Sum.inr (Sum.inr (119, 13)),
    Sum.inr (Sum.inr (188, 0)),
    Sum.inr (Sum.inr (61, 13)),
    Sum.inr (Sum.inr (246, 0)),
    Sum.inr (Sum.inr (418, 13)),
    Sum.inr (Sum.inr (361, 0)),
    Sum.inr (Sum.inr (488, 13)),
    Sum.inr (Sum.inr (291, 0)),
    Sum.inr (Sum.inr (425, 13)),
    Sum.inr (Sum.inr (354, 0)),
    Sum.inr (Sum.inr (483, 13)),
    Sum.inr (Sum.inr (296, 0)),
    Sum.inr (Sum.inr (124, 13)),
    Sum.inr (Sum.inr (183, 0)),
    Sum.inr (Sum.inr (54, 13)),
    Sum.inr (Sum.inr (253, 0)),
    Sum.inr (Sum.inr (188, 8)),
    Sum.inr (Sum.inr (119, 23)),
    Sum.inr (Sum.inr (246, 8)),
    Sum.inr (Sum.inr (61, 23)),
    Sum.inr (Sum.inr (361, 8)),
    Sum.inr (Sum.inr (418, 23)),
    Sum.inr (Sum.inr (291, 8)),
    Sum.inr (Sum.inr (488, 23)),
    Sum.inr (Sum.inr (354, 8)),
    Sum.inr (Sum.inr (425, 23)),
    Sum.inr (Sum.inr (296, 8)),
    Sum.inr (Sum.inr (483, 23)),
    Sum.inr (Sum.inr (183, 8)),
    Sum.inr (Sum.inr (124, 23)),
    Sum.inr (Sum.inr (253, 8)),
    Sum.inr (Sum.inr (54, 23)),
    Sum.inr (Sum.inr (253, 13)),
    Sum.inr (Sum.inr (54, 0)),
    Sum.inr (Sum.inr (183, 13)),
    Sum.inr (Sum.inr (124, 0)),
    Sum.inr (Sum.inr (296, 13)),
    Sum.inr (Sum.inr (483, 0)),
    Sum.inr (Sum.inr (354, 13)),
    Sum.inr (Sum.inr (425, 0)),
    Sum.inr (Sum.inr (291, 13)),
    Sum.inr (Sum.inr (488, 0)),
    Sum.inr (Sum.inr (361, 13)),
    Sum.inr (Sum.inr (418, 0)),
    Sum.inr (Sum.inr (246, 13)),
    Sum.inr (Sum.inr (61, 0)),
    Sum.inr (Sum.inr (188, 13)),
    Sum.inr (Sum.inr (119, 0)),
    Sum.inr (Sum.inr (54, 8)),
    Sum.inr (Sum.inr (253, 23)),
    Sum.inr (Sum.inr (124, 8)),
    Sum.inr (Sum.inr (183, 23)),
    Sum.inr (Sum.inr (483, 8)),
    Sum.inr (Sum.inr (296, 23)),
    Sum.inr (Sum.inr (425, 8)),
    Sum.inr (Sum.inr (354, 23)),
    Sum.inr (Sum.inr (488, 8)),
    Sum.inr (Sum.inr (291, 23)),
    Sum.inr (Sum.inr (418, 8)),
    Sum.inr (Sum.inr (361, 23)),
    Sum.inr (Sum.inr (61, 8)),
    Sum.inr (Sum.inr (246, 23)),
    Sum.inr (Sum.inr (119, 8)),
    Sum.inr (Sum.inr (188, 23)),
    Sum.inr (Sum.inl (131, 10)),
    Sum.inr (Sum.inl (113, 12)),
    Sum.inr (Sum.inl (185, 24)),
    Sum.inr (Sum.inl (193, 8)),
    Sum.inr (Sum.inl (131, 24)),
    Sum.inr (Sum.inl (113, 4)),
    Sum.inr (Sum.inl (185, 16)),
    Sum.inr (Sum.inl (193, 16)),
    Sum.inr (Sum.inl (221, 6)),
    Sum.inr (Sum.inl (61, 6)),
    Sum.inr (Sum.inl (57, 34)),
    Sum.inr (Sum.inl (89, 36)),
    Sum.inr (Sum.inl (221, 18)),
    Sum.inr (Sum.inl (61, 20)),
    Sum.inr (Sum.inl (57, 48)),
    Sum.inr (Sum.inl (89, 32)),
    Sum.inr (Sum.inl (113, 29)),
    Sum.inr (Sum.inl (131, 49)),
    Sum.inr (Sum.inl (193, 41)),
    Sum.inr (Sum.inl (185, 35)),
    Sum.inr (Sum.inl (113, 21)),
    Sum.inr (Sum.inl (131, 35)),
    Sum.inr (Sum.inl (193, 49)),
    Sum.inr (Sum.inl (185, 43)),
    Sum.inr (Sum.inl (61, 39)),
    Sum.inr (Sum.inl (221, 56)),
    Sum.inr (Sum.inl (89, 53)),
    Sum.inr (Sum.inl (57, 25)),
    Sum.inr (Sum.inl (61, 53)),
    Sum.inr (Sum.inl (221, 44)),
    Sum.inr (Sum.inl (89, 49)),
    Sum.inr (Sum.inl (57, 11)),
    Sum.inr (Sum.inl (185, 10)),
    Sum.inr (Sum.inl (193, 12)),
    Sum.inr (Sum.inl (131, 2)),
    Sum.inr (Sum.inl (113, 55)),
    Sum.inr (Sum.inl (185, 2)),
    Sum.inr (Sum.inl (193, 20)),
    Sum.inr (Sum.inl (131, 16)),
    Sum.inr (Sum.inl (113, 63)),
    Sum.inr (Sum.inl (57, 3)),
    Sum.inr (Sum.inl (89, 6)),
    Sum.inr (Sum.inl (221, 36)),
    Sum.inr (Sum.inl (61, 2)),
    Sum.inr (Sum.inl (57, 17)),
    Sum.inr (Sum.inl (89, 2)),
    Sum.inr (Sum.inl (221, 48)),
    Sum.inr (Sum.inl (61, 16)),
    Sum.inr (Sum.inl (193, 45)),
    Sum.inr (Sum.inl (185, 49)),
    Sum.inr (Sum.inl (113, 38)),
    Sum.inr (Sum.inl (131, 57)),
    Sum.inr (Sum.inl (193, 53)),
    Sum.inr (Sum.inl (185, 57)),
    Sum.inr (Sum.inl (113, 46)),
    Sum.inr (Sum.inl (131, 43)),
    Sum.inr (Sum.inl (89, 23)),
    Sum.inr (Sum.inl (57, 56)),
    Sum.inr (Sum.inl (61, 35)),
    Sum.inr (Sum.inl (221, 26)),
    Sum.inr (Sum.inl (89, 19)),
    Sum.inr (Sum.inl (57, 42)),
    Sum.inr (Sum.inl (61, 49)),
    Sum.inr (Sum.inl (221, 14)),
    Sum.inr (Sum.inl (43, 10)),
    Sum.inr (Sum.inl (201, 12)),
    Sum.inr (Sum.inl (43, 6)),
    Sum.inr (Sum.inl (201, 4)),
    Sum.inr (Sum.inl (130, 3)),
    Sum.inr (Sum.inl (75, 10)),
    Sum.inr (Sum.inl (130, 1)),
    Sum.inr (Sum.inl (75, 6)),
    Sum.inr (Sum.inl (201, 30)),
    Sum.inr (Sum.inl (43, 42)),
    Sum.inr (Sum.inl (201, 22)),
    Sum.inr (Sum.inl (43, 38)),
    Sum.inr (Sum.inl (75, 43)),
    Sum.inr (Sum.inl (130, 28)),
    Sum.inr (Sum.inl (75, 39)),
    Sum.inr (Sum.inl (130, 30)),
    Sum.inr (Sum.inl (217, 34)),
    Sum.inr (Sum.inl (164, 8)),
    Sum.inr (Sum.inl (217, 48)),
    Sum.inr (Sum.inl (164, 4)),
    Sum.inr (Sum.inl (115, 2)),
    Sum.inr (Sum.inl (90, 61)),
    Sum.inr (Sum.inl (115, 1)),
    Sum.inr (Sum.inl (90, 63)),
    Sum.inr (Sum.inl (164, 26)),
    Sum.inr (Sum.inl (217, 42)),
    Sum.inr (Sum.inl (164, 22)),
    Sum.inr (Sum.inl (217, 56)),
    Sum.inr (Sum.inl (90, 52)),
    Sum.inr (Sum.inl (115, 29)),
    Sum.inr (Sum.inl (90, 54)),
    Sum.inr (Sum.inl (115, 30)),
    Sum.inr (Sum.inl (130, 23)),
    Sum.inr (Sum.inl (75, 37)),
    Sum.inr (Sum.inl (130, 21)),
    Sum.inr (Sum.inl (75, 41)),
    Sum.inr (Sum.inl (43, 52)),
    Sum.inr (Sum.inl (201, 50)),
    Sum.inr (Sum.inl (43, 56)),
    Sum.inr (Sum.inl (201, 58)),
    Sum.inr (Sum.inl (75, 4)),
    Sum.inr (Sum.inl (130, 8)),
    Sum.inr (Sum.inl (75, 8)),
    Sum.inr (Sum.inl (130, 10)),
    Sum.inr (Sum.inl (201, 32)),
    Sum.inr (Sum.inl (43, 20)),
    Sum.inr (Sum.inl (201, 40)),
    Sum.inr (Sum.inl (43, 24)),
    Sum.inr (Sum.inl (115, 22)),
    Sum.inr (Sum.inl (90, 25)),
    Sum.inr (Sum.inl (115, 21)),
    Sum.inr (Sum.inl (90, 27)),
    Sum.inr (Sum.inl (217, 28)),
    Sum.inr (Sum.inl (164, 54)),
    Sum.inr (Sum.inl (217, 14)),
    Sum.inr (Sum.inl (164, 58)),
    Sum.inr (Sum.inl (90, 16)),
    Sum.inr (Sum.inl (115, 9)),
    Sum.inr (Sum.inl (90, 18)),
    Sum.inr (Sum.inl (115, 10)),
    Sum.inr (Sum.inl (164, 36)),
    Sum.inr (Sum.inl (217, 20)),
    Sum.inr (Sum.inl (164, 40)),
    Sum.inr (Sum.inl (217, 6)),
    Sum.inr (Sum.inl (154, 40)),
    Sum.inr (Sum.inl (108, 23)),
    Sum.inr (Sum.inl (216, 39)),
    Sum.inr (Sum.inl (138, 63)),
    Sum.inr (Sum.inl (154, 21)),
    Sum.inr (Sum.inl (108, 8)),
    Sum.inr (Sum.inl (216, 8)),
    Sum.inr (Sum.inl (138, 29)),
    Sum.inr (Sum.inl (41, 33)),
    Sum.inr (Sum.inl (125, 39)),
    Sum.inr (Sum.inl (186, 51)),
    Sum.inr (Sum.inl (91, 3)),
    Sum.inr (Sum.inl (41, 41)),
    Sum.inr (Sum.inl (125, 6)),
    Sum.inr (Sum.inl (186, 18)),
    Sum.inr (Sum.inl (91, 7)),
    Sum.inr (Sum.inl (216, 37)),
    Sum.inr (Sum.inl (138, 55)),
    Sum.inr (Sum.inl (154, 36)),
    Sum.inr (Sum.inl (108, 27)),
    Sum.inr (Sum.inl (216, 10)),
    Sum.inr (Sum.inl (138, 21)),
    Sum.inr (Sum.inl (154, 25)),
    Sum.inr (Sum.inl (108, 4))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock024Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨6144 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block024_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock024Input a
    let y := generatedSixthXiShortBlock024Output a
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
theorem generatedSixth_xi_short_block024_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock024Input a
    let y := generatedSixthXiShortBlock024Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block024_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block024_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock024Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block024_certificate a).1
    (generatedSixth_xi_short_block024_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
