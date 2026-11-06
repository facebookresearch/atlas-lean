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
def generatedSixthXiShortBlock030Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (92, 62)),
    Sum.inr (Sum.inl (156, 26)),
    Sum.inr (Sum.inl (54, 40)),
    Sum.inr (Sum.inl (111, 25)),
    Sum.inr (Sum.inl (107, 46)),
    Sum.inr (Sum.inl (176, 32)),
    Sum.inr (Sum.inl (73, 54)),
    Sum.inr (Sum.inl (230, 10)),
    Sum.inr (Sum.inl (73, 25)),
    Sum.inr (Sum.inl (230, 40)),
    Sum.inr (Sum.inl (107, 42)),
    Sum.inr (Sum.inl (176, 1)),
    Sum.inr (Sum.inl (54, 8)),
    Sum.inr (Sum.inl (111, 39)),
    Sum.inr (Sum.inl (92, 9)),
    Sum.inr (Sum.inl (156, 56)),
    Sum.inr (Sum.inl (54, 4)),
    Sum.inr (Sum.inl (111, 43)),
    Sum.inr (Sum.inl (92, 10)),
    Sum.inr (Sum.inl (156, 52)),
    Sum.inr (Sum.inl (73, 27)),
    Sum.inr (Sum.inl (230, 32)),
    Sum.inr (Sum.inl (107, 56)),
    Sum.inr (Sum.inl (176, 3)),
    Sum.inr (Sum.inl (73, 61)),
    Sum.inr (Sum.inl (230, 22)),
    Sum.inr (Sum.inl (107, 20)),
    Sum.inr (Sum.inl (176, 21)),
    Sum.inr (Sum.inl (54, 54)),
    Sum.inr (Sum.inl (111, 55)),
    Sum.inr (Sum.inl (92, 45)),
    Sum.inr (Sum.inl (156, 6)),
    Sum.inr (Sum.inl (54, 58)),
    Sum.inr (Sum.inl (111, 59)),
    Sum.inr (Sum.inl (92, 46)),
    Sum.inr (Sum.inl (156, 10)),
    Sum.inr (Sum.inl (73, 63)),
    Sum.inr (Sum.inl (230, 30)),
    Sum.inr (Sum.inl (107, 6)),
    Sum.inr (Sum.inl (176, 23)),
    Sum.inr (Sum.inr (144, 21)),
    Sum.inr (Sum.inr (209, 21)),
    Sum.inr (Sum.inr (17, 2)),
    Sum.inr (Sum.inr (80, 2)),
    Sum.inr (Sum.inr (389, 21)),
    Sum.inr (Sum.inr (452, 21)),
    Sum.inr (Sum.inr (260, 2)),
    Sum.inr (Sum.inr (325, 2)),
    Sum.inr (Sum.inr (398, 21)),
    Sum.inr (Sum.inr (463, 21)),
    Sum.inr (Sum.inr (271, 2)),
    Sum.inr (Sum.inr (334, 2)),
    Sum.inr (Sum.inr (155, 21)),
    Sum.inr (Sum.inr (218, 21)),
    Sum.inr (Sum.inr (26, 2)),
    Sum.inr (Sum.inr (91, 2)),
    Sum.inr (Sum.inr (17, 9)),
    Sum.inr (Sum.inr (80, 9)),
    Sum.inr (Sum.inr (144, 14)),
    Sum.inr (Sum.inr (209, 14)),
    Sum.inr (Sum.inr (260, 9)),
    Sum.inr (Sum.inr (325, 9)),
    Sum.inr (Sum.inr (389, 14)),
    Sum.inr (Sum.inr (452, 14)),
    Sum.inr (Sum.inr (271, 9)),
    Sum.inr (Sum.inr (334, 9)),
    Sum.inr (Sum.inr (398, 14)),
    Sum.inr (Sum.inr (463, 14)),
    Sum.inr (Sum.inr (26, 9)),
    Sum.inr (Sum.inr (91, 9)),
    Sum.inr (Sum.inr (155, 14)),
    Sum.inr (Sum.inr (218, 14)),
    Sum.inr (Sum.inr (91, 21)),
    Sum.inr (Sum.inr (26, 21)),
    Sum.inr (Sum.inr (218, 2)),
    Sum.inr (Sum.inr (155, 2)),
    Sum.inr (Sum.inr (334, 21)),
    Sum.inr (Sum.inr (271, 21)),
    Sum.inr (Sum.inr (463, 2)),
    Sum.inr (Sum.inr (398, 2)),
    Sum.inr (Sum.inr (325, 21)),
    Sum.inr (Sum.inr (260, 21)),
    Sum.inr (Sum.inr (452, 2)),
    Sum.inr (Sum.inr (389, 2)),
    Sum.inr (Sum.inr (80, 21)),
    Sum.inr (Sum.inr (17, 21)),
    Sum.inr (Sum.inr (209, 2)),
    Sum.inr (Sum.inr (144, 2)),
    Sum.inr (Sum.inr (218, 9)),
    Sum.inr (Sum.inr (155, 9)),
    Sum.inr (Sum.inr (91, 14)),
    Sum.inr (Sum.inr (26, 14)),
    Sum.inr (Sum.inr (463, 9)),
    Sum.inr (Sum.inr (398, 9)),
    Sum.inr (Sum.inr (334, 14)),
    Sum.inr (Sum.inr (271, 14)),
    Sum.inr (Sum.inr (452, 9)),
    Sum.inr (Sum.inr (389, 9)),
    Sum.inr (Sum.inr (325, 14)),
    Sum.inr (Sum.inr (260, 14)),
    Sum.inr (Sum.inr (209, 9)),
    Sum.inr (Sum.inr (144, 9)),
    Sum.inr (Sum.inr (80, 14)),
    Sum.inr (Sum.inr (17, 14)),
    Sum.inr (Sum.inl (57, 2)),
    Sum.inr (Sum.inl (89, 59)),
    Sum.inr (Sum.inl (185, 40)),
    Sum.inr (Sum.inl (193, 55)),
    Sum.inr (Sum.inl (221, 38)),
    Sum.inr (Sum.inl (61, 57)),
    Sum.inr (Sum.inl (131, 42)),
    Sum.inr (Sum.inl (113, 19)),
    Sum.inr (Sum.inl (57, 16)),
    Sum.inr (Sum.inl (89, 63)),
    Sum.inr (Sum.inl (185, 32)),
    Sum.inr (Sum.inl (193, 47)),
    Sum.inr (Sum.inl (221, 50)),
    Sum.inr (Sum.inl (61, 43)),
    Sum.inr (Sum.inl (131, 56)),
    Sum.inr (Sum.inl (113, 27)),
    Sum.inr (Sum.inl (89, 42)),
    Sum.inr (Sum.inl (57, 57)),
    Sum.inr (Sum.inl (193, 22)),
    Sum.inr (Sum.inl (185, 19)),
    Sum.inr (Sum.inl (61, 24)),
    Sum.inr (Sum.inl (221, 24)),
    Sum.inr (Sum.inl (113, 2)),
    Sum.inr (Sum.inl (131, 17)),
    Sum.inr (Sum.inl (89, 46)),
    Sum.inr (Sum.inl (57, 43)),
    Sum.inr (Sum.inl (193, 14)),
    Sum.inr (Sum.inl (185, 27)),
    Sum.inr (Sum.inl (61, 10)),
    Sum.inr (Sum.inl (221, 12)),
    Sum.inr (Sum.inl (113, 10)),
    Sum.inr (Sum.inl (131, 3)),
    Sum.inr (Sum.inl (185, 9)),
    Sum.inr (Sum.inl (193, 10)),
    Sum.inr (Sum.inl (57, 10)),
    Sum.inr (Sum.inl (89, 12)),
    Sum.inr (Sum.inl (131, 11)),
    Sum.inr (Sum.inl (113, 49)),
    Sum.inr (Sum.inl (221, 46)),
    Sum.inr (Sum.inl (61, 14)),
    Sum.inr (Sum.inl (185, 1)),
    Sum.inr (Sum.inl (193, 18)),
    Sum.inr (Sum.inl (57, 24)),
    Sum.inr (Sum.inl (89, 8)),
    Sum.inr (Sum.inl (131, 25)),
    Sum.inr (Sum.inl (113, 57)),
    Sum.inr (Sum.inl (221, 58)),
    Sum.inr (Sum.inl (61, 28)),
    Sum.inr (Sum.inl (193, 43)),
    Sum.inr (Sum.inl (185, 50)),
    Sum.inr (Sum.inl (89, 29)),
    Sum.inr (Sum.inl (57, 49)),
    Sum.inr (Sum.inl (113, 32)),
    Sum.inr (Sum.inl (131, 48)),
    Sum.inr (Sum.inl (61, 47)),
    Sum.inr (Sum.inl (221, 16)),
    Sum.inr (Sum.inl (193, 51)),
    Sum.inr (Sum.inl (185, 58)),
    Sum.inr (Sum.inl (89, 25)),
    Sum.inr (Sum.inl (57, 35)),
    Sum.inr (Sum.inl (113, 40)),
    Sum.inr (Sum.inl (131, 34)),
    Sum.inr (Sum.inl (61, 61)),
    Sum.inr (Sum.inl (221, 4)),
    Sum.inr (Sum.inr (144, 10)),
    Sum.inr (Sum.inr (26, 20)),
    Sum.inr (Sum.inr (144, 12)),
    Sum.inr (Sum.inr (26, 3)),
    Sum.inr (Sum.inr (334, 20)),
    Sum.inr (Sum.inr (452, 10)),
    Sum.inr (Sum.inr (334, 3)),
    Sum.inr (Sum.inr (452, 12)),
    Sum.inr (Sum.inr (325, 20)),
    Sum.inr (Sum.inr (463, 10)),
    Sum.inr (Sum.inr (325, 3)),
    Sum.inr (Sum.inr (463, 12)),
    Sum.inr (Sum.inr (155, 10)),
    Sum.inr (Sum.inr (17, 20)),
    Sum.inr (Sum.inr (155, 12)),
    Sum.inr (Sum.inr (17, 3)),
    Sum.inr (Sum.inr (144, 3)),
    Sum.inr (Sum.inr (26, 12)),
    Sum.inr (Sum.inr (144, 20)),
    Sum.inr (Sum.inr (26, 10)),
    Sum.inr (Sum.inr (334, 12)),
    Sum.inr (Sum.inr (452, 3)),
    Sum.inr (Sum.inr (334, 10)),
    Sum.inr (Sum.inr (452, 20)),
    Sum.inr (Sum.inr (325, 12)),
    Sum.inr (Sum.inr (463, 3)),
    Sum.inr (Sum.inr (325, 10)),
    Sum.inr (Sum.inr (463, 20)),
    Sum.inr (Sum.inr (155, 3)),
    Sum.inr (Sum.inr (17, 12)),
    Sum.inr (Sum.inr (155, 20)),
    Sum.inr (Sum.inr (17, 10)),
    Sum.inr (Sum.inr (91, 20)),
    Sum.inr (Sum.inr (209, 10)),
    Sum.inr (Sum.inr (91, 3)),
    Sum.inr (Sum.inr (209, 12)),
    Sum.inr (Sum.inr (389, 10)),
    Sum.inr (Sum.inr (271, 20)),
    Sum.inr (Sum.inr (389, 12)),
    Sum.inr (Sum.inr (271, 3)),
    Sum.inr (Sum.inr (398, 10)),
    Sum.inr (Sum.inr (260, 20)),
    Sum.inr (Sum.inr (398, 12)),
    Sum.inr (Sum.inr (260, 3)),
    Sum.inr (Sum.inr (80, 20)),
    Sum.inr (Sum.inr (218, 10)),
    Sum.inr (Sum.inr (80, 3)),
    Sum.inr (Sum.inr (218, 12)),
    Sum.inr (Sum.inr (91, 12)),
    Sum.inr (Sum.inr (209, 3)),
    Sum.inr (Sum.inr (91, 10)),
    Sum.inr (Sum.inr (209, 20)),
    Sum.inr (Sum.inr (389, 3)),
    Sum.inr (Sum.inr (271, 12)),
    Sum.inr (Sum.inr (389, 20)),
    Sum.inr (Sum.inr (271, 10)),
    Sum.inr (Sum.inr (398, 3)),
    Sum.inr (Sum.inr (260, 12)),
    Sum.inr (Sum.inr (398, 20)),
    Sum.inr (Sum.inr (260, 10)),
    Sum.inr (Sum.inr (80, 12)),
    Sum.inr (Sum.inr (218, 3)),
    Sum.inr (Sum.inr (80, 10)),
    Sum.inr (Sum.inr (218, 20)),
    Sum.inr (Sum.inl (201, 20)),
    Sum.inr (Sum.inl (164, 48)),
    Sum.inr (Sum.inl (164, 60)),
    Sum.inr (Sum.inl (201, 28)),
    Sum.inr (Sum.inl (90, 24)),
    Sum.inr (Sum.inl (75, 34)),
    Sum.inr (Sum.inl (75, 46)),
    Sum.inr (Sum.inl (90, 26)),
    Sum.inr (Sum.inl (201, 48)),
    Sum.inr (Sum.inl (164, 16)),
    Sum.inr (Sum.inl (164, 28)),
    Sum.inr (Sum.inl (201, 56)),
    Sum.inr (Sum.inl (90, 55)),
    Sum.inr (Sum.inl (75, 32)),
    Sum.inr (Sum.inl (75, 44)),
    Sum.inr (Sum.inl (90, 53)),
    Sum.inr (Sum.inl (90, 60)),
    Sum.inr (Sum.inl (75, 13)),
    Sum.inr (Sum.inl (75, 1)),
    Sum.inr (Sum.inl (90, 62)),
    Sum.inr (Sum.inl (201, 42)),
    Sum.inr (Sum.inl (164, 14)),
    Sum.inr (Sum.inl (164, 2)),
    Sum.inr (Sum.inl (201, 34))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock030Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨7680 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block030_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock030Input a
    let y := generatedSixthXiShortBlock030Output a
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
theorem generatedSixth_xi_short_block030_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock030Input a
    let y := generatedSixthXiShortBlock030Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block030_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block030_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock030Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block030_certificate a).1
    (generatedSixth_xi_short_block030_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
