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
def generatedSixthXiShortBlock015Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (159, 42)),
    Sum.inr (Sum.inl (51, 11)),
    Sum.inr (Sum.inl (159, 34)),
    Sum.inr (Sum.inl (51, 9)),
    Sum.inr (Sum.inl (68, 43)),
    Sum.inr (Sum.inl (181, 52)),
    Sum.inr (Sum.inl (68, 34)),
    Sum.inr (Sum.inl (181, 3)),
    Sum.inr (Sum.inl (109, 9)),
    Sum.inr (Sum.inl (227, 10)),
    Sum.inr (Sum.inl (109, 45)),
    Sum.inr (Sum.inl (227, 46)),
    Sum.inr (Sum.inl (79, 9)),
    Sum.inr (Sum.inl (137, 40)),
    Sum.inr (Sum.inl (79, 25)),
    Sum.inr (Sum.inl (137, 58)),
    Sum.inr (Sum.inl (79, 5)),
    Sum.inr (Sum.inl (137, 36)),
    Sum.inr (Sum.inl (79, 21)),
    Sum.inr (Sum.inl (137, 54)),
    Sum.inr (Sum.inl (109, 1)),
    Sum.inr (Sum.inl (227, 24)),
    Sum.inr (Sum.inl (109, 37)),
    Sum.inr (Sum.inl (227, 60)),
    Sum.inr (Sum.inl (181, 39)),
    Sum.inr (Sum.inl (68, 54)),
    Sum.inr (Sum.inl (181, 16)),
    Sum.inr (Sum.inl (68, 63)),
    Sum.inr (Sum.inl (51, 38)),
    Sum.inr (Sum.inl (159, 54)),
    Sum.inr (Sum.inl (51, 36)),
    Sum.inr (Sum.inl (159, 62)),
    Sum.inr (Sum.inl (51, 42)),
    Sum.inr (Sum.inl (159, 53)),
    Sum.inr (Sum.inl (51, 40)),
    Sum.inr (Sum.inl (159, 61)),
    Sum.inr (Sum.inl (181, 37)),
    Sum.inr (Sum.inl (68, 52)),
    Sum.inr (Sum.inl (181, 18)),
    Sum.inr (Sum.inl (68, 61)),
    Sum.inr (Sum.inr (16, 11)),
    Sum.inr (Sum.inr (16, 15)),
    Sum.inr (Sum.inr (154, 22)),
    Sum.inr (Sum.inr (154, 1)),
    Sum.inr (Sum.inr (324, 22)),
    Sum.inr (Sum.inr (324, 1)),
    Sum.inr (Sum.inr (462, 11)),
    Sum.inr (Sum.inr (462, 15)),
    Sum.inr (Sum.inr (335, 22)),
    Sum.inr (Sum.inr (335, 1)),
    Sum.inr (Sum.inr (453, 11)),
    Sum.inr (Sum.inr (453, 15)),
    Sum.inr (Sum.inr (27, 11)),
    Sum.inr (Sum.inr (27, 15)),
    Sum.inr (Sum.inr (145, 22)),
    Sum.inr (Sum.inr (145, 1)),
    Sum.inr (Sum.inr (208, 22)),
    Sum.inr (Sum.inr (208, 1)),
    Sum.inr (Sum.inr (90, 11)),
    Sum.inr (Sum.inr (90, 15)),
    Sum.inr (Sum.inr (388, 11)),
    Sum.inr (Sum.inr (388, 15)),
    Sum.inr (Sum.inr (270, 22)),
    Sum.inr (Sum.inr (270, 1)),
    Sum.inr (Sum.inr (399, 11)),
    Sum.inr (Sum.inr (399, 15)),
    Sum.inr (Sum.inr (261, 22)),
    Sum.inr (Sum.inr (261, 1)),
    Sum.inr (Sum.inr (219, 22)),
    Sum.inr (Sum.inr (219, 1)),
    Sum.inr (Sum.inr (81, 11)),
    Sum.inr (Sum.inr (81, 15)),
    Sum.inr (Sum.inr (16, 1)),
    Sum.inr (Sum.inr (16, 22)),
    Sum.inr (Sum.inr (154, 15)),
    Sum.inr (Sum.inr (154, 11)),
    Sum.inr (Sum.inr (324, 15)),
    Sum.inr (Sum.inr (324, 11)),
    Sum.inr (Sum.inr (462, 1)),
    Sum.inr (Sum.inr (462, 22)),
    Sum.inr (Sum.inr (335, 15)),
    Sum.inr (Sum.inr (335, 11)),
    Sum.inr (Sum.inr (453, 1)),
    Sum.inr (Sum.inr (453, 22)),
    Sum.inr (Sum.inr (27, 1)),
    Sum.inr (Sum.inr (27, 22)),
    Sum.inr (Sum.inr (145, 15)),
    Sum.inr (Sum.inr (145, 11)),
    Sum.inr (Sum.inr (208, 15)),
    Sum.inr (Sum.inr (208, 11)),
    Sum.inr (Sum.inr (90, 1)),
    Sum.inr (Sum.inr (90, 22)),
    Sum.inr (Sum.inr (388, 1)),
    Sum.inr (Sum.inr (388, 22)),
    Sum.inr (Sum.inr (270, 15)),
    Sum.inr (Sum.inr (270, 11)),
    Sum.inr (Sum.inr (399, 1)),
    Sum.inr (Sum.inr (399, 22)),
    Sum.inr (Sum.inr (261, 15)),
    Sum.inr (Sum.inr (261, 11)),
    Sum.inr (Sum.inr (219, 15)),
    Sum.inr (Sum.inr (219, 11)),
    Sum.inr (Sum.inr (81, 1)),
    Sum.inr (Sum.inr (81, 22)),
    Sum.inr (Sum.inr (16, 23)),
    Sum.inr (Sum.inr (16, 8)),
    Sum.inr (Sum.inr (219, 13)),
    Sum.inr (Sum.inr (219, 0)),
    Sum.inr (Sum.inr (261, 13)),
    Sum.inr (Sum.inr (261, 0)),
    Sum.inr (Sum.inr (462, 23)),
    Sum.inr (Sum.inr (462, 8)),
    Sum.inr (Sum.inr (270, 13)),
    Sum.inr (Sum.inr (270, 0)),
    Sum.inr (Sum.inr (453, 23)),
    Sum.inr (Sum.inr (453, 8)),
    Sum.inr (Sum.inr (27, 23)),
    Sum.inr (Sum.inr (27, 8)),
    Sum.inr (Sum.inr (208, 13)),
    Sum.inr (Sum.inr (208, 0)),
    Sum.inr (Sum.inr (16, 0)),
    Sum.inr (Sum.inr (16, 13)),
    Sum.inr (Sum.inr (219, 8)),
    Sum.inr (Sum.inr (219, 23)),
    Sum.inr (Sum.inr (261, 8)),
    Sum.inr (Sum.inr (261, 23)),
    Sum.inr (Sum.inr (462, 0)),
    Sum.inr (Sum.inr (462, 13)),
    Sum.inr (Sum.inr (270, 8)),
    Sum.inr (Sum.inr (270, 23)),
    Sum.inr (Sum.inr (453, 0)),
    Sum.inr (Sum.inr (453, 13)),
    Sum.inr (Sum.inr (27, 0)),
    Sum.inr (Sum.inr (27, 13)),
    Sum.inr (Sum.inr (208, 8)),
    Sum.inr (Sum.inr (208, 23)),
    Sum.inr (Sum.inr (81, 13)),
    Sum.inr (Sum.inr (81, 0)),
    Sum.inr (Sum.inr (154, 23)),
    Sum.inr (Sum.inr (154, 8)),
    Sum.inr (Sum.inr (324, 23)),
    Sum.inr (Sum.inr (324, 8)),
    Sum.inr (Sum.inr (399, 13)),
    Sum.inr (Sum.inr (399, 0)),
    Sum.inr (Sum.inr (335, 23)),
    Sum.inr (Sum.inr (335, 8)),
    Sum.inr (Sum.inr (388, 13)),
    Sum.inr (Sum.inr (388, 0)),
    Sum.inr (Sum.inr (90, 13)),
    Sum.inr (Sum.inr (90, 0)),
    Sum.inr (Sum.inr (145, 23)),
    Sum.inr (Sum.inr (145, 8)),
    Sum.inr (Sum.inr (81, 8)),
    Sum.inr (Sum.inr (81, 23)),
    Sum.inr (Sum.inr (154, 0)),
    Sum.inr (Sum.inr (154, 13)),
    Sum.inr (Sum.inr (324, 0)),
    Sum.inr (Sum.inr (324, 13)),
    Sum.inr (Sum.inr (399, 8)),
    Sum.inr (Sum.inr (399, 23)),
    Sum.inr (Sum.inr (335, 0)),
    Sum.inr (Sum.inr (335, 13)),
    Sum.inr (Sum.inr (388, 8)),
    Sum.inr (Sum.inr (388, 23)),
    Sum.inr (Sum.inr (90, 8)),
    Sum.inr (Sum.inr (90, 23)),
    Sum.inr (Sum.inr (145, 0)),
    Sum.inr (Sum.inr (145, 13)),
    Sum.inr (Sum.inl (176, 18)),
    Sum.inr (Sum.inl (107, 57)),
    Sum.inr (Sum.inl (73, 4)),
    Sum.inr (Sum.inl (230, 35)),
    Sum.inr (Sum.inl (92, 21)),
    Sum.inr (Sum.inl (156, 55)),
    Sum.inr (Sum.inl (111, 42)),
    Sum.inr (Sum.inl (54, 5)),
    Sum.inr (Sum.inl (92, 22)),
    Sum.inr (Sum.inl (156, 59)),
    Sum.inr (Sum.inl (111, 38)),
    Sum.inr (Sum.inl (54, 9)),
    Sum.inr (Sum.inl (176, 16)),
    Sum.inr (Sum.inl (107, 43)),
    Sum.inr (Sum.inl (73, 6)),
    Sum.inr (Sum.inl (230, 43)),
    Sum.inr (Sum.inl (73, 13)),
    Sum.inr (Sum.inl (230, 55)),
    Sum.inr (Sum.inl (176, 37)),
    Sum.inr (Sum.inl (107, 17)),
    Sum.inr (Sum.inl (111, 8)),
    Sum.inr (Sum.inl (54, 23)),
    Sum.inr (Sum.inl (92, 5)),
    Sum.inr (Sum.inl (156, 39)),
    Sum.inr (Sum.inl (111, 4)),
    Sum.inr (Sum.inl (54, 27)),
    Sum.inr (Sum.inl (92, 6)),
    Sum.inr (Sum.inl (156, 43)),
    Sum.inr (Sum.inl (73, 15)),
    Sum.inr (Sum.inl (230, 63)),
    Sum.inr (Sum.inl (176, 39)),
    Sum.inr (Sum.inl (107, 3)),
    Sum.inr (Sum.inl (176, 51)),
    Sum.inr (Sum.inl (107, 61)),
    Sum.inr (Sum.inl (73, 43)),
    Sum.inr (Sum.inl (230, 1)),
    Sum.inr (Sum.inl (92, 34)),
    Sum.inr (Sum.inl (156, 21)),
    Sum.inr (Sum.inl (111, 20)),
    Sum.inr (Sum.inl (54, 37)),
    Sum.inr (Sum.inl (92, 33)),
    Sum.inr (Sum.inl (156, 25)),
    Sum.inr (Sum.inl (111, 24)),
    Sum.inr (Sum.inl (54, 41)),
    Sum.inr (Sum.inl (176, 49)),
    Sum.inr (Sum.inl (107, 47)),
    Sum.inr (Sum.inl (73, 41)),
    Sum.inr (Sum.inl (230, 9)),
    Sum.inr (Sum.inl (73, 34)),
    Sum.inr (Sum.inl (230, 21)),
    Sum.inr (Sum.inl (176, 4)),
    Sum.inr (Sum.inl (107, 21)),
    Sum.inr (Sum.inl (111, 54)),
    Sum.inr (Sum.inl (54, 55)),
    Sum.inr (Sum.inl (92, 50)),
    Sum.inr (Sum.inl (156, 5)),
    Sum.inr (Sum.inl (111, 58)),
    Sum.inr (Sum.inl (54, 59)),
    Sum.inr (Sum.inl (92, 49)),
    Sum.inr (Sum.inl (156, 9)),
    Sum.inr (Sum.inl (73, 32)),
    Sum.inr (Sum.inl (230, 29)),
    Sum.inr (Sum.inl (176, 6)),
    Sum.inr (Sum.inl (107, 7)),
    Sum.inr (Sum.inl (78, 40)),
    Sum.inr (Sum.inl (124, 60)),
    Sum.inr (Sum.inl (78, 36)),
    Sum.inr (Sum.inl (124, 52)),
    Sum.inr (Sum.inl (225, 61)),
    Sum.inr (Sum.inl (139, 21)),
    Sum.inr (Sum.inl (225, 47)),
    Sum.inr (Sum.inl (139, 25)),
    Sum.inr (Sum.inl (155, 54)),
    Sum.inr (Sum.inl (72, 5)),
    Sum.inr (Sum.inl (155, 52)),
    Sum.inr (Sum.inl (72, 9)),
    Sum.inr (Sum.inl (177, 21)),
    Sum.inr (Sum.inl (55, 4)),
    Sum.inr (Sum.inl (177, 22)),
    Sum.inr (Sum.inl (55, 6)),
    Sum.inr (Sum.inl (124, 40)),
    Sum.inr (Sum.inl (78, 56)),
    Sum.inr (Sum.inl (124, 32)),
    Sum.inr (Sum.inl (78, 52)),
    Sum.inr (Sum.inl (139, 55)),
    Sum.inr (Sum.inl (225, 21)),
    Sum.inr (Sum.inl (139, 59)),
    Sum.inr (Sum.inl (225, 7))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock015Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨3840 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block015_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock015Input a
    let y := generatedSixthXiShortBlock015Output a
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
theorem generatedSixth_xi_short_block015_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock015Input a
    let y := generatedSixthXiShortBlock015Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block015_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block015_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock015Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block015_certificate a).1
    (generatedSixth_xi_short_block015_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
