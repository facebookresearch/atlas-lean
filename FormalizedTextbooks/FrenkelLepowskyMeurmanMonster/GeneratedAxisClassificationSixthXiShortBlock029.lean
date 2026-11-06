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
def generatedSixthXiShortBlock029Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (176, 47)),
    Sum.inr (Sum.inl (107, 27)),
    Sum.inr (Sum.inl (92, 20)),
    Sum.inr (Sum.inl (156, 51)),
    Sum.inr (Sum.inl (176, 14)),
    Sum.inr (Sum.inl (107, 31)),
    Sum.inr (Sum.inl (92, 35)),
    Sum.inr (Sum.inl (156, 17)),
    Sum.inr (Sum.inl (92, 7)),
    Sum.inr (Sum.inl (156, 47)),
    Sum.inr (Sum.inl (176, 26)),
    Sum.inr (Sum.inl (107, 33)),
    Sum.inr (Sum.inl (92, 48)),
    Sum.inr (Sum.inl (156, 13)),
    Sum.inr (Sum.inl (176, 59)),
    Sum.inr (Sum.inl (107, 37)),
    Sum.inr (Sum.inl (111, 32)),
    Sum.inr (Sum.inl (54, 15)),
    Sum.inr (Sum.inl (73, 5)),
    Sum.inr (Sum.inl (230, 39)),
    Sum.inr (Sum.inl (111, 30)),
    Sum.inr (Sum.inl (54, 47)),
    Sum.inr (Sum.inl (73, 42)),
    Sum.inr (Sum.inl (230, 5)),
    Sum.inr (Sum.inl (176, 24)),
    Sum.inr (Sum.inl (107, 51)),
    Sum.inr (Sum.inl (92, 4)),
    Sum.inr (Sum.inl (156, 35)),
    Sum.inr (Sum.inl (176, 57)),
    Sum.inr (Sum.inl (107, 55)),
    Sum.inr (Sum.inl (92, 51)),
    Sum.inr (Sum.inl (156, 1)),
    Sum.inr (Sum.inl (73, 7)),
    Sum.inr (Sum.inl (230, 47)),
    Sum.inr (Sum.inl (111, 44)),
    Sum.inr (Sum.inl (54, 3)),
    Sum.inr (Sum.inl (73, 40)),
    Sum.inr (Sum.inl (230, 13)),
    Sum.inr (Sum.inl (111, 18)),
    Sum.inr (Sum.inl (54, 35)),
    Sum.inr (Sum.inl (186, 12)),
    Sum.inr (Sum.inl (138, 20)),
    Sum.inr (Sum.inl (186, 24)),
    Sum.inr (Sum.inl (138, 47)),
    Sum.inr (Sum.inl (125, 18)),
    Sum.inr (Sum.inl (154, 48)),
    Sum.inr (Sum.inl (125, 16)),
    Sum.inr (Sum.inl (154, 16)),
    Sum.inr (Sum.inl (125, 30)),
    Sum.inr (Sum.inl (154, 60)),
    Sum.inr (Sum.inl (125, 28)),
    Sum.inr (Sum.inl (154, 28)),
    Sum.inr (Sum.inl (186, 14)),
    Sum.inr (Sum.inl (138, 28)),
    Sum.inr (Sum.inl (186, 26)),
    Sum.inr (Sum.inl (138, 39)),
    Sum.inr (Sum.inl (138, 5)),
    Sum.inr (Sum.inl (186, 59)),
    Sum.inr (Sum.inl (138, 62)),
    Sum.inr (Sum.inl (186, 47)),
    Sum.inr (Sum.inl (154, 33)),
    Sum.inr (Sum.inl (125, 61)),
    Sum.inr (Sum.inl (154, 1)),
    Sum.inr (Sum.inl (125, 63)),
    Sum.inr (Sum.inl (154, 45)),
    Sum.inr (Sum.inl (125, 49)),
    Sum.inr (Sum.inl (154, 13)),
    Sum.inr (Sum.inl (125, 51)),
    Sum.inr (Sum.inl (138, 13)),
    Sum.inr (Sum.inl (186, 57)),
    Sum.inr (Sum.inl (138, 54)),
    Sum.inr (Sum.inl (186, 45)),
    Sum.inr (Sum.inl (91, 9)),
    Sum.inr (Sum.inl (216, 12)),
    Sum.inr (Sum.inl (91, 40)),
    Sum.inr (Sum.inl (216, 36)),
    Sum.inr (Sum.inl (41, 20)),
    Sum.inr (Sum.inl (108, 18)),
    Sum.inr (Sum.inl (41, 48)),
    Sum.inr (Sum.inl (108, 16)),
    Sum.inr (Sum.inl (41, 23)),
    Sum.inr (Sum.inl (108, 30)),
    Sum.inr (Sum.inl (41, 51)),
    Sum.inr (Sum.inl (108, 28)),
    Sum.inr (Sum.inl (91, 27)),
    Sum.inr (Sum.inl (216, 14)),
    Sum.inr (Sum.inl (91, 58)),
    Sum.inr (Sum.inl (216, 38)),
    Sum.inr (Sum.inl (216, 9)),
    Sum.inr (Sum.inl (91, 62)),
    Sum.inr (Sum.inl (216, 33)),
    Sum.inr (Sum.inl (91, 31)),
    Sum.inr (Sum.inl (108, 3)),
    Sum.inr (Sum.inl (41, 59)),
    Sum.inr (Sum.inl (108, 1)),
    Sum.inr (Sum.inl (41, 31)),
    Sum.inr (Sum.inl (108, 15)),
    Sum.inr (Sum.inl (41, 56)),
    Sum.inr (Sum.inl (108, 13)),
    Sum.inr (Sum.inl (41, 28)),
    Sum.inr (Sum.inl (216, 11)),
    Sum.inr (Sum.inl (91, 44)),
    Sum.inr (Sum.inl (216, 35)),
    Sum.inr (Sum.inl (91, 13)),
    Sum.inr (Sum.inl (159, 59)),
    Sum.inr (Sum.inl (181, 20)),
    Sum.inr (Sum.inl (227, 63)),
    Sum.inr (Sum.inl (79, 31)),
    Sum.inr (Sum.inl (68, 50)),
    Sum.inr (Sum.inl (51, 50)),
    Sum.inr (Sum.inl (137, 45)),
    Sum.inr (Sum.inl (109, 11)),
    Sum.inr (Sum.inl (159, 56)),
    Sum.inr (Sum.inl (181, 22)),
    Sum.inr (Sum.inl (227, 45)),
    Sum.inr (Sum.inl (79, 19)),
    Sum.inr (Sum.inl (68, 48)),
    Sum.inr (Sum.inl (51, 62)),
    Sum.inr (Sum.inl (137, 33)),
    Sum.inr (Sum.inl (109, 3)),
    Sum.inr (Sum.inl (181, 5)),
    Sum.inr (Sum.inl (159, 36)),
    Sum.inr (Sum.inl (79, 62)),
    Sum.inr (Sum.inl (227, 8)),
    Sum.inr (Sum.inl (51, 19)),
    Sum.inr (Sum.inl (68, 45)),
    Sum.inr (Sum.inl (109, 26)),
    Sum.inr (Sum.inl (137, 50)),
    Sum.inr (Sum.inl (181, 7)),
    Sum.inr (Sum.inl (159, 39)),
    Sum.inr (Sum.inl (79, 50)),
    Sum.inr (Sum.inl (227, 26)),
    Sum.inr (Sum.inl (51, 31)),
    Sum.inr (Sum.inl (68, 47)),
    Sum.inr (Sum.inl (109, 18)),
    Sum.inr (Sum.inl (137, 62)),
    Sum.inr (Sum.inl (68, 59)),
    Sum.inr (Sum.inl (51, 48)),
    Sum.inr (Sum.inl (137, 63)),
    Sum.inr (Sum.inl (109, 47)),
    Sum.inr (Sum.inl (159, 51)),
    Sum.inr (Sum.inl (181, 35)),
    Sum.inr (Sum.inl (227, 27)),
    Sum.inr (Sum.inl (79, 15)),
    Sum.inr (Sum.inl (68, 57)),
    Sum.inr (Sum.inl (51, 60)),
    Sum.inr (Sum.inl (137, 51)),
    Sum.inr (Sum.inl (109, 39)),
    Sum.inr (Sum.inl (159, 48)),
    Sum.inr (Sum.inl (181, 33)),
    Sum.inr (Sum.inl (227, 9)),
    Sum.inr (Sum.inl (79, 3)),
    Sum.inr (Sum.inl (51, 17)),
    Sum.inr (Sum.inl (68, 36)),
    Sum.inr (Sum.inl (109, 62)),
    Sum.inr (Sum.inl (137, 32)),
    Sum.inr (Sum.inl (181, 50)),
    Sum.inr (Sum.inl (159, 44)),
    Sum.inr (Sum.inl (79, 46)),
    Sum.inr (Sum.inl (227, 44)),
    Sum.inr (Sum.inl (51, 29)),
    Sum.inr (Sum.inl (68, 38)),
    Sum.inr (Sum.inl (109, 54)),
    Sum.inr (Sum.inl (137, 44)),
    Sum.inr (Sum.inl (181, 48)),
    Sum.inr (Sum.inl (159, 47)),
    Sum.inr (Sum.inl (79, 34)),
    Sum.inr (Sum.inl (227, 62)),
    Sum.inr (Sum.inl (67, 37)),
    Sum.inr (Sum.inl (226, 51)),
    Sum.inr (Sum.inl (67, 13)),
    Sum.inr (Sum.inl (226, 23)),
    Sum.inr (Sum.inl (123, 13)),
    Sum.inr (Sum.inl (197, 43)),
    Sum.inr (Sum.inl (123, 15)),
    Sum.inr (Sum.inl (197, 15)),
    Sum.inr (Sum.inl (80, 51)),
    Sum.inr (Sum.inl (47, 25)),
    Sum.inr (Sum.inl (80, 13)),
    Sum.inr (Sum.inl (47, 13)),
    Sum.inr (Sum.inl (190, 13)),
    Sum.inr (Sum.inl (110, 13)),
    Sum.inr (Sum.inl (190, 15)),
    Sum.inr (Sum.inl (110, 15)),
    Sum.inr (Sum.inl (123, 21)),
    Sum.inr (Sum.inl (197, 51)),
    Sum.inr (Sum.inl (123, 23)),
    Sum.inr (Sum.inl (197, 23)),
    Sum.inr (Sum.inl (67, 39)),
    Sum.inr (Sum.inl (226, 43)),
    Sum.inr (Sum.inl (67, 15)),
    Sum.inr (Sum.inl (226, 15)),
    Sum.inr (Sum.inl (190, 25)),
    Sum.inr (Sum.inl (110, 25)),
    Sum.inr (Sum.inl (190, 27)),
    Sum.inr (Sum.inl (110, 27)),
    Sum.inr (Sum.inl (80, 49)),
    Sum.inr (Sum.inl (47, 27)),
    Sum.inr (Sum.inl (80, 15)),
    Sum.inr (Sum.inl (47, 15)),
    Sum.inr (Sum.inl (80, 27)),
    Sum.inr (Sum.inl (47, 49)),
    Sum.inr (Sum.inl (80, 37)),
    Sum.inr (Sum.inl (47, 37)),
    Sum.inr (Sum.inl (190, 58)),
    Sum.inr (Sum.inl (110, 37)),
    Sum.inr (Sum.inl (190, 56)),
    Sum.inr (Sum.inl (110, 39)),
    Sum.inr (Sum.inl (67, 27)),
    Sum.inr (Sum.inl (226, 49)),
    Sum.inr (Sum.inl (67, 51)),
    Sum.inr (Sum.inl (226, 21)),
    Sum.inr (Sum.inl (123, 51)),
    Sum.inr (Sum.inl (197, 41)),
    Sum.inr (Sum.inl (123, 49)),
    Sum.inr (Sum.inl (197, 13)),
    Sum.inr (Sum.inl (190, 46)),
    Sum.inr (Sum.inl (110, 49)),
    Sum.inr (Sum.inl (190, 44)),
    Sum.inr (Sum.inl (110, 51)),
    Sum.inr (Sum.inl (80, 25)),
    Sum.inr (Sum.inl (47, 51)),
    Sum.inr (Sum.inl (80, 39)),
    Sum.inr (Sum.inl (47, 39)),
    Sum.inr (Sum.inl (123, 43)),
    Sum.inr (Sum.inl (197, 49)),
    Sum.inr (Sum.inl (123, 41)),
    Sum.inr (Sum.inl (197, 21)),
    Sum.inr (Sum.inl (67, 25)),
    Sum.inr (Sum.inl (226, 41)),
    Sum.inr (Sum.inl (67, 49)),
    Sum.inr (Sum.inl (226, 13)),
    Sum.inr (Sum.inl (107, 2)),
    Sum.inr (Sum.inl (176, 54)),
    Sum.inr (Sum.inl (73, 16)),
    Sum.inr (Sum.inl (230, 60)),
    Sum.inr (Sum.inl (92, 25)),
    Sum.inr (Sum.inl (156, 40)),
    Sum.inr (Sum.inl (54, 26)),
    Sum.inr (Sum.inl (111, 5)),
    Sum.inr (Sum.inl (92, 26)),
    Sum.inr (Sum.inl (156, 36)),
    Sum.inr (Sum.inl (54, 22)),
    Sum.inr (Sum.inl (111, 9)),
    Sum.inr (Sum.inl (107, 16)),
    Sum.inr (Sum.inl (176, 52)),
    Sum.inr (Sum.inl (73, 18)),
    Sum.inr (Sum.inl (230, 52)),
    Sum.inr (Sum.inl (107, 60)),
    Sum.inr (Sum.inl (176, 34)),
    Sum.inr (Sum.inl (73, 52)),
    Sum.inr (Sum.inl (230, 2)),
    Sum.inr (Sum.inl (92, 61)),
    Sum.inr (Sum.inl (156, 22)),
    Sum.inr (Sum.inl (54, 36)),
    Sum.inr (Sum.inl (111, 21))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock029Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨7424 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block029_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock029Input a
    let y := generatedSixthXiShortBlock029Output a
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
theorem generatedSixth_xi_short_block029_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock029Input a
    let y := generatedSixthXiShortBlock029Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block029_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block029_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock029Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block029_certificate a).1
    (generatedSixth_xi_short_block029_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
