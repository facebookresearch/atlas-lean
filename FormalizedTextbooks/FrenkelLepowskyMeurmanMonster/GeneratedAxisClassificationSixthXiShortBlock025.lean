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
def generatedSixthXiShortBlock025Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (186, 49)),
    Sum.inr (Sum.inl (91, 17)),
    Sum.inr (Sum.inl (41, 34)),
    Sum.inr (Sum.inl (125, 43)),
    Sum.inr (Sum.inl (186, 16)),
    Sum.inr (Sum.inl (91, 21)),
    Sum.inr (Sum.inl (41, 42)),
    Sum.inr (Sum.inl (125, 10)),
    Sum.inr (Sum.inl (108, 21)),
    Sum.inr (Sum.inl (154, 8)),
    Sum.inr (Sum.inl (138, 4)),
    Sum.inr (Sum.inl (216, 15)),
    Sum.inr (Sum.inl (108, 10)),
    Sum.inr (Sum.inl (154, 53)),
    Sum.inr (Sum.inl (138, 38)),
    Sum.inr (Sum.inl (216, 32)),
    Sum.inr (Sum.inl (125, 37)),
    Sum.inr (Sum.inl (41, 5)),
    Sum.inr (Sum.inl (91, 34)),
    Sum.inr (Sum.inl (186, 39)),
    Sum.inr (Sum.inl (125, 4)),
    Sum.inr (Sum.inl (41, 13)),
    Sum.inr (Sum.inl (91, 38)),
    Sum.inr (Sum.inl (186, 6)),
    Sum.inr (Sum.inl (138, 12)),
    Sum.inr (Sum.inl (216, 13)),
    Sum.inr (Sum.inl (108, 25)),
    Sum.inr (Sum.inl (154, 4)),
    Sum.inr (Sum.inl (138, 46)),
    Sum.inr (Sum.inl (216, 34)),
    Sum.inr (Sum.inl (108, 6)),
    Sum.inr (Sum.inl (154, 57)),
    Sum.inr (Sum.inl (91, 48)),
    Sum.inr (Sum.inl (186, 37)),
    Sum.inr (Sum.inl (125, 41)),
    Sum.inr (Sum.inl (41, 6)),
    Sum.inr (Sum.inl (91, 52)),
    Sum.inr (Sum.inl (186, 4)),
    Sum.inr (Sum.inl (125, 8)),
    Sum.inr (Sum.inl (41, 14)),
    Sum.inr (Sum.inl (230, 12)),
    Sum.inr (Sum.inl (156, 24)),
    Sum.inr (Sum.inl (156, 20)),
    Sum.inr (Sum.inl (230, 4)),
    Sum.inr (Sum.inl (176, 10)),
    Sum.inr (Sum.inl (111, 10)),
    Sum.inr (Sum.inl (111, 6)),
    Sum.inr (Sum.inl (176, 8)),
    Sum.inr (Sum.inl (107, 10)),
    Sum.inr (Sum.inl (54, 10)),
    Sum.inr (Sum.inl (54, 6)),
    Sum.inr (Sum.inl (107, 24)),
    Sum.inr (Sum.inl (73, 3)),
    Sum.inr (Sum.inl (92, 18)),
    Sum.inr (Sum.inl (92, 17)),
    Sum.inr (Sum.inl (73, 1)),
    Sum.inr (Sum.inl (230, 24)),
    Sum.inr (Sum.inl (156, 8)),
    Sum.inr (Sum.inl (156, 4)),
    Sum.inr (Sum.inl (230, 16)),
    Sum.inr (Sum.inl (176, 61)),
    Sum.inr (Sum.inl (111, 40)),
    Sum.inr (Sum.inl (111, 36)),
    Sum.inr (Sum.inl (176, 63)),
    Sum.inr (Sum.inl (107, 34)),
    Sum.inr (Sum.inl (54, 24)),
    Sum.inr (Sum.inl (54, 20)),
    Sum.inr (Sum.inl (107, 48)),
    Sum.inr (Sum.inl (73, 10)),
    Sum.inr (Sum.inl (92, 2)),
    Sum.inr (Sum.inl (92, 1)),
    Sum.inr (Sum.inl (73, 8)),
    Sum.inr (Sum.inl (176, 30)),
    Sum.inr (Sum.inl (111, 26)),
    Sum.inr (Sum.inl (111, 22)),
    Sum.inr (Sum.inl (176, 28)),
    Sum.inr (Sum.inl (230, 50)),
    Sum.inr (Sum.inl (156, 38)),
    Sum.inr (Sum.inl (156, 42)),
    Sum.inr (Sum.inl (230, 58)),
    Sum.inr (Sum.inl (73, 39)),
    Sum.inr (Sum.inl (92, 54)),
    Sum.inr (Sum.inl (92, 53)),
    Sum.inr (Sum.inl (73, 37)),
    Sum.inr (Sum.inl (107, 52)),
    Sum.inr (Sum.inl (54, 52)),
    Sum.inr (Sum.inl (54, 56)),
    Sum.inr (Sum.inl (107, 38)),
    Sum.inr (Sum.inl (176, 41)),
    Sum.inr (Sum.inl (111, 56)),
    Sum.inr (Sum.inl (111, 52)),
    Sum.inr (Sum.inl (176, 43)),
    Sum.inr (Sum.inl (230, 38)),
    Sum.inr (Sum.inl (156, 54)),
    Sum.inr (Sum.inl (156, 58)),
    Sum.inr (Sum.inl (230, 46)),
    Sum.inr (Sum.inl (73, 46)),
    Sum.inr (Sum.inl (92, 38)),
    Sum.inr (Sum.inl (92, 37)),
    Sum.inr (Sum.inl (73, 44)),
    Sum.inr (Sum.inl (107, 28)),
    Sum.inr (Sum.inl (54, 38)),
    Sum.inr (Sum.inl (54, 42)),
    Sum.inr (Sum.inl (107, 14)),
    Sum.inr (Sum.inl (229, 2)),
    Sum.inr (Sum.inl (189, 61)),
    Sum.inr (Sum.inl (198, 18)),
    Sum.inr (Sum.inl (95, 40)),
    Sum.inr (Sum.inl (136, 35)),
    Sum.inr (Sum.inl (65, 53)),
    Sum.inr (Sum.inl (49, 42)),
    Sum.inr (Sum.inl (93, 35)),
    Sum.inr (Sum.inl (229, 1)),
    Sum.inr (Sum.inl (189, 63)),
    Sum.inr (Sum.inl (198, 16)),
    Sum.inr (Sum.inl (95, 36)),
    Sum.inr (Sum.inl (136, 49)),
    Sum.inr (Sum.inl (65, 57)),
    Sum.inr (Sum.inl (49, 38)),
    Sum.inr (Sum.inl (93, 43)),
    Sum.inr (Sum.inl (198, 3)),
    Sum.inr (Sum.inl (95, 10)),
    Sum.inr (Sum.inl (229, 34)),
    Sum.inr (Sum.inl (189, 34)),
    Sum.inr (Sum.inl (49, 11)),
    Sum.inr (Sum.inl (93, 49)),
    Sum.inr (Sum.inl (136, 43)),
    Sum.inr (Sum.inl (65, 42)),
    Sum.inr (Sum.inl (198, 1)),
    Sum.inr (Sum.inl (95, 6)),
    Sum.inr (Sum.inl (229, 33)),
    Sum.inr (Sum.inl (189, 32)),
    Sum.inr (Sum.inl (49, 7)),
    Sum.inr (Sum.inl (93, 57)),
    Sum.inr (Sum.inl (136, 57)),
    Sum.inr (Sum.inl (65, 38)),
    Sum.inr (Sum.inl (189, 44)),
    Sum.inr (Sum.inl (229, 57)),
    Sum.inr (Sum.inl (95, 22)),
    Sum.inr (Sum.inl (198, 41)),
    Sum.inr (Sum.inl (65, 36)),
    Sum.inr (Sum.inl (136, 24)),
    Sum.inr (Sum.inl (93, 2)),
    Sum.inr (Sum.inl (49, 5)),
    Sum.inr (Sum.inl (189, 46)),
    Sum.inr (Sum.inl (229, 58)),
    Sum.inr (Sum.inl (95, 26)),
    Sum.inr (Sum.inl (198, 43)),
    Sum.inr (Sum.inl (65, 40)),
    Sum.inr (Sum.inl (136, 10)),
    Sum.inr (Sum.inl (93, 10)),
    Sum.inr (Sum.inl (49, 9)),
    Sum.inr (Sum.inl (95, 52)),
    Sum.inr (Sum.inl (198, 56)),
    Sum.inr (Sum.inl (189, 51)),
    Sum.inr (Sum.inl (229, 25)),
    Sum.inr (Sum.inl (93, 16)),
    Sum.inr (Sum.inl (49, 36)),
    Sum.inr (Sum.inl (65, 59)),
    Sum.inr (Sum.inl (136, 16)),
    Sum.inr (Sum.inl (95, 56)),
    Sum.inr (Sum.inl (198, 58)),
    Sum.inr (Sum.inl (189, 49)),
    Sum.inr (Sum.inl (229, 26)),
    Sum.inr (Sum.inl (93, 24)),
    Sum.inr (Sum.inl (49, 40)),
    Sum.inr (Sum.inl (65, 55)),
    Sum.inr (Sum.inl (136, 2)),
    Sum.inr (Sum.inl (228, 59)),
    Sum.inr (Sum.inl (180, 31)),
    Sum.inr (Sum.inl (180, 19)),
    Sum.inr (Sum.inl (228, 51)),
    Sum.inr (Sum.inl (228, 31)),
    Sum.inr (Sum.inl (180, 63)),
    Sum.inr (Sum.inl (180, 51)),
    Sum.inr (Sum.inl (228, 23)),
    Sum.inr (Sum.inl (160, 40)),
    Sum.inr (Sum.inl (96, 61)),
    Sum.inr (Sum.inl (96, 49)),
    Sum.inr (Sum.inl (160, 42)),
    Sum.inr (Sum.inl (160, 31)),
    Sum.inr (Sum.inl (96, 63)),
    Sum.inr (Sum.inl (96, 51)),
    Sum.inr (Sum.inl (160, 29)),
    Sum.inr (Sum.inl (122, 51)),
    Sum.inr (Sum.inl (69, 29)),
    Sum.inr (Sum.inl (69, 17)),
    Sum.inr (Sum.inl (122, 33)),
    Sum.inr (Sum.inl (122, 23)),
    Sum.inr (Sum.inl (69, 15)),
    Sum.inr (Sum.inl (69, 3)),
    Sum.inr (Sum.inl (122, 5)),
    Sum.inr (Sum.inl (50, 14)),
    Sum.inr (Sum.inl (94, 11)),
    Sum.inr (Sum.inl (94, 8)),
    Sum.inr (Sum.inl (50, 12)),
    Sum.inr (Sum.inl (50, 7)),
    Sum.inr (Sum.inl (94, 15)),
    Sum.inr (Sum.inl (94, 12)),
    Sum.inr (Sum.inl (50, 5)),
    Sum.inr (Sum.inl (160, 24)),
    Sum.inr (Sum.inl (96, 34)),
    Sum.inr (Sum.inl (96, 46)),
    Sum.inr (Sum.inl (160, 26)),
    Sum.inr (Sum.inl (160, 47)),
    Sum.inr (Sum.inl (96, 32)),
    Sum.inr (Sum.inl (96, 44)),
    Sum.inr (Sum.inl (160, 45)),
    Sum.inr (Sum.inl (228, 6)),
    Sum.inr (Sum.inl (180, 34)),
    Sum.inr (Sum.inl (180, 46)),
    Sum.inr (Sum.inl (228, 14)),
    Sum.inr (Sum.inl (228, 34)),
    Sum.inr (Sum.inl (180, 2)),
    Sum.inr (Sum.inl (180, 14)),
    Sum.inr (Sum.inl (228, 42)),
    Sum.inr (Sum.inl (50, 42)),
    Sum.inr (Sum.inl (94, 35)),
    Sum.inr (Sum.inl (94, 32)),
    Sum.inr (Sum.inl (50, 40)),
    Sum.inr (Sum.inl (50, 35)),
    Sum.inr (Sum.inl (94, 39)),
    Sum.inr (Sum.inl (94, 36)),
    Sum.inr (Sum.inl (50, 33)),
    Sum.inr (Sum.inl (122, 50)),
    Sum.inr (Sum.inl (69, 28)),
    Sum.inr (Sum.inl (69, 16)),
    Sum.inr (Sum.inl (122, 32)),
    Sum.inr (Sum.inl (122, 22)),
    Sum.inr (Sum.inl (69, 14)),
    Sum.inr (Sum.inl (69, 2)),
    Sum.inr (Sum.inl (122, 4)),
    Sum.inr (Sum.inl (136, 1)),
    Sum.inr (Sum.inl (189, 59)),
    Sum.inr (Sum.inl (198, 24)),
    Sum.inr (Sum.inl (93, 20)),
    Sum.inr (Sum.inl (229, 8)),
    Sum.inr (Sum.inl (65, 61)),
    Sum.inr (Sum.inl (49, 34)),
    Sum.inr (Sum.inl (95, 48)),
    Sum.inr (Sum.inl (229, 11)),
    Sum.inr (Sum.inl (65, 49)),
    Sum.inr (Sum.inl (49, 46)),
    Sum.inr (Sum.inl (95, 60)),
    Sum.inr (Sum.inl (136, 19)),
    Sum.inr (Sum.inl (189, 57)),
    Sum.inr (Sum.inl (198, 26)),
    Sum.inr (Sum.inl (93, 28)),
    Sum.inr (Sum.inl (136, 32)),
    Sum.inr (Sum.inl (189, 55)),
    Sum.inr (Sum.inl (198, 48)),
    Sum.inr (Sum.inl (93, 47)),
    Sum.inr (Sum.inl (229, 16)),
    Sum.inr (Sum.inl (65, 63)),
    Sum.inr (Sum.inl (49, 32)),
    Sum.inr (Sum.inl (95, 32))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock025Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨6400 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block025_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock025Input a
    let y := generatedSixthXiShortBlock025Output a
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
theorem generatedSixth_xi_short_block025_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock025Input a
    let y := generatedSixthXiShortBlock025Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block025_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block025_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock025Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block025_certificate a).1
    (generatedSixth_xi_short_block025_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
