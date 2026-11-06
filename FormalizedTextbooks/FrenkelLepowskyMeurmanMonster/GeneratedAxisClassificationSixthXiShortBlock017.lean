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
def generatedSixthXiShortBlock017Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (62, 35)),
    Sum.inr (Sum.inl (62, 51)),
    Sum.inr (Sum.inl (183, 33)),
    Sum.inr (Sum.inl (183, 3)),
    Sum.inr (Sum.inl (219, 53)),
    Sum.inr (Sum.inl (219, 23)),
    Sum.inr (Sum.inl (199, 1)),
    Sum.inr (Sum.inl (199, 5)),
    Sum.inr (Sum.inl (85, 33)),
    Sum.inr (Sum.inl (85, 48)),
    Sum.inr (Sum.inl (135, 45)),
    Sum.inr (Sum.inl (135, 22)),
    Sum.inr (Sum.inl (98, 36)),
    Sum.inr (Sum.inl (98, 31)),
    Sum.inr (Sum.inl (59, 44)),
    Sum.inr (Sum.inl (59, 45)),
    Sum.inr (Sum.inl (98, 39)),
    Sum.inr (Sum.inl (98, 28)),
    Sum.inr (Sum.inl (59, 32)),
    Sum.inr (Sum.inl (59, 33)),
    Sum.inr (Sum.inl (85, 35)),
    Sum.inr (Sum.inl (85, 50)),
    Sum.inr (Sum.inl (135, 47)),
    Sum.inr (Sum.inl (135, 20)),
    Sum.inr (Sum.inl (135, 36)),
    Sum.inr (Sum.inl (135, 31)),
    Sum.inr (Sum.inl (85, 22)),
    Sum.inr (Sum.inl (85, 7)),
    Sum.inr (Sum.inl (59, 62)),
    Sum.inr (Sum.inl (59, 63)),
    Sum.inr (Sum.inl (98, 52)),
    Sum.inr (Sum.inl (98, 15)),
    Sum.inr (Sum.inl (59, 50)),
    Sum.inr (Sum.inl (59, 51)),
    Sum.inr (Sum.inl (98, 55)),
    Sum.inr (Sum.inl (98, 12)),
    Sum.inr (Sum.inl (135, 38)),
    Sum.inr (Sum.inl (135, 29)),
    Sum.inr (Sum.inl (85, 20)),
    Sum.inr (Sum.inl (85, 5)),
    Sum.inr (Sum.inl (116, 0)),
    Sum.inr (Sum.inl (163, 0)),
    Sum.inr (Sum.inl (116, 12)),
    Sum.inr (Sum.inl (163, 59)),
    Sum.inr (Sum.inl (129, 0)),
    Sum.inr (Sum.inl (202, 0)),
    Sum.inr (Sum.inl (129, 2)),
    Sum.inr (Sum.inl (202, 32)),
    Sum.inr (Sum.inl (129, 12)),
    Sum.inr (Sum.inl (202, 12)),
    Sum.inr (Sum.inl (129, 14)),
    Sum.inr (Sum.inl (202, 44)),
    Sum.inr (Sum.inl (116, 2)),
    Sum.inr (Sum.inl (163, 8)),
    Sum.inr (Sum.inl (116, 14)),
    Sum.inr (Sum.inl (163, 51)),
    Sum.inr (Sum.inl (163, 18)),
    Sum.inr (Sum.inl (116, 47)),
    Sum.inr (Sum.inl (163, 41)),
    Sum.inr (Sum.inl (116, 35)),
    Sum.inr (Sum.inl (202, 18)),
    Sum.inr (Sum.inl (129, 47)),
    Sum.inr (Sum.inl (202, 50)),
    Sum.inr (Sum.inl (129, 45)),
    Sum.inr (Sum.inl (202, 30)),
    Sum.inr (Sum.inl (129, 35)),
    Sum.inr (Sum.inl (202, 62)),
    Sum.inr (Sum.inl (129, 33)),
    Sum.inr (Sum.inl (163, 26)),
    Sum.inr (Sum.inl (116, 45)),
    Sum.inr (Sum.inl (163, 33)),
    Sum.inr (Sum.inl (116, 33)),
    Sum.inr (Sum.inl (56, 0)),
    Sum.inr (Sum.inl (222, 0)),
    Sum.inr (Sum.inl (56, 33)),
    Sum.inr (Sum.inl (222, 40)),
    Sum.inr (Sum.inl (105, 0)),
    Sum.inr (Sum.inl (60, 0)),
    Sum.inr (Sum.inl (105, 20)),
    Sum.inr (Sum.inl (60, 2)),
    Sum.inr (Sum.inl (105, 3)),
    Sum.inr (Sum.inl (60, 12)),
    Sum.inr (Sum.inl (105, 23)),
    Sum.inr (Sum.inl (60, 14)),
    Sum.inr (Sum.inl (56, 18)),
    Sum.inr (Sum.inl (222, 2)),
    Sum.inr (Sum.inl (56, 51)),
    Sum.inr (Sum.inl (222, 42)),
    Sum.inr (Sum.inl (222, 5)),
    Sum.inr (Sum.inl (56, 8)),
    Sum.inr (Sum.inl (222, 45)),
    Sum.inr (Sum.inl (56, 41)),
    Sum.inr (Sum.inl (60, 17)),
    Sum.inr (Sum.inl (105, 32)),
    Sum.inr (Sum.inl (60, 19)),
    Sum.inr (Sum.inl (105, 52)),
    Sum.inr (Sum.inl (60, 29)),
    Sum.inr (Sum.inl (105, 35)),
    Sum.inr (Sum.inl (60, 31)),
    Sum.inr (Sum.inl (105, 55)),
    Sum.inr (Sum.inl (222, 7)),
    Sum.inr (Sum.inl (56, 26)),
    Sum.inr (Sum.inl (222, 47)),
    Sum.inr (Sum.inl (56, 59)),
    Sum.inr (Sum.inl (185, 0)),
    Sum.inr (Sum.inl (113, 0)),
    Sum.inr (Sum.inl (131, 18)),
    Sum.inr (Sum.inl (193, 24)),
    Sum.inr (Sum.inl (185, 18)),
    Sum.inr (Sum.inl (113, 59)),
    Sum.inr (Sum.inl (131, 26)),
    Sum.inr (Sum.inl (193, 28)),
    Sum.inr (Sum.inl (221, 0)),
    Sum.inr (Sum.inl (89, 0)),
    Sum.inr (Sum.inl (57, 18)),
    Sum.inr (Sum.inl (61, 18)),
    Sum.inr (Sum.inl (221, 34)),
    Sum.inr (Sum.inl (89, 34)),
    Sum.inr (Sum.inl (57, 51)),
    Sum.inr (Sum.inl (61, 22)),
    Sum.inr (Sum.inl (131, 0)),
    Sum.inr (Sum.inl (193, 0)),
    Sum.inr (Sum.inl (185, 8)),
    Sum.inr (Sum.inl (113, 8)),
    Sum.inr (Sum.inl (131, 8)),
    Sum.inr (Sum.inl (193, 4)),
    Sum.inr (Sum.inl (185, 26)),
    Sum.inr (Sum.inl (113, 51)),
    Sum.inr (Sum.inl (57, 0)),
    Sum.inr (Sum.inl (61, 0)),
    Sum.inr (Sum.inl (221, 20)),
    Sum.inr (Sum.inl (89, 4)),
    Sum.inr (Sum.inl (57, 33)),
    Sum.inr (Sum.inl (61, 4)),
    Sum.inr (Sum.inl (221, 54)),
    Sum.inr (Sum.inl (89, 38)),
    Sum.inr (Sum.inl (113, 17)),
    Sum.inr (Sum.inl (185, 59)),
    Sum.inr (Sum.inl (193, 57)),
    Sum.inr (Sum.inl (131, 41)),
    Sum.inr (Sum.inl (113, 42)),
    Sum.inr (Sum.inl (185, 41)),
    Sum.inr (Sum.inl (193, 61)),
    Sum.inr (Sum.inl (131, 33)),
    Sum.inr (Sum.inl (89, 17)),
    Sum.inr (Sum.inl (221, 62)),
    Sum.inr (Sum.inl (61, 51)),
    Sum.inr (Sum.inl (57, 41)),
    Sum.inr (Sum.inl (89, 51)),
    Sum.inr (Sum.inl (221, 28)),
    Sum.inr (Sum.inl (61, 55)),
    Sum.inr (Sum.inl (57, 8)),
    Sum.inr (Sum.inl (193, 33)),
    Sum.inr (Sum.inl (131, 59)),
    Sum.inr (Sum.inl (113, 25)),
    Sum.inr (Sum.inl (185, 51)),
    Sum.inr (Sum.inl (193, 37)),
    Sum.inr (Sum.inl (131, 51)),
    Sum.inr (Sum.inl (113, 34)),
    Sum.inr (Sum.inl (185, 33)),
    Sum.inr (Sum.inl (61, 33)),
    Sum.inr (Sum.inl (57, 59)),
    Sum.inr (Sum.inl (89, 21)),
    Sum.inr (Sum.inl (221, 42)),
    Sum.inr (Sum.inl (61, 37)),
    Sum.inr (Sum.inl (57, 26)),
    Sum.inr (Sum.inl (89, 55)),
    Sum.inr (Sum.inl (221, 8)),
    Sum.inr (Sum.inl (85, 0)),
    Sum.inr (Sum.inl (199, 0)),
    Sum.inr (Sum.inl (135, 9)),
    Sum.inr (Sum.inl (219, 20)),
    Sum.inr (Sum.inl (98, 0)),
    Sum.inr (Sum.inl (183, 0)),
    Sum.inr (Sum.inl (59, 18)),
    Sum.inr (Sum.inl (62, 34)),
    Sum.inr (Sum.inl (98, 3)),
    Sum.inr (Sum.inl (183, 12)),
    Sum.inr (Sum.inl (59, 30)),
    Sum.inr (Sum.inl (62, 46)),
    Sum.inr (Sum.inl (85, 2)),
    Sum.inr (Sum.inl (199, 18)),
    Sum.inr (Sum.inl (135, 11)),
    Sum.inr (Sum.inl (219, 28)),
    Sum.inr (Sum.inl (85, 17)),
    Sum.inr (Sum.inl (199, 4)),
    Sum.inr (Sum.inl (135, 50)),
    Sum.inr (Sum.inl (219, 54)),
    Sum.inr (Sum.inl (98, 59)),
    Sum.inr (Sum.inl (183, 34)),
    Sum.inr (Sum.inl (59, 19)),
    Sum.inr (Sum.inl (62, 50)),
    Sum.inr (Sum.inl (98, 56)),
    Sum.inr (Sum.inl (183, 46)),
    Sum.inr (Sum.inl (59, 31)),
    Sum.inr (Sum.inl (62, 62)),
    Sum.inr (Sum.inl (85, 19)),
    Sum.inr (Sum.inl (199, 22)),
    Sum.inr (Sum.inl (135, 48)),
    Sum.inr (Sum.inl (219, 62)),
    Sum.inr (Sum.inl (135, 0)),
    Sum.inr (Sum.inl (219, 0)),
    Sum.inr (Sum.inl (85, 55)),
    Sum.inr (Sum.inl (199, 40)),
    Sum.inr (Sum.inl (59, 0)),
    Sum.inr (Sum.inl (62, 0)),
    Sum.inr (Sum.inl (98, 16)),
    Sum.inr (Sum.inl (183, 16)),
    Sum.inr (Sum.inl (59, 12)),
    Sum.inr (Sum.inl (62, 12)),
    Sum.inr (Sum.inl (98, 19)),
    Sum.inr (Sum.inl (183, 28)),
    Sum.inr (Sum.inl (135, 2)),
    Sum.inr (Sum.inl (219, 8)),
    Sum.inr (Sum.inl (85, 53)),
    Sum.inr (Sum.inl (199, 58)),
    Sum.inr (Sum.inl (135, 59)),
    Sum.inr (Sum.inl (219, 34)),
    Sum.inr (Sum.inl (85, 38)),
    Sum.inr (Sum.inl (199, 44)),
    Sum.inr (Sum.inl (59, 1)),
    Sum.inr (Sum.inl (62, 16)),
    Sum.inr (Sum.inl (98, 43)),
    Sum.inr (Sum.inl (183, 50)),
    Sum.inr (Sum.inl (59, 13)),
    Sum.inr (Sum.inl (62, 28)),
    Sum.inr (Sum.inl (98, 40)),
    Sum.inr (Sum.inl (183, 62)),
    Sum.inr (Sum.inl (135, 57)),
    Sum.inr (Sum.inl (219, 42)),
    Sum.inr (Sum.inl (85, 36)),
    Sum.inr (Sum.inl (199, 62)),
    Sum.inr (Sum.inl (58, 0)),
    Sum.inr (Sum.inl (102, 0)),
    Sum.inr (Sum.inl (102, 12)),
    Sum.inr (Sum.inl (58, 8)),
    Sum.inr (Sum.inl (121, 0)),
    Sum.inr (Sum.inl (84, 0)),
    Sum.inr (Sum.inl (84, 12)),
    Sum.inr (Sum.inl (121, 2)),
    Sum.inr (Sum.inl (58, 36)),
    Sum.inr (Sum.inl (102, 16)),
    Sum.inr (Sum.inl (102, 28)),
    Sum.inr (Sum.inl (58, 44)),
    Sum.inr (Sum.inl (121, 55)),
    Sum.inr (Sum.inl (84, 61)),
    Sum.inr (Sum.inl (84, 49)),
    Sum.inr (Sum.inl (121, 53)),
    Sum.inr (Sum.inl (121, 36)),
    Sum.inr (Sum.inl (84, 16)),
    Sum.inr (Sum.inl (84, 28)),
    Sum.inr (Sum.inl (121, 38)),
    Sum.inr (Sum.inl (58, 62)),
    Sum.inr (Sum.inl (102, 62)),
    Sum.inr (Sum.inl (102, 50)),
    Sum.inr (Sum.inl (58, 54))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock017Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨4352 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block017_combined_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock017Input a
    let y := generatedSixthXiShortBlock017Output a
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
theorem generatedSixth_xi_short_block017_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock017Input a
    let y := generatedSixthXiShortBlock017Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block017_combined_certificate a
  simpa only [generatedSixth_xi_combined_mask_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block017_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock017Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block017_certificate a).1
    (generatedSixth_xi_short_block017_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
