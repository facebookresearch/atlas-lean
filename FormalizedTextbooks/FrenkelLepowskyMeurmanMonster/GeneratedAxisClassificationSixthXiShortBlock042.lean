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
def generatedSixthXiShortBlock042Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (181, 61)),
    Sum.inr (Sum.inl (51, 8)),
    Sum.inr (Sum.inl (51, 4)),
    Sum.inr (Sum.inl (181, 63)),
    Sum.inr (Sum.inl (109, 21)),
    Sum.inr (Sum.inl (79, 53)),
    Sum.inr (Sum.inl (79, 57)),
    Sum.inr (Sum.inl (109, 29)),
    Sum.inr (Sum.inl (227, 6)),
    Sum.inr (Sum.inl (137, 10)),
    Sum.inr (Sum.inl (137, 6)),
    Sum.inr (Sum.inl (227, 20)),
    Sum.inr (Sum.inl (68, 23)),
    Sum.inr (Sum.inl (159, 30)),
    Sum.inr (Sum.inl (159, 29)),
    Sum.inr (Sum.inl (68, 21)),
    Sum.inr (Sum.inl (227, 34)),
    Sum.inr (Sum.inl (137, 24)),
    Sum.inr (Sum.inl (137, 20)),
    Sum.inr (Sum.inl (227, 48)),
    Sum.inr (Sum.inl (68, 30)),
    Sum.inr (Sum.inl (159, 22)),
    Sum.inr (Sum.inl (159, 21)),
    Sum.inr (Sum.inl (68, 28)),
    Sum.inr (Sum.inl (68, 3)),
    Sum.inr (Sum.inl (159, 10)),
    Sum.inr (Sum.inl (159, 9)),
    Sum.inr (Sum.inl (68, 1)),
    Sum.inr (Sum.inl (227, 7)),
    Sum.inr (Sum.inl (137, 11)),
    Sum.inr (Sum.inl (137, 7)),
    Sum.inr (Sum.inl (227, 21)),
    Sum.inr (Sum.inl (68, 10)),
    Sum.inr (Sum.inl (159, 2)),
    Sum.inr (Sum.inl (159, 1)),
    Sum.inr (Sum.inl (68, 8)),
    Sum.inr (Sum.inl (227, 35)),
    Sum.inr (Sum.inl (137, 25)),
    Sum.inr (Sum.inl (137, 21)),
    Sum.inr (Sum.inl (227, 49)),
    Sum.inr (Sum.inl (69, 42)),
    Sum.inr (Sum.inl (228, 35)),
    Sum.inr (Sum.inl (69, 38)),
    Sum.inr (Sum.inl (228, 43)),
    Sum.inr (Sum.inl (228, 50)),
    Sum.inr (Sum.inl (69, 53)),
    Sum.inr (Sum.inl (228, 58)),
    Sum.inr (Sum.inl (69, 57)),
    Sum.inr (Sum.inl (122, 42)),
    Sum.inr (Sum.inl (180, 39)),
    Sum.inr (Sum.inl (122, 56)),
    Sum.inr (Sum.inl (180, 43)),
    Sum.inr (Sum.inl (180, 54)),
    Sum.inr (Sum.inl (122, 29)),
    Sum.inr (Sum.inl (180, 58)),
    Sum.inr (Sum.inl (122, 15)),
    Sum.inr (Sum.inl (50, 51)),
    Sum.inr (Sum.inl (96, 37)),
    Sum.inr (Sum.inl (50, 49)),
    Sum.inr (Sum.inl (96, 41)),
    Sum.inr (Sum.inl (96, 52)),
    Sum.inr (Sum.inl (50, 28)),
    Sum.inr (Sum.inl (96, 56)),
    Sum.inr (Sum.inl (50, 30)),
    Sum.inr (Sum.inl (94, 50)),
    Sum.inr (Sum.inl (160, 25)),
    Sum.inr (Sum.inl (94, 49)),
    Sum.inr (Sum.inl (160, 27)),
    Sum.inr (Sum.inl (160, 28)),
    Sum.inr (Sum.inl (94, 29)),
    Sum.inr (Sum.inl (160, 30)),
    Sum.inr (Sum.inl (94, 30)),
    Sum.inr (Sum.inl (50, 23)),
    Sum.inr (Sum.inl (96, 58)),
    Sum.inr (Sum.inl (50, 21)),
    Sum.inr (Sum.inl (96, 54)),
    Sum.inr (Sum.inl (96, 43)),
    Sum.inr (Sum.inl (50, 56)),
    Sum.inr (Sum.inl (96, 39)),
    Sum.inr (Sum.inl (50, 58)),
    Sum.inr (Sum.inl (94, 26)),
    Sum.inr (Sum.inl (160, 41)),
    Sum.inr (Sum.inl (94, 25)),
    Sum.inr (Sum.inl (160, 43)),
    Sum.inr (Sum.inl (160, 44)),
    Sum.inr (Sum.inl (94, 53)),
    Sum.inr (Sum.inl (160, 46)),
    Sum.inr (Sum.inl (94, 54)),
    Sum.inr (Sum.inl (69, 43)),
    Sum.inr (Sum.inl (228, 30)),
    Sum.inr (Sum.inl (69, 39)),
    Sum.inr (Sum.inl (228, 22)),
    Sum.inr (Sum.inl (228, 15)),
    Sum.inr (Sum.inl (69, 52)),
    Sum.inr (Sum.inl (228, 7)),
    Sum.inr (Sum.inl (69, 56)),
    Sum.inr (Sum.inl (122, 43)),
    Sum.inr (Sum.inl (180, 26)),
    Sum.inr (Sum.inl (122, 57)),
    Sum.inr (Sum.inl (180, 22)),
    Sum.inr (Sum.inl (180, 11)),
    Sum.inr (Sum.inl (122, 28)),
    Sum.inr (Sum.inl (180, 7)),
    Sum.inr (Sum.inl (122, 14)),
    Sum.inr (Sum.inl (84, 8)),
    Sum.inr (Sum.inl (220, 23)),
    Sum.inr (Sum.inl (192, 23)),
    Sum.inr (Sum.inl (58, 63)),
    Sum.inr (Sum.inl (63, 5)),
    Sum.inr (Sum.inl (102, 39)),
    Sum.inr (Sum.inl (121, 23)),
    Sum.inr (Sum.inl (161, 3)),
    Sum.inr (Sum.inl (84, 41)),
    Sum.inr (Sum.inl (220, 55)),
    Sum.inr (Sum.inl (192, 8)),
    Sum.inr (Sum.inl (58, 45)),
    Sum.inr (Sum.inl (63, 26)),
    Sum.inr (Sum.inl (102, 5)),
    Sum.inr (Sum.inl (121, 6)),
    Sum.inr (Sum.inl (161, 11)),
    Sum.inr (Sum.inl (192, 21)),
    Sum.inr (Sum.inl (58, 55)),
    Sum.inr (Sum.inl (84, 4)),
    Sum.inr (Sum.inl (220, 27)),
    Sum.inr (Sum.inl (121, 21)),
    Sum.inr (Sum.inl (161, 17)),
    Sum.inr (Sum.inl (63, 6)),
    Sum.inr (Sum.inl (102, 43)),
    Sum.inr (Sum.inl (192, 10)),
    Sum.inr (Sum.inl (58, 37)),
    Sum.inr (Sum.inl (84, 37)),
    Sum.inr (Sum.inl (220, 59)),
    Sum.inr (Sum.inl (121, 4)),
    Sum.inr (Sum.inl (161, 25)),
    Sum.inr (Sum.inl (63, 25)),
    Sum.inr (Sum.inl (102, 9)),
    Sum.inr (Sum.inl (63, 13)),
    Sum.inr (Sum.inl (102, 55)),
    Sum.inr (Sum.inl (121, 32)),
    Sum.inr (Sum.inl (161, 39)),
    Sum.inr (Sum.inl (84, 53)),
    Sum.inr (Sum.inl (220, 5)),
    Sum.inr (Sum.inl (192, 6)),
    Sum.inr (Sum.inl (58, 27)),
    Sum.inr (Sum.inl (63, 18)),
    Sum.inr (Sum.inl (102, 21)),
    Sum.inr (Sum.inl (121, 49)),
    Sum.inr (Sum.inl (161, 47)),
    Sum.inr (Sum.inl (84, 20)),
    Sum.inr (Sum.inl (220, 37)),
    Sum.inr (Sum.inl (192, 25)),
    Sum.inr (Sum.inl (58, 9)),
    Sum.inr (Sum.inl (121, 34)),
    Sum.inr (Sum.inl (161, 53)),
    Sum.inr (Sum.inl (63, 14)),
    Sum.inr (Sum.inl (102, 59)),
    Sum.inr (Sum.inl (192, 4)),
    Sum.inr (Sum.inl (58, 19)),
    Sum.inr (Sum.inl (84, 57)),
    Sum.inr (Sum.inl (220, 9)),
    Sum.inr (Sum.inl (121, 51)),
    Sum.inr (Sum.inl (161, 61)),
    Sum.inr (Sum.inl (63, 17)),
    Sum.inr (Sum.inl (102, 25)),
    Sum.inr (Sum.inl (192, 27)),
    Sum.inr (Sum.inl (58, 1)),
    Sum.inr (Sum.inl (84, 24)),
    Sum.inr (Sum.inl (220, 41)),
    Sum.inr (Sum.inl (44, 18)),
    Sum.inr (Sum.inl (100, 20)),
    Sum.inr (Sum.inl (86, 48)),
    Sum.inr (Sum.inl (223, 24)),
    Sum.inr (Sum.inl (100, 17)),
    Sum.inr (Sum.inl (44, 61)),
    Sum.inr (Sum.inl (223, 9)),
    Sum.inr (Sum.inl (86, 47)),
    Sum.inr (Sum.inl (86, 54)),
    Sum.inr (Sum.inl (223, 60)),
    Sum.inr (Sum.inl (44, 50)),
    Sum.inr (Sum.inl (100, 11)),
    Sum.inr (Sum.inl (223, 45)),
    Sum.inr (Sum.inl (86, 41)),
    Sum.inr (Sum.inl (100, 14)),
    Sum.inr (Sum.inl (44, 29)),
    Sum.inr (Sum.inl (44, 20)),
    Sum.inr (Sum.inl (100, 4)),
    Sum.inr (Sum.inl (86, 32)),
    Sum.inr (Sum.inl (223, 16)),
    Sum.inr (Sum.inl (100, 1)),
    Sum.inr (Sum.inl (44, 59)),
    Sum.inr (Sum.inl (223, 1)),
    Sum.inr (Sum.inl (86, 63)),
    Sum.inr (Sum.inl (86, 38)),
    Sum.inr (Sum.inl (223, 52)),
    Sum.inr (Sum.inl (44, 52)),
    Sum.inr (Sum.inl (100, 27)),
    Sum.inr (Sum.inl (223, 37)),
    Sum.inr (Sum.inl (86, 57)),
    Sum.inr (Sum.inl (100, 30)),
    Sum.inr (Sum.inl (44, 27)),
    Sum.inr (Sum.inl (191, 3)),
    Sum.inr (Sum.inl (134, 6)),
    Sum.inr (Sum.inl (77, 18)),
    Sum.inr (Sum.inl (162, 20)),
    Sum.inr (Sum.inl (134, 3)),
    Sum.inr (Sum.inl (191, 62)),
    Sum.inr (Sum.inl (162, 17)),
    Sum.inr (Sum.inl (77, 61)),
    Sum.inr (Sum.inl (77, 23)),
    Sum.inr (Sum.inl (162, 30)),
    Sum.inr (Sum.inl (191, 39)),
    Sum.inr (Sum.inl (134, 22)),
    Sum.inr (Sum.inl (162, 27)),
    Sum.inr (Sum.inl (77, 56)),
    Sum.inr (Sum.inl (134, 19)),
    Sum.inr (Sum.inl (191, 26)),
    Sum.inr (Sum.inl (191, 18)),
    Sum.inr (Sum.inl (134, 12)),
    Sum.inr (Sum.inl (77, 24)),
    Sum.inr (Sum.inl (162, 4)),
    Sum.inr (Sum.inl (134, 9)),
    Sum.inr (Sum.inl (191, 47)),
    Sum.inr (Sum.inl (162, 1)),
    Sum.inr (Sum.inl (77, 55)),
    Sum.inr (Sum.inl (77, 29)),
    Sum.inr (Sum.inl (162, 14)),
    Sum.inr (Sum.inl (191, 54)),
    Sum.inr (Sum.inl (134, 28)),
    Sum.inr (Sum.inl (162, 11)),
    Sum.inr (Sum.inl (77, 50)),
    Sum.inr (Sum.inl (134, 25)),
    Sum.inr (Sum.inl (191, 11)),
    Sum.inr (Sum.inl (105, 61)),
    Sum.inr (Sum.inl (116, 34)),
    Sum.inr (Sum.inl (222, 61)),
    Sum.inr (Sum.inl (202, 55)),
    Sum.inr (Sum.inl (56, 28)),
    Sum.inr (Sum.inl (129, 42)),
    Sum.inr (Sum.inl (60, 53)),
    Sum.inr (Sum.inl (163, 19)),
    Sum.inr (Sum.inl (105, 62)),
    Sum.inr (Sum.inl (116, 32)),
    Sum.inr (Sum.inl (222, 63)),
    Sum.inr (Sum.inl (202, 59)),
    Sum.inr (Sum.inl (56, 14)),
    Sum.inr (Sum.inl (129, 38)),
    Sum.inr (Sum.inl (60, 57)),
    Sum.inr (Sum.inl (163, 27)),
    Sum.inr (Sum.inl (222, 56)),
    Sum.inr (Sum.inl (202, 37)),
    Sum.inr (Sum.inl (105, 29)),
    Sum.inr (Sum.inl (116, 13)),
    Sum.inr (Sum.inl (60, 36)),
    Sum.inr (Sum.inl (163, 1)),
    Sum.inr (Sum.inl (56, 20)),
    Sum.inr (Sum.inl (129, 5))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock042Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨10752 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block042_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock042Input a
    let y := generatedSixthXiShortBlock042Output a
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
theorem generatedSixth_xi_short_block042_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock042Input a
    let y := generatedSixthXiShortBlock042Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block042_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block042_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock042Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block042_certificate a).1
    (generatedSixth_xi_short_block042_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
