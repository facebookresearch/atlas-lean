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
def generatedSixthXiShortBlock035Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (61, 27)),
    Sum.inr (Sum.inl (193, 27)),
    Sum.inr (Sum.inl (89, 9)),
    Sum.inr (Sum.inl (113, 3)),
    Sum.inr (Sum.inl (57, 30)),
    Sum.inr (Sum.inl (131, 23)),
    Sum.inr (Sum.inl (221, 9)),
    Sum.inr (Sum.inl (185, 5)),
    Sum.inr (Sum.inl (113, 18)),
    Sum.inr (Sum.inl (89, 24)),
    Sum.inr (Sum.inl (193, 58)),
    Sum.inr (Sum.inl (61, 58)),
    Sum.inr (Sum.inl (185, 62)),
    Sum.inr (Sum.inl (221, 55)),
    Sum.inr (Sum.inl (131, 44)),
    Sum.inr (Sum.inl (57, 37)),
    Sum.inr (Sum.inl (113, 41)),
    Sum.inr (Sum.inl (89, 58)),
    Sum.inr (Sum.inl (193, 62)),
    Sum.inr (Sum.inl (61, 62)),
    Sum.inr (Sum.inl (185, 44)),
    Sum.inr (Sum.inl (221, 21)),
    Sum.inr (Sum.inl (131, 36)),
    Sum.inr (Sum.inl (57, 4)),
    Sum.inr (Sum.inl (193, 34)),
    Sum.inr (Sum.inl (61, 40)),
    Sum.inr (Sum.inl (113, 26)),
    Sum.inr (Sum.inl (89, 28)),
    Sum.inr (Sum.inl (131, 62)),
    Sum.inr (Sum.inl (57, 55)),
    Sum.inr (Sum.inl (185, 54)),
    Sum.inr (Sum.inl (221, 35)),
    Sum.inr (Sum.inl (193, 38)),
    Sum.inr (Sum.inl (61, 44)),
    Sum.inr (Sum.inl (113, 33)),
    Sum.inr (Sum.inl (89, 62)),
    Sum.inr (Sum.inl (131, 54)),
    Sum.inr (Sum.inl (57, 22)),
    Sum.inr (Sum.inl (185, 36)),
    Sum.inr (Sum.inl (221, 1)),
    Sum.inr (Sum.inr (62, 15)),
    Sum.inr (Sum.inr (254, 1)),
    Sum.inr (Sum.inr (116, 15)),
    Sum.inr (Sum.inr (180, 1)),
    Sum.inr (Sum.inr (417, 15)),
    Sum.inr (Sum.inr (353, 1)),
    Sum.inr (Sum.inr (491, 15)),
    Sum.inr (Sum.inr (299, 1)),
    Sum.inr (Sum.inr (426, 15)),
    Sum.inr (Sum.inr (362, 1)),
    Sum.inr (Sum.inr (480, 15)),
    Sum.inr (Sum.inr (288, 1)),
    Sum.inr (Sum.inr (53, 15)),
    Sum.inr (Sum.inr (245, 1)),
    Sum.inr (Sum.inr (127, 15)),
    Sum.inr (Sum.inr (191, 1)),
    Sum.inr (Sum.inr (191, 15)),
    Sum.inr (Sum.inr (127, 1)),
    Sum.inr (Sum.inr (245, 15)),
    Sum.inr (Sum.inr (53, 1)),
    Sum.inr (Sum.inr (288, 15)),
    Sum.inr (Sum.inr (480, 1)),
    Sum.inr (Sum.inr (362, 15)),
    Sum.inr (Sum.inr (426, 1)),
    Sum.inr (Sum.inr (299, 15)),
    Sum.inr (Sum.inr (491, 1)),
    Sum.inr (Sum.inr (353, 15)),
    Sum.inr (Sum.inr (417, 1)),
    Sum.inr (Sum.inr (180, 15)),
    Sum.inr (Sum.inr (116, 1)),
    Sum.inr (Sum.inr (254, 15)),
    Sum.inr (Sum.inr (62, 1)),
    Sum.inr (Sum.inr (254, 11)),
    Sum.inr (Sum.inr (62, 22)),
    Sum.inr (Sum.inr (180, 11)),
    Sum.inr (Sum.inr (116, 22)),
    Sum.inr (Sum.inr (353, 11)),
    Sum.inr (Sum.inr (417, 22)),
    Sum.inr (Sum.inr (299, 11)),
    Sum.inr (Sum.inr (491, 22)),
    Sum.inr (Sum.inr (362, 11)),
    Sum.inr (Sum.inr (426, 22)),
    Sum.inr (Sum.inr (288, 11)),
    Sum.inr (Sum.inr (480, 22)),
    Sum.inr (Sum.inr (245, 11)),
    Sum.inr (Sum.inr (53, 22)),
    Sum.inr (Sum.inr (191, 11)),
    Sum.inr (Sum.inr (127, 22)),
    Sum.inr (Sum.inr (127, 11)),
    Sum.inr (Sum.inr (191, 22)),
    Sum.inr (Sum.inr (53, 11)),
    Sum.inr (Sum.inr (245, 22)),
    Sum.inr (Sum.inr (480, 11)),
    Sum.inr (Sum.inr (288, 22)),
    Sum.inr (Sum.inr (426, 11)),
    Sum.inr (Sum.inr (362, 22)),
    Sum.inr (Sum.inr (491, 11)),
    Sum.inr (Sum.inr (299, 22)),
    Sum.inr (Sum.inr (417, 11)),
    Sum.inr (Sum.inr (353, 22)),
    Sum.inr (Sum.inr (116, 11)),
    Sum.inr (Sum.inr (180, 22)),
    Sum.inr (Sum.inr (62, 11)),
    Sum.inr (Sum.inr (254, 22)),
    Sum.inr (Sum.inr (62, 8)),
    Sum.inr (Sum.inr (191, 0)),
    Sum.inr (Sum.inr (116, 8)),
    Sum.inr (Sum.inr (245, 0)),
    Sum.inr (Sum.inr (417, 8)),
    Sum.inr (Sum.inr (288, 0)),
    Sum.inr (Sum.inr (491, 8)),
    Sum.inr (Sum.inr (362, 0)),
    Sum.inr (Sum.inr (426, 8)),
    Sum.inr (Sum.inr (299, 0)),
    Sum.inr (Sum.inr (480, 8)),
    Sum.inr (Sum.inr (353, 0)),
    Sum.inr (Sum.inr (53, 8)),
    Sum.inr (Sum.inr (180, 0)),
    Sum.inr (Sum.inr (127, 8)),
    Sum.inr (Sum.inr (254, 0)),
    Sum.inr (Sum.inr (191, 13)),
    Sum.inr (Sum.inr (62, 23)),
    Sum.inr (Sum.inr (245, 13)),
    Sum.inr (Sum.inr (116, 23)),
    Sum.inr (Sum.inr (288, 13)),
    Sum.inr (Sum.inr (417, 23)),
    Sum.inr (Sum.inr (362, 13)),
    Sum.inr (Sum.inr (491, 23)),
    Sum.inr (Sum.inr (299, 13)),
    Sum.inr (Sum.inr (426, 23)),
    Sum.inr (Sum.inr (353, 13)),
    Sum.inr (Sum.inr (480, 23)),
    Sum.inr (Sum.inr (180, 13)),
    Sum.inr (Sum.inr (53, 23)),
    Sum.inr (Sum.inr (254, 13)),
    Sum.inr (Sum.inr (127, 23)),
    Sum.inr (Sum.inr (254, 8)),
    Sum.inr (Sum.inr (127, 0)),
    Sum.inr (Sum.inr (180, 8)),
    Sum.inr (Sum.inr (53, 0)),
    Sum.inr (Sum.inr (353, 8)),
    Sum.inr (Sum.inr (480, 0)),
    Sum.inr (Sum.inr (299, 8)),
    Sum.inr (Sum.inr (426, 0)),
    Sum.inr (Sum.inr (362, 8)),
    Sum.inr (Sum.inr (491, 0)),
    Sum.inr (Sum.inr (288, 8)),
    Sum.inr (Sum.inr (417, 0)),
    Sum.inr (Sum.inr (245, 8)),
    Sum.inr (Sum.inr (116, 0)),
    Sum.inr (Sum.inr (191, 8)),
    Sum.inr (Sum.inr (62, 0)),
    Sum.inr (Sum.inr (127, 13)),
    Sum.inr (Sum.inr (254, 23)),
    Sum.inr (Sum.inr (53, 13)),
    Sum.inr (Sum.inr (180, 23)),
    Sum.inr (Sum.inr (480, 13)),
    Sum.inr (Sum.inr (353, 23)),
    Sum.inr (Sum.inr (426, 13)),
    Sum.inr (Sum.inr (299, 23)),
    Sum.inr (Sum.inr (491, 13)),
    Sum.inr (Sum.inr (362, 23)),
    Sum.inr (Sum.inr (417, 13)),
    Sum.inr (Sum.inr (288, 23)),
    Sum.inr (Sum.inr (116, 13)),
    Sum.inr (Sum.inr (245, 23)),
    Sum.inr (Sum.inr (62, 13)),
    Sum.inr (Sum.inr (191, 23)),
    Sum.inr (Sum.inl (86, 36)),
    Sum.inr (Sum.inl (100, 36)),
    Sum.inr (Sum.inl (44, 54)),
    Sum.inr (Sum.inl (223, 56)),
    Sum.inr (Sum.inl (100, 33)),
    Sum.inr (Sum.inl (86, 59)),
    Sum.inr (Sum.inl (223, 41)),
    Sum.inr (Sum.inl (44, 25)),
    Sum.inr (Sum.inl (44, 48)),
    Sum.inr (Sum.inl (223, 48)),
    Sum.inr (Sum.inl (86, 52)),
    Sum.inr (Sum.inl (100, 52)),
    Sum.inr (Sum.inl (223, 33)),
    Sum.inr (Sum.inl (44, 31)),
    Sum.inr (Sum.inl (100, 49)),
    Sum.inr (Sum.inl (86, 43)),
    Sum.inr (Sum.inl (86, 34)),
    Sum.inr (Sum.inl (100, 59)),
    Sum.inr (Sum.inl (44, 22)),
    Sum.inr (Sum.inl (223, 28)),
    Sum.inr (Sum.inl (100, 62)),
    Sum.inr (Sum.inl (86, 61)),
    Sum.inr (Sum.inl (223, 13)),
    Sum.inr (Sum.inl (44, 57)),
    Sum.inr (Sum.inl (44, 16)),
    Sum.inr (Sum.inl (223, 20)),
    Sum.inr (Sum.inl (86, 50)),
    Sum.inr (Sum.inl (100, 43)),
    Sum.inr (Sum.inl (223, 5)),
    Sum.inr (Sum.inl (44, 63)),
    Sum.inr (Sum.inl (100, 46)),
    Sum.inr (Sum.inl (86, 45)),
    Sum.inr (Sum.inl (191, 6)),
    Sum.inr (Sum.inl (162, 12)),
    Sum.inr (Sum.inl (77, 30)),
    Sum.inr (Sum.inl (134, 30)),
    Sum.inr (Sum.inl (162, 9)),
    Sum.inr (Sum.inl (191, 59)),
    Sum.inr (Sum.inl (134, 27)),
    Sum.inr (Sum.inl (77, 49)),
    Sum.inr (Sum.inl (77, 20)),
    Sum.inr (Sum.inl (134, 20)),
    Sum.inr (Sum.inl (191, 23)),
    Sum.inr (Sum.inl (162, 28)),
    Sum.inr (Sum.inl (134, 17)),
    Sum.inr (Sum.inl (77, 59)),
    Sum.inr (Sum.inl (162, 25)),
    Sum.inr (Sum.inl (191, 42)),
    Sum.inr (Sum.inl (191, 34)),
    Sum.inr (Sum.inl (162, 6)),
    Sum.inr (Sum.inl (77, 27)),
    Sum.inr (Sum.inl (134, 14)),
    Sum.inr (Sum.inl (162, 3)),
    Sum.inr (Sum.inl (191, 31)),
    Sum.inr (Sum.inl (134, 11)),
    Sum.inr (Sum.inl (77, 52)),
    Sum.inr (Sum.inl (77, 17)),
    Sum.inr (Sum.inl (134, 4)),
    Sum.inr (Sum.inl (191, 51)),
    Sum.inr (Sum.inl (162, 22)),
    Sum.inr (Sum.inl (134, 1)),
    Sum.inr (Sum.inl (77, 62)),
    Sum.inr (Sum.inl (162, 19)),
    Sum.inr (Sum.inl (191, 14)),
    Sum.inr (Sum.inl (183, 55)),
    Sum.inr (Sum.inl (219, 35)),
    Sum.inr (Sum.inl (183, 59)),
    Sum.inr (Sum.inl (219, 43)),
    Sum.inr (Sum.inl (199, 57)),
    Sum.inr (Sum.inl (62, 5)),
    Sum.inr (Sum.inl (199, 43)),
    Sum.inr (Sum.inl (62, 9)),
    Sum.inr (Sum.inl (219, 55)),
    Sum.inr (Sum.inl (183, 39)),
    Sum.inr (Sum.inl (219, 63)),
    Sum.inr (Sum.inl (183, 43)),
    Sum.inr (Sum.inl (62, 39)),
    Sum.inr (Sum.inl (199, 17)),
    Sum.inr (Sum.inl (62, 43)),
    Sum.inr (Sum.inl (199, 3)),
    Sum.inr (Sum.inl (85, 34)),
    Sum.inr (Sum.inl (59, 37)),
    Sum.inr (Sum.inl (85, 32)),
    Sum.inr (Sum.inl (59, 41)),
    Sum.inr (Sum.inl (98, 25)),
    Sum.inr (Sum.inl (135, 16)),
    Sum.inr (Sum.inl (98, 26)),
    Sum.inr (Sum.inl (135, 18))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock035Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨8960 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block035_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock035Input a
    let y := generatedSixthXiShortBlock035Output a
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
theorem generatedSixth_xi_short_block035_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock035Input a
    let y := generatedSixthXiShortBlock035Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block035_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block035_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock035Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block035_certificate a).1
    (generatedSixth_xi_short_block035_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
