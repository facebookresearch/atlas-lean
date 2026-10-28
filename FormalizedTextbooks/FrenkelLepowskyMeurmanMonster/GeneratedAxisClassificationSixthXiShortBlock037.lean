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
def generatedSixthXiShortBlock037Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (177, 52)),
    Sum.inr (Sum.inl (177, 28)),
    Sum.inr (Sum.inl (139, 16)),
    Sum.inr (Sum.inl (139, 17)),
    Sum.inr (Sum.inl (225, 44)),
    Sum.inr (Sum.inl (225, 45)),
    Sum.inr (Sum.inl (55, 36)),
    Sum.inr (Sum.inl (55, 12)),
    Sum.inr (Sum.inl (124, 34)),
    Sum.inr (Sum.inl (124, 31)),
    Sum.inr (Sum.inl (155, 35)),
    Sum.inr (Sum.inl (155, 7)),
    Sum.inr (Sum.inl (72, 16)),
    Sum.inr (Sum.inl (72, 63)),
    Sum.inr (Sum.inl (78, 50)),
    Sum.inr (Sum.inl (78, 15)),
    Sum.inr (Sum.inl (72, 28)),
    Sum.inr (Sum.inl (72, 51)),
    Sum.inr (Sum.inl (78, 62)),
    Sum.inr (Sum.inl (78, 3)),
    Sum.inr (Sum.inl (124, 42)),
    Sum.inr (Sum.inl (124, 23)),
    Sum.inr (Sum.inl (155, 33)),
    Sum.inr (Sum.inl (155, 5)),
    Sum.inr (Sum.inl (55, 55)),
    Sum.inr (Sum.inl (55, 31)),
    Sum.inr (Sum.inl (225, 22)),
    Sum.inr (Sum.inl (225, 23)),
    Sum.inr (Sum.inl (139, 62)),
    Sum.inr (Sum.inl (139, 63)),
    Sum.inr (Sum.inl (177, 39)),
    Sum.inr (Sum.inl (177, 15)),
    Sum.inr (Sum.inl (139, 50)),
    Sum.inr (Sum.inl (139, 51)),
    Sum.inr (Sum.inl (177, 36)),
    Sum.inr (Sum.inl (177, 12)),
    Sum.inr (Sum.inl (55, 53)),
    Sum.inr (Sum.inl (55, 29)),
    Sum.inr (Sum.inl (225, 4)),
    Sum.inr (Sum.inl (225, 5)),
    Sum.inr (Sum.inr (216, 9)),
    Sum.inr (Sum.inr (19, 9)),
    Sum.inr (Sum.inr (146, 2)),
    Sum.inr (Sum.inr (89, 2)),
    Sum.inr (Sum.inr (262, 9)),
    Sum.inr (Sum.inr (461, 9)),
    Sum.inr (Sum.inr (332, 2)),
    Sum.inr (Sum.inr (391, 2)),
    Sum.inr (Sum.inr (269, 9)),
    Sum.inr (Sum.inr (454, 9)),
    Sum.inr (Sum.inr (327, 2)),
    Sum.inr (Sum.inr (396, 2)),
    Sum.inr (Sum.inr (211, 9)),
    Sum.inr (Sum.inr (24, 9)),
    Sum.inr (Sum.inr (153, 2)),
    Sum.inr (Sum.inr (82, 2)),
    Sum.inr (Sum.inr (146, 14)),
    Sum.inr (Sum.inr (89, 14)),
    Sum.inr (Sum.inr (216, 21)),
    Sum.inr (Sum.inr (19, 21)),
    Sum.inr (Sum.inr (332, 14)),
    Sum.inr (Sum.inr (391, 14)),
    Sum.inr (Sum.inr (262, 21)),
    Sum.inr (Sum.inr (461, 21)),
    Sum.inr (Sum.inr (327, 14)),
    Sum.inr (Sum.inr (396, 14)),
    Sum.inr (Sum.inr (269, 21)),
    Sum.inr (Sum.inr (454, 21)),
    Sum.inr (Sum.inr (153, 14)),
    Sum.inr (Sum.inr (82, 14)),
    Sum.inr (Sum.inr (211, 21)),
    Sum.inr (Sum.inr (24, 21)),
    Sum.inr (Sum.inr (82, 9)),
    Sum.inr (Sum.inr (153, 9)),
    Sum.inr (Sum.inr (24, 2)),
    Sum.inr (Sum.inr (211, 2)),
    Sum.inr (Sum.inr (396, 9)),
    Sum.inr (Sum.inr (327, 9)),
    Sum.inr (Sum.inr (454, 2)),
    Sum.inr (Sum.inr (269, 2)),
    Sum.inr (Sum.inr (391, 9)),
    Sum.inr (Sum.inr (332, 9)),
    Sum.inr (Sum.inr (461, 2)),
    Sum.inr (Sum.inr (262, 2)),
    Sum.inr (Sum.inr (89, 9)),
    Sum.inr (Sum.inr (146, 9)),
    Sum.inr (Sum.inr (19, 2)),
    Sum.inr (Sum.inr (216, 2)),
    Sum.inr (Sum.inr (24, 14)),
    Sum.inr (Sum.inr (211, 14)),
    Sum.inr (Sum.inr (82, 21)),
    Sum.inr (Sum.inr (153, 21)),
    Sum.inr (Sum.inr (454, 14)),
    Sum.inr (Sum.inr (269, 14)),
    Sum.inr (Sum.inr (396, 21)),
    Sum.inr (Sum.inr (327, 21)),
    Sum.inr (Sum.inr (461, 14)),
    Sum.inr (Sum.inr (262, 14)),
    Sum.inr (Sum.inr (391, 21)),
    Sum.inr (Sum.inr (332, 21)),
    Sum.inr (Sum.inr (19, 14)),
    Sum.inr (Sum.inr (216, 14)),
    Sum.inr (Sum.inr (89, 21)),
    Sum.inr (Sum.inr (146, 21)),
    Sum.inr (Sum.inl (141, 6)),
    Sum.inl 125,
    Sum.inr (Sum.inl (141, 30)),
    Sum.inl 90,
    Sum.inl 362,
    Sum.inr (Sum.inl (141, 25)),
    Sum.inl 143,
    Sum.inr (Sum.inl (141, 1)),
    Sum.inr (Sum.inl (141, 20)),
    Sum.inl 105,
    Sum.inr (Sum.inl (141, 22)),
    Sum.inl 108,
    Sum.inl 342,
    Sum.inr (Sum.inl (141, 11)),
    Sum.inl 347,
    Sum.inr (Sum.inl (141, 9)),
    Sum.inr (Sum.inl (141, 12)),
    Sum.inl 109,
    Sum.inr (Sum.inl (141, 14)),
    Sum.inl 104,
    Sum.inl 346,
    Sum.inr (Sum.inl (141, 19)),
    Sum.inl 343,
    Sum.inr (Sum.inl (141, 17)),
    Sum.inr (Sum.inl (141, 4)),
    Sum.inl 91,
    Sum.inr (Sum.inl (141, 28)),
    Sum.inl 124,
    Sum.inl 142,
    Sum.inr (Sum.inl (141, 27)),
    Sum.inl 363,
    Sum.inr (Sum.inl (141, 3)),
    Sum.inl 473,
    Sum.inr (Sum.inl (141, 61)),
    Sum.inl 152,
    Sum.inr (Sum.inl (141, 37)),
    Sum.inr (Sum.inl (141, 56)),
    Sum.inl 540,
    Sum.inr (Sum.inl (141, 32)),
    Sum.inl 167,
    Sum.inl 377,
    Sum.inr (Sum.inl (141, 47)),
    Sum.inl 422,
    Sum.inr (Sum.inl (141, 45)),
    Sum.inr (Sum.inl (141, 42)),
    Sum.inl 390,
    Sum.inr (Sum.inl (141, 40)),
    Sum.inl 437,
    Sum.inl 423,
    Sum.inr (Sum.inl (141, 55)),
    Sum.inl 376,
    Sum.inr (Sum.inl (141, 53)),
    Sum.inr (Sum.inl (141, 50)),
    Sum.inl 436,
    Sum.inr (Sum.inl (141, 48)),
    Sum.inl 391,
    Sum.inl 153,
    Sum.inr (Sum.inl (141, 63)),
    Sum.inl 472,
    Sum.inr (Sum.inl (141, 39)),
    Sum.inr (Sum.inl (141, 58)),
    Sum.inl 166,
    Sum.inr (Sum.inl (141, 34)),
    Sum.inl 541,
    Sum.inr (Sum.inr (137, 14)),
    Sum.inr (Sum.inr (3, 14)),
    Sum.inr (Sum.inr (195, 2)),
    Sum.inr (Sum.inr (73, 2)),
    Sum.inr (Sum.inr (343, 14)),
    Sum.inr (Sum.inr (477, 14)),
    Sum.inr (Sum.inr (285, 2)),
    Sum.inr (Sum.inr (407, 2)),
    Sum.inr (Sum.inr (348, 14)),
    Sum.inr (Sum.inr (470, 14)),
    Sum.inr (Sum.inr (278, 2)),
    Sum.inr (Sum.inr (412, 2)),
    Sum.inr (Sum.inr (130, 14)),
    Sum.inr (Sum.inr (8, 14)),
    Sum.inr (Sum.inr (200, 2)),
    Sum.inr (Sum.inr (66, 2)),
    Sum.inr (Sum.inr (66, 14)),
    Sum.inr (Sum.inr (200, 14)),
    Sum.inr (Sum.inr (8, 2)),
    Sum.inr (Sum.inr (130, 2)),
    Sum.inr (Sum.inr (412, 14)),
    Sum.inr (Sum.inr (278, 14)),
    Sum.inr (Sum.inr (470, 2)),
    Sum.inr (Sum.inr (348, 2)),
    Sum.inr (Sum.inr (407, 14)),
    Sum.inr (Sum.inr (285, 14)),
    Sum.inr (Sum.inr (477, 2)),
    Sum.inr (Sum.inr (343, 2)),
    Sum.inr (Sum.inr (73, 14)),
    Sum.inr (Sum.inr (195, 14)),
    Sum.inr (Sum.inr (3, 2)),
    Sum.inr (Sum.inr (137, 2)),
    Sum.inr (Sum.inr (195, 9)),
    Sum.inr (Sum.inr (73, 9)),
    Sum.inr (Sum.inr (137, 21)),
    Sum.inr (Sum.inr (3, 21)),
    Sum.inr (Sum.inr (285, 9)),
    Sum.inr (Sum.inr (407, 9)),
    Sum.inr (Sum.inr (343, 21)),
    Sum.inr (Sum.inr (477, 21)),
    Sum.inr (Sum.inr (278, 9)),
    Sum.inr (Sum.inr (412, 9)),
    Sum.inr (Sum.inr (348, 21)),
    Sum.inr (Sum.inr (470, 21)),
    Sum.inr (Sum.inr (200, 9)),
    Sum.inr (Sum.inr (66, 9)),
    Sum.inr (Sum.inr (130, 21)),
    Sum.inr (Sum.inr (8, 21)),
    Sum.inr (Sum.inr (8, 9)),
    Sum.inr (Sum.inr (130, 9)),
    Sum.inr (Sum.inr (66, 21)),
    Sum.inr (Sum.inr (200, 21)),
    Sum.inr (Sum.inr (470, 9)),
    Sum.inr (Sum.inr (348, 9)),
    Sum.inr (Sum.inr (412, 21)),
    Sum.inr (Sum.inr (278, 21)),
    Sum.inr (Sum.inr (477, 9)),
    Sum.inr (Sum.inr (343, 9)),
    Sum.inr (Sum.inr (407, 21)),
    Sum.inr (Sum.inr (285, 21)),
    Sum.inr (Sum.inr (3, 9)),
    Sum.inr (Sum.inr (137, 9)),
    Sum.inr (Sum.inr (73, 21)),
    Sum.inr (Sum.inr (195, 21)),
    Sum.inr (Sum.inr (498, 14)),
    Sum.inr (Sum.inr (109, 2)),
    Sum.inr (Sum.inr (505, 14)),
    Sum.inr (Sum.inr (102, 2)),
    Sum.inr (Sum.inr (109, 9)),
    Sum.inr (Sum.inr (498, 21)),
    Sum.inr (Sum.inr (102, 9)),
    Sum.inr (Sum.inr (505, 21)),
    Sum.inr (Sum.inr (39, 14)),
    Sum.inr (Sum.inr (440, 2)),
    Sum.inr (Sum.inr (44, 14)),
    Sum.inr (Sum.inr (435, 2)),
    Sum.inr (Sum.inr (440, 9)),
    Sum.inr (Sum.inr (39, 21)),
    Sum.inr (Sum.inr (435, 9)),
    Sum.inr (Sum.inr (44, 21)),
    Sum.inr (Sum.inr (236, 14)),
    Sum.inr (Sum.inr (371, 2)),
    Sum.inr (Sum.inr (231, 14)),
    Sum.inr (Sum.inr (376, 2)),
    Sum.inr (Sum.inr (371, 9)),
    Sum.inr (Sum.inr (236, 21)),
    Sum.inr (Sum.inr (376, 9)),
    Sum.inr (Sum.inr (231, 21))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock037Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨9472 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block037_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock037Input a
    let y := generatedSixthXiShortBlock037Output a
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
theorem generatedSixth_xi_short_block037_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock037Input a
    let y := generatedSixthXiShortBlock037Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block037_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block037_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock037Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block037_certificate a).1
    (generatedSixth_xi_short_block037_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
