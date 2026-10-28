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
def generatedSixthXiShortBlock041Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inl (78, 41)),
    Sum.inr (Sum.inl (225, 25)),
    Sum.inr (Sum.inl (78, 37)),
    Sum.inr (Sum.inl (225, 11)),
    Sum.inr (Sum.inl (155, 8)),
    Sum.inr (Sum.inl (177, 17)),
    Sum.inr (Sum.inl (155, 10)),
    Sum.inr (Sum.inl (177, 18)),
    Sum.inr (Sum.inl (55, 3)),
    Sum.inr (Sum.inl (72, 10)),
    Sum.inr (Sum.inl (55, 1)),
    Sum.inr (Sum.inl (72, 6)),
    Sum.inr (Sum.inl (139, 11)),
    Sum.inr (Sum.inl (124, 49)),
    Sum.inr (Sum.inl (139, 7)),
    Sum.inr (Sum.inl (124, 57)),
    Sum.inr (Sum.inl (177, 2)),
    Sum.inr (Sum.inl (155, 61)),
    Sum.inr (Sum.inl (177, 1)),
    Sum.inr (Sum.inl (155, 63)),
    Sum.inr (Sum.inl (225, 35)),
    Sum.inr (Sum.inl (78, 53)),
    Sum.inr (Sum.inl (225, 49)),
    Sum.inr (Sum.inl (78, 57)),
    Sum.inr (Sum.inl (72, 11)),
    Sum.inr (Sum.inl (55, 56)),
    Sum.inr (Sum.inl (72, 7)),
    Sum.inr (Sum.inl (55, 58)),
    Sum.inr (Sum.inl (124, 16)),
    Sum.inr (Sum.inl (139, 36)),
    Sum.inr (Sum.inl (124, 24)),
    Sum.inr (Sum.inl (139, 40)),
    Sum.inr (Sum.inl (155, 44)),
    Sum.inr (Sum.inl (177, 57)),
    Sum.inr (Sum.inl (155, 46)),
    Sum.inr (Sum.inl (177, 58)),
    Sum.inr (Sum.inl (78, 20)),
    Sum.inr (Sum.inl (225, 24)),
    Sum.inr (Sum.inl (78, 24)),
    Sum.inr (Sum.inl (225, 10)),
    Sum.inr (Sum.inl (73, 28)),
    Sum.inr (Sum.inl (107, 53)),
    Sum.inr (Sum.inl (176, 58)),
    Sum.inr (Sum.inl (230, 19)),
    Sum.inr (Sum.inl (92, 13)),
    Sum.inr (Sum.inl (54, 53)),
    Sum.inr (Sum.inl (111, 53)),
    Sum.inr (Sum.inl (156, 7)),
    Sum.inr (Sum.inl (92, 14)),
    Sum.inr (Sum.inl (54, 57)),
    Sum.inr (Sum.inl (111, 57)),
    Sum.inr (Sum.inl (156, 11)),
    Sum.inr (Sum.inl (73, 30)),
    Sum.inr (Sum.inl (107, 39)),
    Sum.inr (Sum.inl (176, 56)),
    Sum.inr (Sum.inl (230, 27)),
    Sum.inr (Sum.inl (73, 21)),
    Sum.inr (Sum.inl (107, 29)),
    Sum.inr (Sum.inl (176, 13)),
    Sum.inr (Sum.inl (230, 7)),
    Sum.inr (Sum.inl (92, 29)),
    Sum.inr (Sum.inl (54, 39)),
    Sum.inr (Sum.inl (111, 23)),
    Sum.inr (Sum.inl (156, 23)),
    Sum.inr (Sum.inl (92, 30)),
    Sum.inr (Sum.inl (54, 43)),
    Sum.inr (Sum.inl (111, 27)),
    Sum.inr (Sum.inl (156, 27)),
    Sum.inr (Sum.inl (73, 23)),
    Sum.inr (Sum.inl (107, 15)),
    Sum.inr (Sum.inl (176, 15)),
    Sum.inr (Sum.inl (230, 15)),
    Sum.inr (Sum.inl (176, 27)),
    Sum.inr (Sum.inl (230, 49)),
    Sum.inr (Sum.inl (73, 51)),
    Sum.inr (Sum.inl (107, 49)),
    Sum.inr (Sum.inl (111, 11)),
    Sum.inr (Sum.inl (156, 37)),
    Sum.inr (Sum.inl (92, 58)),
    Sum.inr (Sum.inl (54, 21)),
    Sum.inr (Sum.inl (111, 7)),
    Sum.inr (Sum.inl (156, 41)),
    Sum.inr (Sum.inl (92, 57)),
    Sum.inr (Sum.inl (54, 25)),
    Sum.inr (Sum.inl (176, 25)),
    Sum.inr (Sum.inl (230, 57)),
    Sum.inr (Sum.inl (73, 49)),
    Sum.inr (Sum.inl (107, 35)),
    Sum.inr (Sum.inl (176, 44)),
    Sum.inr (Sum.inl (230, 37)),
    Sum.inr (Sum.inl (73, 58)),
    Sum.inr (Sum.inl (107, 25)),
    Sum.inr (Sum.inl (111, 41)),
    Sum.inr (Sum.inl (156, 53)),
    Sum.inr (Sum.inl (92, 42)),
    Sum.inr (Sum.inl (54, 7)),
    Sum.inr (Sum.inl (111, 37)),
    Sum.inr (Sum.inl (156, 57)),
    Sum.inr (Sum.inl (92, 41)),
    Sum.inr (Sum.inl (54, 11)),
    Sum.inr (Sum.inl (176, 46)),
    Sum.inr (Sum.inl (230, 45)),
    Sum.inr (Sum.inl (73, 56)),
    Sum.inr (Sum.inl (107, 11)),
    Sum.inr (Sum.inr (216, 15)),
    Sum.inr (Sum.inr (19, 15)),
    Sum.inr (Sum.inr (82, 1)),
    Sum.inr (Sum.inr (153, 1)),
    Sum.inr (Sum.inr (262, 15)),
    Sum.inr (Sum.inr (461, 15)),
    Sum.inr (Sum.inr (396, 1)),
    Sum.inr (Sum.inr (327, 1)),
    Sum.inr (Sum.inr (269, 15)),
    Sum.inr (Sum.inr (454, 15)),
    Sum.inr (Sum.inr (391, 1)),
    Sum.inr (Sum.inr (332, 1)),
    Sum.inr (Sum.inr (211, 15)),
    Sum.inr (Sum.inr (24, 15)),
    Sum.inr (Sum.inr (89, 1)),
    Sum.inr (Sum.inr (146, 1)),
    Sum.inr (Sum.inr (146, 15)),
    Sum.inr (Sum.inr (89, 15)),
    Sum.inr (Sum.inr (24, 1)),
    Sum.inr (Sum.inr (211, 1)),
    Sum.inr (Sum.inr (332, 15)),
    Sum.inr (Sum.inr (391, 15)),
    Sum.inr (Sum.inr (454, 1)),
    Sum.inr (Sum.inr (269, 1)),
    Sum.inr (Sum.inr (327, 15)),
    Sum.inr (Sum.inr (396, 15)),
    Sum.inr (Sum.inr (461, 1)),
    Sum.inr (Sum.inr (262, 1)),
    Sum.inr (Sum.inr (153, 15)),
    Sum.inr (Sum.inr (82, 15)),
    Sum.inr (Sum.inr (19, 1)),
    Sum.inr (Sum.inr (216, 1)),
    Sum.inr (Sum.inr (82, 11)),
    Sum.inr (Sum.inr (153, 11)),
    Sum.inr (Sum.inr (216, 22)),
    Sum.inr (Sum.inr (19, 22)),
    Sum.inr (Sum.inr (396, 11)),
    Sum.inr (Sum.inr (327, 11)),
    Sum.inr (Sum.inr (262, 22)),
    Sum.inr (Sum.inr (461, 22)),
    Sum.inr (Sum.inr (391, 11)),
    Sum.inr (Sum.inr (332, 11)),
    Sum.inr (Sum.inr (269, 22)),
    Sum.inr (Sum.inr (454, 22)),
    Sum.inr (Sum.inr (89, 11)),
    Sum.inr (Sum.inr (146, 11)),
    Sum.inr (Sum.inr (211, 22)),
    Sum.inr (Sum.inr (24, 22)),
    Sum.inr (Sum.inr (24, 11)),
    Sum.inr (Sum.inr (211, 11)),
    Sum.inr (Sum.inr (146, 22)),
    Sum.inr (Sum.inr (89, 22)),
    Sum.inr (Sum.inr (454, 11)),
    Sum.inr (Sum.inr (269, 11)),
    Sum.inr (Sum.inr (332, 22)),
    Sum.inr (Sum.inr (391, 22)),
    Sum.inr (Sum.inr (461, 11)),
    Sum.inr (Sum.inr (262, 11)),
    Sum.inr (Sum.inr (327, 22)),
    Sum.inr (Sum.inr (396, 22)),
    Sum.inr (Sum.inr (19, 11)),
    Sum.inr (Sum.inr (216, 11)),
    Sum.inr (Sum.inr (153, 22)),
    Sum.inr (Sum.inr (82, 22)),
    Sum.inr (Sum.inr (216, 0)),
    Sum.inr (Sum.inr (262, 0)),
    Sum.inr (Sum.inr (269, 0)),
    Sum.inr (Sum.inr (211, 0)),
    Sum.inr (Sum.inr (19, 8)),
    Sum.inr (Sum.inr (461, 8)),
    Sum.inr (Sum.inr (454, 8)),
    Sum.inr (Sum.inr (24, 8)),
    Sum.inr (Sum.inr (146, 0)),
    Sum.inr (Sum.inr (332, 0)),
    Sum.inr (Sum.inr (327, 0)),
    Sum.inr (Sum.inr (153, 0)),
    Sum.inr (Sum.inr (89, 8)),
    Sum.inr (Sum.inr (391, 8)),
    Sum.inr (Sum.inr (396, 8)),
    Sum.inr (Sum.inr (82, 8)),
    Sum.inr (Sum.inr (19, 13)),
    Sum.inr (Sum.inr (461, 13)),
    Sum.inr (Sum.inr (454, 13)),
    Sum.inr (Sum.inr (24, 13)),
    Sum.inr (Sum.inr (216, 23)),
    Sum.inr (Sum.inr (262, 23)),
    Sum.inr (Sum.inr (269, 23)),
    Sum.inr (Sum.inr (211, 23)),
    Sum.inr (Sum.inr (89, 13)),
    Sum.inr (Sum.inr (391, 13)),
    Sum.inr (Sum.inr (396, 13)),
    Sum.inr (Sum.inr (82, 13)),
    Sum.inr (Sum.inr (146, 23)),
    Sum.inr (Sum.inr (332, 23)),
    Sum.inr (Sum.inr (327, 23)),
    Sum.inr (Sum.inr (153, 23)),
    Sum.inr (Sum.inr (82, 0)),
    Sum.inr (Sum.inr (396, 0)),
    Sum.inr (Sum.inr (391, 0)),
    Sum.inr (Sum.inr (89, 0)),
    Sum.inr (Sum.inr (153, 8)),
    Sum.inr (Sum.inr (327, 8)),
    Sum.inr (Sum.inr (332, 8)),
    Sum.inr (Sum.inr (146, 8)),
    Sum.inr (Sum.inr (24, 0)),
    Sum.inr (Sum.inr (454, 0)),
    Sum.inr (Sum.inr (461, 0)),
    Sum.inr (Sum.inr (19, 0)),
    Sum.inr (Sum.inr (211, 8)),
    Sum.inr (Sum.inr (269, 8)),
    Sum.inr (Sum.inr (262, 8)),
    Sum.inr (Sum.inr (216, 8)),
    Sum.inr (Sum.inr (153, 13)),
    Sum.inr (Sum.inr (327, 13)),
    Sum.inr (Sum.inr (332, 13)),
    Sum.inr (Sum.inr (146, 13)),
    Sum.inr (Sum.inr (82, 23)),
    Sum.inr (Sum.inr (396, 23)),
    Sum.inr (Sum.inr (391, 23)),
    Sum.inr (Sum.inr (89, 23)),
    Sum.inr (Sum.inr (211, 13)),
    Sum.inr (Sum.inr (269, 13)),
    Sum.inr (Sum.inr (262, 13)),
    Sum.inr (Sum.inr (216, 13)),
    Sum.inr (Sum.inr (24, 23)),
    Sum.inr (Sum.inr (454, 23)),
    Sum.inr (Sum.inr (461, 23)),
    Sum.inr (Sum.inr (19, 23)),
    Sum.inr (Sum.inl (109, 12)),
    Sum.inr (Sum.inl (79, 24)),
    Sum.inr (Sum.inl (79, 20)),
    Sum.inr (Sum.inl (109, 4)),
    Sum.inr (Sum.inl (181, 46)),
    Sum.inr (Sum.inl (51, 37)),
    Sum.inr (Sum.inl (51, 41)),
    Sum.inr (Sum.inl (181, 44)),
    Sum.inr (Sum.inl (109, 40)),
    Sum.inr (Sum.inl (79, 8)),
    Sum.inr (Sum.inl (79, 4)),
    Sum.inr (Sum.inl (109, 32)),
    Sum.inr (Sum.inl (181, 25)),
    Sum.inr (Sum.inl (51, 39)),
    Sum.inr (Sum.inl (51, 43)),
    Sum.inr (Sum.inl (181, 27)),
    Sum.inr (Sum.inl (181, 10)),
    Sum.inr (Sum.inl (51, 10)),
    Sum.inr (Sum.inl (51, 6)),
    Sum.inr (Sum.inl (181, 8)),
    Sum.inr (Sum.inl (109, 49)),
    Sum.inr (Sum.inl (79, 37)),
    Sum.inr (Sum.inl (79, 41)),
    Sum.inr (Sum.inl (109, 57))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock041Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨10496 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block041_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock041Input a
    let y := generatedSixthXiShortBlock041Output a
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
theorem generatedSixth_xi_short_block041_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock041Input a
    let y := generatedSixthXiShortBlock041Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block041_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block041_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock041Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block041_certificate a).1
    (generatedSixth_xi_short_block041_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
