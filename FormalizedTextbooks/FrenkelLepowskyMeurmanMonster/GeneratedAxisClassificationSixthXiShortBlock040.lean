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
def generatedSixthXiShortBlock040Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (100, 9)),
    Sum.inr (Sum.inr (378, 9)),
    Sum.inr (Sum.inr (315, 9)),
    Sum.inr (Sum.inr (37, 9)),
    Sum.inr (Sum.inr (433, 9)),
    Sum.inr (Sum.inr (175, 9)),
    Sum.inr (Sum.inr (238, 9)),
    Sum.inr (Sum.inr (496, 9)),
    Sum.inr (Sum.inr (111, 14)),
    Sum.inr (Sum.inr (369, 14)),
    Sum.inr (Sum.inr (304, 14)),
    Sum.inr (Sum.inr (46, 14)),
    Sum.inr (Sum.inr (442, 14)),
    Sum.inr (Sum.inr (164, 14)),
    Sum.inr (Sum.inr (229, 14)),
    Sum.inr (Sum.inr (507, 14)),
    Sum.inr (Sum.inr (100, 14)),
    Sum.inr (Sum.inr (378, 14)),
    Sum.inr (Sum.inr (315, 14)),
    Sum.inr (Sum.inr (37, 14)),
    Sum.inr (Sum.inr (433, 14)),
    Sum.inr (Sum.inr (175, 14)),
    Sum.inr (Sum.inr (238, 14)),
    Sum.inr (Sum.inr (496, 14)),
    Sum.inr (Sum.inr (496, 21)),
    Sum.inr (Sum.inr (238, 21)),
    Sum.inr (Sum.inr (175, 21)),
    Sum.inr (Sum.inr (433, 21)),
    Sum.inr (Sum.inr (37, 21)),
    Sum.inr (Sum.inr (315, 21)),
    Sum.inr (Sum.inr (378, 21)),
    Sum.inr (Sum.inr (100, 21)),
    Sum.inr (Sum.inr (507, 21)),
    Sum.inr (Sum.inr (229, 21)),
    Sum.inr (Sum.inr (164, 21)),
    Sum.inr (Sum.inr (442, 21)),
    Sum.inr (Sum.inr (46, 21)),
    Sum.inr (Sum.inr (304, 21)),
    Sum.inr (Sum.inr (369, 21)),
    Sum.inr (Sum.inr (111, 21)),
    Sum.inr (Sum.inr (64, 2)),
    Sum.inr (Sum.inr (468, 21)),
    Sum.inr (Sum.inr (479, 21)),
    Sum.inr (Sum.inr (75, 2)),
    Sum.inr (Sum.inr (64, 14)),
    Sum.inr (Sum.inr (468, 9)),
    Sum.inr (Sum.inr (479, 9)),
    Sum.inr (Sum.inr (75, 14)),
    Sum.inr (Sum.inr (10, 21)),
    Sum.inr (Sum.inr (414, 2)),
    Sum.inr (Sum.inr (405, 2)),
    Sum.inr (Sum.inr (1, 21)),
    Sum.inr (Sum.inr (10, 9)),
    Sum.inr (Sum.inr (414, 14)),
    Sum.inr (Sum.inr (405, 14)),
    Sum.inr (Sum.inr (1, 9)),
    Sum.inr (Sum.inr (64, 9)),
    Sum.inr (Sum.inr (468, 14)),
    Sum.inr (Sum.inr (479, 14)),
    Sum.inr (Sum.inr (75, 9)),
    Sum.inr (Sum.inr (64, 21)),
    Sum.inr (Sum.inr (468, 2)),
    Sum.inr (Sum.inr (479, 2)),
    Sum.inr (Sum.inr (75, 21)),
    Sum.inr (Sum.inr (10, 14)),
    Sum.inr (Sum.inr (414, 9)),
    Sum.inr (Sum.inr (405, 9)),
    Sum.inr (Sum.inr (1, 14)),
    Sum.inr (Sum.inr (10, 2)),
    Sum.inr (Sum.inr (414, 21)),
    Sum.inr (Sum.inr (405, 21)),
    Sum.inr (Sum.inr (1, 2)),
    Sum.inr (Sum.inr (128, 21)),
    Sum.inr (Sum.inr (276, 2)),
    Sum.inr (Sum.inr (287, 2)),
    Sum.inr (Sum.inr (139, 21)),
    Sum.inr (Sum.inr (128, 9)),
    Sum.inr (Sum.inr (276, 14)),
    Sum.inr (Sum.inr (287, 14)),
    Sum.inr (Sum.inr (139, 9)),
    Sum.inr (Sum.inr (202, 2)),
    Sum.inr (Sum.inr (350, 21)),
    Sum.inr (Sum.inr (341, 21)),
    Sum.inr (Sum.inr (193, 2)),
    Sum.inr (Sum.inr (202, 14)),
    Sum.inr (Sum.inr (350, 9)),
    Sum.inr (Sum.inr (341, 9)),
    Sum.inr (Sum.inr (193, 14)),
    Sum.inr (Sum.inr (128, 14)),
    Sum.inr (Sum.inr (276, 9)),
    Sum.inr (Sum.inr (287, 9)),
    Sum.inr (Sum.inr (139, 14)),
    Sum.inr (Sum.inr (128, 2)),
    Sum.inr (Sum.inr (276, 21)),
    Sum.inr (Sum.inr (287, 21)),
    Sum.inr (Sum.inr (139, 2)),
    Sum.inr (Sum.inr (202, 9)),
    Sum.inr (Sum.inr (350, 14)),
    Sum.inr (Sum.inr (341, 14)),
    Sum.inr (Sum.inr (193, 9)),
    Sum.inr (Sum.inr (202, 21)),
    Sum.inr (Sum.inr (350, 2)),
    Sum.inr (Sum.inr (341, 2)),
    Sum.inr (Sum.inr (193, 21)),
    Sum.inr (Sum.inr (216, 20)),
    Sum.inr (Sum.inr (19, 12)),
    Sum.inr (Sum.inr (216, 10)),
    Sum.inr (Sum.inr (19, 3)),
    Sum.inr (Sum.inr (262, 12)),
    Sum.inr (Sum.inr (461, 20)),
    Sum.inr (Sum.inr (262, 3)),
    Sum.inr (Sum.inr (461, 10)),
    Sum.inr (Sum.inr (269, 12)),
    Sum.inr (Sum.inr (454, 20)),
    Sum.inr (Sum.inr (269, 3)),
    Sum.inr (Sum.inr (454, 10)),
    Sum.inr (Sum.inr (211, 20)),
    Sum.inr (Sum.inr (24, 12)),
    Sum.inr (Sum.inr (211, 10)),
    Sum.inr (Sum.inr (24, 3)),
    Sum.inr (Sum.inr (146, 12)),
    Sum.inr (Sum.inr (89, 20)),
    Sum.inr (Sum.inr (146, 3)),
    Sum.inr (Sum.inr (89, 10)),
    Sum.inr (Sum.inr (332, 20)),
    Sum.inr (Sum.inr (391, 12)),
    Sum.inr (Sum.inr (332, 10)),
    Sum.inr (Sum.inr (391, 3)),
    Sum.inr (Sum.inr (327, 20)),
    Sum.inr (Sum.inr (396, 12)),
    Sum.inr (Sum.inr (327, 10)),
    Sum.inr (Sum.inr (396, 3)),
    Sum.inr (Sum.inr (153, 12)),
    Sum.inr (Sum.inr (82, 20)),
    Sum.inr (Sum.inr (153, 3)),
    Sum.inr (Sum.inr (82, 10)),
    Sum.inr (Sum.inr (216, 3)),
    Sum.inr (Sum.inr (19, 10)),
    Sum.inr (Sum.inr (216, 12)),
    Sum.inr (Sum.inr (19, 20)),
    Sum.inr (Sum.inr (262, 10)),
    Sum.inr (Sum.inr (461, 3)),
    Sum.inr (Sum.inr (262, 20)),
    Sum.inr (Sum.inr (461, 12)),
    Sum.inr (Sum.inr (269, 10)),
    Sum.inr (Sum.inr (454, 3)),
    Sum.inr (Sum.inr (269, 20)),
    Sum.inr (Sum.inr (454, 12)),
    Sum.inr (Sum.inr (211, 3)),
    Sum.inr (Sum.inr (24, 10)),
    Sum.inr (Sum.inr (211, 12)),
    Sum.inr (Sum.inr (24, 20)),
    Sum.inr (Sum.inr (146, 10)),
    Sum.inr (Sum.inr (89, 3)),
    Sum.inr (Sum.inr (146, 20)),
    Sum.inr (Sum.inr (89, 12)),
    Sum.inr (Sum.inr (332, 3)),
    Sum.inr (Sum.inr (391, 10)),
    Sum.inr (Sum.inr (332, 12)),
    Sum.inr (Sum.inr (391, 20)),
    Sum.inr (Sum.inr (327, 3)),
    Sum.inr (Sum.inr (396, 10)),
    Sum.inr (Sum.inr (327, 12)),
    Sum.inr (Sum.inr (396, 20)),
    Sum.inr (Sum.inr (153, 10)),
    Sum.inr (Sum.inr (82, 3)),
    Sum.inr (Sum.inr (153, 20)),
    Sum.inr (Sum.inr (82, 12)),
    Sum.inr (Sum.inl (91, 8)),
    Sum.inr (Sum.inl (216, 59)),
    Sum.inr (Sum.inl (186, 40)),
    Sum.inr (Sum.inl (138, 48)),
    Sum.inr (Sum.inl (41, 16)),
    Sum.inr (Sum.inl (108, 47)),
    Sum.inr (Sum.inl (125, 48)),
    Sum.inr (Sum.inl (154, 47)),
    Sum.inr (Sum.inl (41, 19)),
    Sum.inr (Sum.inl (108, 35)),
    Sum.inr (Sum.inl (125, 60)),
    Sum.inr (Sum.inl (154, 35)),
    Sum.inr (Sum.inl (91, 26)),
    Sum.inr (Sum.inl (216, 57)),
    Sum.inr (Sum.inl (186, 42)),
    Sum.inr (Sum.inl (138, 56)),
    Sum.inr (Sum.inl (216, 62)),
    Sum.inr (Sum.inl (91, 63)),
    Sum.inr (Sum.inl (138, 33)),
    Sum.inr (Sum.inl (186, 31)),
    Sum.inr (Sum.inl (108, 62)),
    Sum.inr (Sum.inl (41, 63)),
    Sum.inr (Sum.inl (154, 62)),
    Sum.inr (Sum.inl (125, 31)),
    Sum.inr (Sum.inl (108, 50)),
    Sum.inr (Sum.inl (41, 60)),
    Sum.inr (Sum.inl (154, 50)),
    Sum.inr (Sum.inl (125, 19)),
    Sum.inr (Sum.inl (216, 60)),
    Sum.inr (Sum.inl (91, 45)),
    Sum.inr (Sum.inl (138, 41)),
    Sum.inr (Sum.inl (186, 29)),
    Sum.inr (Sum.inl (91, 41)),
    Sum.inr (Sum.inl (216, 19)),
    Sum.inr (Sum.inl (186, 60)),
    Sum.inr (Sum.inl (138, 11)),
    Sum.inr (Sum.inl (41, 52)),
    Sum.inr (Sum.inl (108, 45)),
    Sum.inr (Sum.inl (125, 50)),
    Sum.inr (Sum.inl (154, 15)),
    Sum.inr (Sum.inl (41, 55)),
    Sum.inr (Sum.inl (108, 33)),
    Sum.inr (Sum.inl (125, 62)),
    Sum.inr (Sum.inl (154, 3)),
    Sum.inr (Sum.inl (91, 59)),
    Sum.inr (Sum.inl (216, 17)),
    Sum.inr (Sum.inl (186, 62)),
    Sum.inr (Sum.inl (138, 3)),
    Sum.inr (Sum.inl (216, 22)),
    Sum.inr (Sum.inl (91, 30)),
    Sum.inr (Sum.inl (138, 26)),
    Sum.inr (Sum.inl (186, 11)),
    Sum.inr (Sum.inl (108, 60)),
    Sum.inr (Sum.inl (41, 27)),
    Sum.inr (Sum.inl (154, 30)),
    Sum.inr (Sum.inl (125, 29)),
    Sum.inr (Sum.inl (108, 48)),
    Sum.inr (Sum.inl (41, 24)),
    Sum.inr (Sum.inl (154, 18)),
    Sum.inr (Sum.inl (125, 17)),
    Sum.inr (Sum.inl (216, 20)),
    Sum.inr (Sum.inl (91, 12)),
    Sum.inr (Sum.inl (138, 18)),
    Sum.inr (Sum.inl (186, 9)),
    Sum.inr (Sum.inl (139, 10)),
    Sum.inr (Sum.inl (124, 12)),
    Sum.inr (Sum.inl (139, 6)),
    Sum.inr (Sum.inl (124, 4)),
    Sum.inr (Sum.inl (55, 43)),
    Sum.inr (Sum.inl (72, 37)),
    Sum.inr (Sum.inl (55, 41)),
    Sum.inr (Sum.inl (72, 41)),
    Sum.inr (Sum.inl (225, 34)),
    Sum.inr (Sum.inl (78, 8)),
    Sum.inr (Sum.inl (225, 48)),
    Sum.inr (Sum.inl (78, 4)),
    Sum.inr (Sum.inl (177, 42)),
    Sum.inr (Sum.inl (155, 25)),
    Sum.inr (Sum.inl (177, 41)),
    Sum.inr (Sum.inl (155, 27)),
    Sum.inr (Sum.inl (124, 45)),
    Sum.inr (Sum.inl (139, 37)),
    Sum.inr (Sum.inl (124, 37)),
    Sum.inr (Sum.inl (139, 41)),
    Sum.inr (Sum.inl (72, 36)),
    Sum.inr (Sum.inl (55, 16)),
    Sum.inr (Sum.inl (72, 40)),
    Sum.inr (Sum.inl (55, 18))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock040Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨10240 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block040_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock040Input a
    let y := generatedSixthXiShortBlock040Output a
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
theorem generatedSixth_xi_short_block040_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock040Input a
    let y := generatedSixthXiShortBlock040Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block040_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block040_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock040Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block040_certificate a).1
    (generatedSixth_xi_short_block040_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
