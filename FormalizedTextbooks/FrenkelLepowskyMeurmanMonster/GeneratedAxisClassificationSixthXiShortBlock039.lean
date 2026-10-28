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
def generatedSixthXiShortBlock039Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (363, 9)),
    Sum.inr (Sum.inr (490, 2)),
    Sum.inr (Sum.inr (363, 14)),
    Sum.inr (Sum.inr (490, 21)),
    Sum.inr (Sum.inr (244, 2)),
    Sum.inr (Sum.inr (117, 9)),
    Sum.inr (Sum.inr (244, 21)),
    Sum.inr (Sum.inr (117, 14)),
    Sum.inr (Sum.inr (181, 21)),
    Sum.inr (Sum.inr (52, 14)),
    Sum.inr (Sum.inr (181, 2)),
    Sum.inr (Sum.inr (52, 9)),
    Sum.inr (Sum.inr (298, 14)),
    Sum.inr (Sum.inr (427, 21)),
    Sum.inr (Sum.inr (298, 9)),
    Sum.inr (Sum.inr (427, 2)),
    Sum.inr (Sum.inr (289, 14)),
    Sum.inr (Sum.inr (416, 21)),
    Sum.inr (Sum.inr (289, 9)),
    Sum.inr (Sum.inr (416, 2)),
    Sum.inr (Sum.inr (190, 21)),
    Sum.inr (Sum.inr (63, 14)),
    Sum.inr (Sum.inr (190, 2)),
    Sum.inr (Sum.inr (63, 9)),
    Sum.inr (Sum.inr (181, 9)),
    Sum.inr (Sum.inr (52, 2)),
    Sum.inr (Sum.inr (181, 14)),
    Sum.inr (Sum.inr (52, 21)),
    Sum.inr (Sum.inr (298, 2)),
    Sum.inr (Sum.inr (427, 9)),
    Sum.inr (Sum.inr (298, 21)),
    Sum.inr (Sum.inr (427, 14)),
    Sum.inr (Sum.inr (289, 2)),
    Sum.inr (Sum.inr (416, 9)),
    Sum.inr (Sum.inr (289, 21)),
    Sum.inr (Sum.inr (416, 14)),
    Sum.inr (Sum.inr (190, 9)),
    Sum.inr (Sum.inr (63, 2)),
    Sum.inr (Sum.inr (190, 14)),
    Sum.inr (Sum.inr (63, 21)),
    Sum.inr (Sum.inr (497, 9)),
    Sum.inr (Sum.inr (110, 2)),
    Sum.inr (Sum.inr (506, 9)),
    Sum.inr (Sum.inr (101, 2)),
    Sum.inr (Sum.inr (239, 9)),
    Sum.inr (Sum.inr (368, 2)),
    Sum.inr (Sum.inr (228, 9)),
    Sum.inr (Sum.inr (379, 2)),
    Sum.inr (Sum.inr (36, 9)),
    Sum.inr (Sum.inr (443, 2)),
    Sum.inr (Sum.inr (47, 9)),
    Sum.inr (Sum.inr (432, 2)),
    Sum.inr (Sum.inr (314, 9)),
    Sum.inr (Sum.inr (165, 2)),
    Sum.inr (Sum.inr (305, 9)),
    Sum.inr (Sum.inr (174, 2)),
    Sum.inr (Sum.inr (174, 9)),
    Sum.inr (Sum.inr (305, 2)),
    Sum.inr (Sum.inr (165, 9)),
    Sum.inr (Sum.inr (314, 2)),
    Sum.inr (Sum.inr (432, 9)),
    Sum.inr (Sum.inr (47, 2)),
    Sum.inr (Sum.inr (443, 9)),
    Sum.inr (Sum.inr (36, 2)),
    Sum.inr (Sum.inr (379, 9)),
    Sum.inr (Sum.inr (228, 2)),
    Sum.inr (Sum.inr (368, 9)),
    Sum.inr (Sum.inr (239, 2)),
    Sum.inr (Sum.inr (101, 9)),
    Sum.inr (Sum.inr (506, 2)),
    Sum.inr (Sum.inr (110, 9)),
    Sum.inr (Sum.inr (497, 2)),
    Sum.inr (Sum.inr (110, 14)),
    Sum.inr (Sum.inr (497, 21)),
    Sum.inr (Sum.inr (101, 14)),
    Sum.inr (Sum.inr (506, 21)),
    Sum.inr (Sum.inr (368, 14)),
    Sum.inr (Sum.inr (239, 21)),
    Sum.inr (Sum.inr (379, 14)),
    Sum.inr (Sum.inr (228, 21)),
    Sum.inr (Sum.inr (443, 14)),
    Sum.inr (Sum.inr (36, 21)),
    Sum.inr (Sum.inr (432, 14)),
    Sum.inr (Sum.inr (47, 21)),
    Sum.inr (Sum.inr (165, 14)),
    Sum.inr (Sum.inr (314, 21)),
    Sum.inr (Sum.inr (174, 14)),
    Sum.inr (Sum.inr (305, 21)),
    Sum.inr (Sum.inr (305, 14)),
    Sum.inr (Sum.inr (174, 21)),
    Sum.inr (Sum.inr (314, 14)),
    Sum.inr (Sum.inr (165, 21)),
    Sum.inr (Sum.inr (47, 14)),
    Sum.inr (Sum.inr (432, 21)),
    Sum.inr (Sum.inr (36, 14)),
    Sum.inr (Sum.inr (443, 21)),
    Sum.inr (Sum.inr (228, 14)),
    Sum.inr (Sum.inr (379, 21)),
    Sum.inr (Sum.inr (239, 14)),
    Sum.inr (Sum.inr (368, 21)),
    Sum.inr (Sum.inr (506, 14)),
    Sum.inr (Sum.inr (101, 21)),
    Sum.inr (Sum.inr (497, 14)),
    Sum.inr (Sum.inr (110, 21)),
    Sum.inr (Sum.inr (504, 21)),
    Sum.inr (Sum.inr (312, 2)),
    Sum.inr (Sum.inr (172, 21)),
    Sum.inr (Sum.inr (108, 2)),
    Sum.inr (Sum.inr (312, 9)),
    Sum.inr (Sum.inr (504, 14)),
    Sum.inr (Sum.inr (108, 9)),
    Sum.inr (Sum.inr (172, 14)),
    Sum.inr (Sum.inr (312, 14)),
    Sum.inr (Sum.inr (504, 9)),
    Sum.inr (Sum.inr (108, 14)),
    Sum.inr (Sum.inr (172, 9)),
    Sum.inr (Sum.inr (504, 2)),
    Sum.inr (Sum.inr (312, 21)),
    Sum.inr (Sum.inr (172, 2)),
    Sum.inr (Sum.inr (108, 21)),
    Sum.inr (Sum.inr (167, 21)),
    Sum.inr (Sum.inr (103, 2)),
    Sum.inr (Sum.inr (499, 21)),
    Sum.inr (Sum.inr (307, 2)),
    Sum.inr (Sum.inr (103, 9)),
    Sum.inr (Sum.inr (167, 14)),
    Sum.inr (Sum.inr (307, 9)),
    Sum.inr (Sum.inr (499, 14)),
    Sum.inr (Sum.inr (103, 14)),
    Sum.inr (Sum.inr (167, 9)),
    Sum.inr (Sum.inr (307, 14)),
    Sum.inr (Sum.inr (499, 9)),
    Sum.inr (Sum.inr (167, 2)),
    Sum.inr (Sum.inr (103, 21)),
    Sum.inr (Sum.inr (499, 2)),
    Sum.inr (Sum.inr (307, 21)),
    Sum.inr (Sum.inr (370, 21)),
    Sum.inr (Sum.inr (434, 2)),
    Sum.inr (Sum.inr (38, 21)),
    Sum.inr (Sum.inr (230, 2)),
    Sum.inr (Sum.inr (434, 9)),
    Sum.inr (Sum.inr (370, 14)),
    Sum.inr (Sum.inr (230, 9)),
    Sum.inr (Sum.inr (38, 14)),
    Sum.inr (Sum.inr (434, 14)),
    Sum.inr (Sum.inr (370, 9)),
    Sum.inr (Sum.inr (230, 14)),
    Sum.inr (Sum.inr (38, 9)),
    Sum.inr (Sum.inr (370, 2)),
    Sum.inr (Sum.inr (434, 21)),
    Sum.inr (Sum.inr (38, 2)),
    Sum.inr (Sum.inr (230, 21)),
    Sum.inr (Sum.inr (45, 21)),
    Sum.inr (Sum.inr (237, 2)),
    Sum.inr (Sum.inr (377, 21)),
    Sum.inr (Sum.inr (441, 2)),
    Sum.inr (Sum.inr (237, 9)),
    Sum.inr (Sum.inr (45, 14)),
    Sum.inr (Sum.inr (441, 9)),
    Sum.inr (Sum.inr (377, 14)),
    Sum.inr (Sum.inr (237, 14)),
    Sum.inr (Sum.inr (45, 9)),
    Sum.inr (Sum.inr (441, 14)),
    Sum.inr (Sum.inr (377, 9)),
    Sum.inr (Sum.inr (45, 2)),
    Sum.inr (Sum.inr (237, 21)),
    Sum.inr (Sum.inr (377, 2)),
    Sum.inr (Sum.inr (441, 21)),
    Sum.inr (Sum.inr (83, 2)),
    Sum.inr (Sum.inr (455, 21)),
    Sum.inr (Sum.inr (460, 21)),
    Sum.inr (Sum.inr (88, 2)),
    Sum.inr (Sum.inr (210, 21)),
    Sum.inr (Sum.inr (326, 2)),
    Sum.inr (Sum.inr (333, 2)),
    Sum.inr (Sum.inr (217, 21)),
    Sum.inr (Sum.inr (83, 14)),
    Sum.inr (Sum.inr (455, 9)),
    Sum.inr (Sum.inr (460, 9)),
    Sum.inr (Sum.inr (88, 14)),
    Sum.inr (Sum.inr (210, 9)),
    Sum.inr (Sum.inr (326, 14)),
    Sum.inr (Sum.inr (333, 14)),
    Sum.inr (Sum.inr (217, 9)),
    Sum.inr (Sum.inr (25, 21)),
    Sum.inr (Sum.inr (397, 2)),
    Sum.inr (Sum.inr (390, 2)),
    Sum.inr (Sum.inr (18, 21)),
    Sum.inr (Sum.inr (152, 2)),
    Sum.inr (Sum.inr (268, 21)),
    Sum.inr (Sum.inr (263, 21)),
    Sum.inr (Sum.inr (147, 2)),
    Sum.inr (Sum.inr (25, 9)),
    Sum.inr (Sum.inr (397, 14)),
    Sum.inr (Sum.inr (390, 14)),
    Sum.inr (Sum.inr (18, 9)),
    Sum.inr (Sum.inr (152, 14)),
    Sum.inr (Sum.inr (268, 9)),
    Sum.inr (Sum.inr (263, 9)),
    Sum.inr (Sum.inr (147, 14)),
    Sum.inr (Sum.inr (83, 9)),
    Sum.inr (Sum.inr (455, 14)),
    Sum.inr (Sum.inr (460, 14)),
    Sum.inr (Sum.inr (88, 9)),
    Sum.inr (Sum.inr (210, 14)),
    Sum.inr (Sum.inr (326, 9)),
    Sum.inr (Sum.inr (333, 9)),
    Sum.inr (Sum.inr (217, 14)),
    Sum.inr (Sum.inr (83, 21)),
    Sum.inr (Sum.inr (455, 2)),
    Sum.inr (Sum.inr (460, 2)),
    Sum.inr (Sum.inr (88, 21)),
    Sum.inr (Sum.inr (210, 2)),
    Sum.inr (Sum.inr (326, 21)),
    Sum.inr (Sum.inr (333, 21)),
    Sum.inr (Sum.inr (217, 2)),
    Sum.inr (Sum.inr (25, 14)),
    Sum.inr (Sum.inr (397, 9)),
    Sum.inr (Sum.inr (390, 9)),
    Sum.inr (Sum.inr (18, 14)),
    Sum.inr (Sum.inr (152, 9)),
    Sum.inr (Sum.inr (268, 14)),
    Sum.inr (Sum.inr (263, 14)),
    Sum.inr (Sum.inr (147, 9)),
    Sum.inr (Sum.inr (25, 2)),
    Sum.inr (Sum.inr (397, 21)),
    Sum.inr (Sum.inr (390, 21)),
    Sum.inr (Sum.inr (18, 2)),
    Sum.inr (Sum.inr (152, 21)),
    Sum.inr (Sum.inr (268, 2)),
    Sum.inr (Sum.inr (263, 2)),
    Sum.inr (Sum.inr (147, 21)),
    Sum.inr (Sum.inr (496, 2)),
    Sum.inr (Sum.inr (238, 2)),
    Sum.inr (Sum.inr (175, 2)),
    Sum.inr (Sum.inr (433, 2)),
    Sum.inr (Sum.inr (37, 2)),
    Sum.inr (Sum.inr (315, 2)),
    Sum.inr (Sum.inr (378, 2)),
    Sum.inr (Sum.inr (100, 2)),
    Sum.inr (Sum.inr (507, 2)),
    Sum.inr (Sum.inr (229, 2)),
    Sum.inr (Sum.inr (164, 2)),
    Sum.inr (Sum.inr (442, 2)),
    Sum.inr (Sum.inr (46, 2)),
    Sum.inr (Sum.inr (304, 2)),
    Sum.inr (Sum.inr (369, 2)),
    Sum.inr (Sum.inr (111, 2)),
    Sum.inr (Sum.inr (111, 9)),
    Sum.inr (Sum.inr (369, 9)),
    Sum.inr (Sum.inr (304, 9)),
    Sum.inr (Sum.inr (46, 9)),
    Sum.inr (Sum.inr (442, 9)),
    Sum.inr (Sum.inr (164, 9)),
    Sum.inr (Sum.inr (229, 9)),
    Sum.inr (Sum.inr (507, 9))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock039Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨9984 + a.val, by omega⟩

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block039_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock039Input a
    let y := generatedSixthXiShortBlock039Output a
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
theorem generatedSixth_xi_short_block039_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock039Input a
    let y := generatedSixthXiShortBlock039Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block039_folded_certificate a
  simpa only [generatedSixth_xi_folded_phase] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block039_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock039Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block039_certificate a).1
    (generatedSixth_xi_short_block039_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
