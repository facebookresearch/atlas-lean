/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorPacket11

/-! Complete finite packet coverage retains the original signed integer source numerator
in every nonempty octad slot. Actual word action is checked independently. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every octad slot has the original full signed source numerator specified by its cache. -/
theorem generatedNinth_octad_slot_numerator_actual (o : Fin 759) (j : Fin 8) :
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  have h : ∀ o : Fin 759, ∀ j : Fin 8,
      (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
        nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
          generatedNinthOriginalShortNumerator
            (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
        generatedNinthOctadSlotNumeratorFast o j := by
    apply generatedNinth_octad_packet_cover
    intro b
    fin_cases b
    · exact generatedNinth_octad_slot_numerator_packet_00
    · exact generatedNinth_octad_slot_numerator_packet_01
    · exact generatedNinth_octad_slot_numerator_packet_02
    · exact generatedNinth_octad_slot_numerator_packet_03
    · exact generatedNinth_octad_slot_numerator_packet_04
    · exact generatedNinth_octad_slot_numerator_packet_05
    · exact generatedNinth_octad_slot_numerator_packet_06
    · exact generatedNinth_octad_slot_numerator_packet_07
    · exact generatedNinth_octad_slot_numerator_packet_08
    · exact generatedNinth_octad_slot_numerator_packet_09
    · exact generatedNinth_octad_slot_numerator_packet_10
    · exact generatedNinth_octad_slot_numerator_packet_11
  exact h o j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
