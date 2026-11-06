/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket04_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket04_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket04_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket04_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket04_04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket04_05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket04_06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket04_07

/-! Original finite source and target relations checked on a separately compiled interval. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- All original addresses in packet04 satisfy the complete target relation. -/
theorem generatedNinth_octad_slot_target_packet_04 : ∀ (m : Fin 64) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨4, by decide⟩ : Fin 12) m
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  apply generatedNinth_slot_subpacket_cover_64
  intro c
  fin_cases c
  · exact generatedNinth_octad_slot_target_subpacket_04_00
  · exact generatedNinth_octad_slot_target_subpacket_04_01
  · exact generatedNinth_octad_slot_target_subpacket_04_02
  · exact generatedNinth_octad_slot_target_subpacket_04_03
  · exact generatedNinth_octad_slot_target_subpacket_04_04
  · exact generatedNinth_octad_slot_target_subpacket_04_05
  · exact generatedNinth_octad_slot_target_subpacket_04_06
  · exact generatedNinth_octad_slot_target_subpacket_04_07

/-- All original addresses in packet04 satisfy the complete distinct relation. -/
theorem generatedNinth_octad_slot_distinct_packet_04 : ∀ (m : Fin 64) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨4, by decide⟩ : Fin 12) m
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  apply generatedNinth_slot_subpacket_cover_64
  intro c
  fin_cases c
  · exact generatedNinth_octad_slot_distinct_subpacket_04_00
  · exact generatedNinth_octad_slot_distinct_subpacket_04_01
  · exact generatedNinth_octad_slot_distinct_subpacket_04_02
  · exact generatedNinth_octad_slot_distinct_subpacket_04_03
  · exact generatedNinth_octad_slot_distinct_subpacket_04_04
  · exact generatedNinth_octad_slot_distinct_subpacket_04_05
  · exact generatedNinth_octad_slot_distinct_subpacket_04_06
  · exact generatedNinth_octad_slot_distinct_subpacket_04_07

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
