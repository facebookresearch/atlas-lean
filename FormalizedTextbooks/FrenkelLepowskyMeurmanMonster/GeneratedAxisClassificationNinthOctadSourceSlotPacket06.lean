/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket06_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket06_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket06_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket06_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket06_04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket06_05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket06_06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket06_07

/-! Original finite source and target relations checked on a separately compiled interval. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- All original addresses in packet06 satisfy the complete target relation. -/
theorem generatedNinth_octad_slot_target_packet_06 : ∀ (m : Fin 64) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12) m
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  apply generatedNinth_slot_subpacket_cover_64
  intro c
  fin_cases c
  · exact generatedNinth_octad_slot_target_subpacket_06_00
  · exact generatedNinth_octad_slot_target_subpacket_06_01
  · exact generatedNinth_octad_slot_target_subpacket_06_02
  · exact generatedNinth_octad_slot_target_subpacket_06_03
  · exact generatedNinth_octad_slot_target_subpacket_06_04
  · exact generatedNinth_octad_slot_target_subpacket_06_05
  · exact generatedNinth_octad_slot_target_subpacket_06_06
  · exact generatedNinth_octad_slot_target_subpacket_06_07

/-- All original addresses in packet06 satisfy the complete distinct relation. -/
theorem generatedNinth_octad_slot_distinct_packet_06 : ∀ (m : Fin 64) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨6, by decide⟩ : Fin 12) m
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  apply generatedNinth_slot_subpacket_cover_64
  intro c
  fin_cases c
  · exact generatedNinth_octad_slot_distinct_subpacket_06_00
  · exact generatedNinth_octad_slot_distinct_subpacket_06_01
  · exact generatedNinth_octad_slot_distinct_subpacket_06_02
  · exact generatedNinth_octad_slot_distinct_subpacket_06_03
  · exact generatedNinth_octad_slot_distinct_subpacket_06_04
  · exact generatedNinth_octad_slot_distinct_subpacket_06_05
  · exact generatedNinth_octad_slot_distinct_subpacket_06_06
  · exact generatedNinth_octad_slot_distinct_subpacket_06_07

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
