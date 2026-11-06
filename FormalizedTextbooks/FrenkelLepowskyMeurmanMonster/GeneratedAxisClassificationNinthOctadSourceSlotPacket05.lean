/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket05_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket05_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket05_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket05_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket05_04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket05_05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket05_06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacket05_07

/-! Original finite source and target relations checked on a separately compiled interval. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- All original addresses in packet05 satisfy the complete target relation. -/
theorem generatedNinth_octad_slot_target_packet_05 : ∀ (m : Fin 64) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨5, by decide⟩ : Fin 12) m
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  apply generatedNinth_slot_subpacket_cover_64
  intro c
  fin_cases c
  · exact generatedNinth_octad_slot_target_subpacket_05_00
  · exact generatedNinth_octad_slot_target_subpacket_05_01
  · exact generatedNinth_octad_slot_target_subpacket_05_02
  · exact generatedNinth_octad_slot_target_subpacket_05_03
  · exact generatedNinth_octad_slot_target_subpacket_05_04
  · exact generatedNinth_octad_slot_target_subpacket_05_05
  · exact generatedNinth_octad_slot_target_subpacket_05_06
  · exact generatedNinth_octad_slot_target_subpacket_05_07

/-- All original addresses in packet05 satisfy the complete distinct relation. -/
theorem generatedNinth_octad_slot_distinct_packet_05 : ∀ (m : Fin 64) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨5, by decide⟩ : Fin 12) m
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  apply generatedNinth_slot_subpacket_cover_64
  intro c
  fin_cases c
  · exact generatedNinth_octad_slot_distinct_subpacket_05_00
  · exact generatedNinth_octad_slot_distinct_subpacket_05_01
  · exact generatedNinth_octad_slot_distinct_subpacket_05_02
  · exact generatedNinth_octad_slot_distinct_subpacket_05_03
  · exact generatedNinth_octad_slot_distinct_subpacket_05_04
  · exact generatedNinth_octad_slot_distinct_subpacket_05_05
  · exact generatedNinth_octad_slot_distinct_subpacket_05_06
  · exact generatedNinth_octad_slot_distinct_subpacket_05_07

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
