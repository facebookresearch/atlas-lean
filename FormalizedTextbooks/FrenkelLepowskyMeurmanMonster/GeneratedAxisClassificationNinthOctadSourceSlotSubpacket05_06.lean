/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotFourChunk05_06_0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotFourChunk05_06_1

/-! Original finite source and target relations checked on a separately compiled interval. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- The original target relation on subpacket05,06. -/
theorem generatedNinth_octad_slot_target_subpacket_05_06 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨5, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨6, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  intro m
  obtain ⟨h, n, rfl⟩ := generatedNinth_slot_four_chunk_cover8 m
  fin_cases h
  · exact generatedNinth_octad_slot_target_four_chunk_05_06_0 n
  · exact generatedNinth_octad_slot_target_four_chunk_05_06_1 n

/-- The original distinct relation on subpacket05,06. -/
theorem generatedNinth_octad_slot_distinct_subpacket_05_06 : ∀ (m : Fin 8) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨5, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨6, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  intro m
  obtain ⟨h, n, rfl⟩ := generatedNinth_slot_four_chunk_cover8 m
  fin_cases h
  · exact generatedNinth_octad_slot_distinct_four_chunk_05_06_0 n
  · exact generatedNinth_octad_slot_distinct_four_chunk_05_06_1 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
