/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotFourChunkCover

/-! Original finite source and target relations checked on a separately compiled interval. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 40000000 in
-- Full literal source and target reductions exceed the default heartbeat budget.
/-- The original target relation on four-address chunk07,02,1. -/
theorem generatedNinth_octad_slot_target_four_chunk_07_02_1 : ∀ (n : Fin 4) (j : Fin 8),
    let m := generatedNinthSlotFourChunkIndex8 1 n
    let o := generatedNinthOctadPacketIndex (⟨7, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨2, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Full literal source and target reductions exceed the default heartbeat budget.
/-- The original distinct relation on four-address chunk07,02,1. -/
theorem generatedNinth_octad_slot_distinct_four_chunk_07_02_1 : ∀ (n : Fin 4) (j l : Fin 8),
    let m := generatedNinthSlotFourChunkIndex8 1 n
    let o := generatedNinthOctadPacketIndex (⟨7, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨2, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
