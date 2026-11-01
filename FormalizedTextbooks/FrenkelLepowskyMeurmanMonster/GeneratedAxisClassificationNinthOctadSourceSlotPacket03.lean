/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacketCover

/-! Finite original descriptor and source-address checks on one consecutive packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000


set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_target_03_0 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨0, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_target_03_1 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨1, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_target_03_2 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨2, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_target_03_3 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨3, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_target_03_4 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨4, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_target_03_5 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨5, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_target_03_6 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨6, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_target_03_7 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨7, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  decide +kernel

/-- All original addresses in packet03 satisfy the complete target relation. -/
theorem generatedNinth_octad_slot_target_packet_03 : ∀ (m : Fin 64) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12) m
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  apply generatedNinth_slot_subpacket_cover_64
  intro b
  fin_cases b
  · exact slot_target_03_0
  · exact slot_target_03_1
  · exact slot_target_03_2
  · exact slot_target_03_3
  · exact slot_target_03_4
  · exact slot_target_03_5
  · exact slot_target_03_6
  · exact slot_target_03_7

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_distinct_03_0 : ∀ (m : Fin 8) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨0, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_distinct_03_1 : ∀ (m : Fin 8) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨1, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_distinct_03_2 : ∀ (m : Fin 8) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨2, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_distinct_03_3 : ∀ (m : Fin 8) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨3, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_distinct_03_4 : ∀ (m : Fin 8) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨4, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_distinct_03_5 : ∀ (m : Fin 8) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨5, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_distinct_03_6 : ∀ (m : Fin 8) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨6, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_distinct_03_7 : ∀ (m : Fin 8) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨7, by decide⟩ : Fin 8) m)
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  decide +kernel

/-- All original addresses in packet03 satisfy the complete distinct relation. -/
theorem generatedNinth_octad_slot_distinct_packet_03 : ∀ (m : Fin 64) (j l : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨3, by decide⟩ : Fin 12) m
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l →
          j = l := by
  apply generatedNinth_slot_subpacket_cover_64
  intro b
  fin_cases b
  · exact slot_distinct_03_0
  · exact slot_distinct_03_1
  · exact slot_distinct_03_2
  · exact slot_distinct_03_3
  · exact slot_distinct_03_4
  · exact slot_distinct_03_5
  · exact slot_distinct_03_6
  · exact slot_distinct_03_7

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
