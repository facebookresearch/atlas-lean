/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacketCover

/-! The displayed slot signs are compared with the original signed integer source
numerator. Actual full-word phases remain independently checked in the source-row family. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_10_0 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨10, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨0, by decide⟩ : Fin 8) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_10_1 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨10, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨1, by decide⟩ : Fin 8) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_10_2 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨10, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨2, by decide⟩ : Fin 8) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_10_3 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨10, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨3, by decide⟩ : Fin 8) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_10_4 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨10, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨4, by decide⟩ : Fin 8) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_10_5 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨10, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨5, by decide⟩ : Fin 8) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_10_6 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨10, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨6, by decide⟩ : Fin 8) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_10_7 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨10, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex64 (⟨7, by decide⟩ : Fin 8) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

/-- Each slot in packet10 has its original full signed integer numerator. -/
theorem generatedNinth_octad_slot_numerator_packet_10 : ∀ (m : Fin 64) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨10, by decide⟩ : Fin 12) m
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  apply generatedNinth_slot_subpacket_cover_64
  intro b
  fin_cases b
  · exact slot_numerator_10_0
  · exact slot_numerator_10_1
  · exact slot_numerator_10_2
  · exact slot_numerator_10_3
  · exact slot_numerator_10_4
  · exact slot_numerator_10_5
  · exact slot_numerator_10_6
  · exact slot_numerator_10_7

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
