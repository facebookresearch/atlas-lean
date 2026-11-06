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
private theorem slot_numerator_11_0 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨11, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex55 (⟨0, by decide⟩ : Fin 7) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_11_1 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨11, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex55 (⟨1, by decide⟩ : Fin 7) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_11_2 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨11, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex55 (⟨2, by decide⟩ : Fin 7) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_11_3 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨11, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex55 (⟨3, by decide⟩ : Fin 7) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_11_4 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨11, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex55 (⟨4, by decide⟩ : Fin 7) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_11_5 : ∀ (m : Fin 8) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨11, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex55 (⟨5, by decide⟩ : Fin 7) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve the original signed numerator in every selected chronological source slot.
private theorem slot_numerator_11_6 : ∀ (m : Fin 7) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨11, by decide⟩ : Fin 12)
      (generatedNinthSlotSubpacketIndex55 (⟨6, by decide⟩ : Fin 7) m)
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  simp_rw [generatedNinth_short_row_numerator_fast_actual]
  decide +kernel

/-- Each slot in packet11 has its original full signed integer numerator. -/
theorem generatedNinth_octad_slot_numerator_packet_11 : ∀ (m : Fin 55) (j : Fin 8),
    let o := generatedNinthOctadPacketIndex (⟨11, by decide⟩ : Fin 12) m
    (if generatedNinthOctadSourceSlotWord o j ≠ 0 then
      nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0) =
      generatedNinthOctadSlotNumeratorFast o j := by
  apply generatedNinth_slot_subpacket_cover_55
  intro b
  fin_cases b
  · exact slot_numerator_11_0
  · exact slot_numerator_11_1
  · exact slot_numerator_11_2
  · exact slot_numerator_11_3
  · exact slot_numerator_11_4
  · exact slot_numerator_11_5
  · exact slot_numerator_11_6

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
