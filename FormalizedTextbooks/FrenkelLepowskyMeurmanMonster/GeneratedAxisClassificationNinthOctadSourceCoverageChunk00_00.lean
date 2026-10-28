/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotSubpacketCover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoverageChunkCover

/-! Original finite source and target relations checked on a separately compiled interval. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

private instance slot_coverage_decidable (k : Fin 4136) :
    Decidable (match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True) := by
  generalize generatedNinthShortRowTarget k = r
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  all_goals infer_instance

set_option maxHeartbeats 40000000 in
-- Preserve every original source and target field on the next eight source addresses.
private theorem slot_coverage_00_00_00 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨0, by decide⟩ : Fin 17)
      (generatedNinthCoverageChunkIndex (⟨0, by decide⟩ : Fin 4)
      (generatedNinthSlotSubpacketIndex64 (⟨0, by decide⟩ : Fin 8) m))
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve every original source and target field on the next eight source addresses.
private theorem slot_coverage_00_00_01 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨0, by decide⟩ : Fin 17)
      (generatedNinthCoverageChunkIndex (⟨0, by decide⟩ : Fin 4)
      (generatedNinthSlotSubpacketIndex64 (⟨1, by decide⟩ : Fin 8) m))
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve every original source and target field on the next eight source addresses.
private theorem slot_coverage_00_00_02 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨0, by decide⟩ : Fin 17)
      (generatedNinthCoverageChunkIndex (⟨0, by decide⟩ : Fin 4)
      (generatedNinthSlotSubpacketIndex64 (⟨2, by decide⟩ : Fin 8) m))
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve every original source and target field on the next eight source addresses.
private theorem slot_coverage_00_00_03 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨0, by decide⟩ : Fin 17)
      (generatedNinthCoverageChunkIndex (⟨0, by decide⟩ : Fin 4)
      (generatedNinthSlotSubpacketIndex64 (⟨3, by decide⟩ : Fin 8) m))
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve every original source and target field on the next eight source addresses.
private theorem slot_coverage_00_00_04 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨0, by decide⟩ : Fin 17)
      (generatedNinthCoverageChunkIndex (⟨0, by decide⟩ : Fin 4)
      (generatedNinthSlotSubpacketIndex64 (⟨4, by decide⟩ : Fin 8) m))
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve every original source and target field on the next eight source addresses.
private theorem slot_coverage_00_00_05 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨0, by decide⟩ : Fin 17)
      (generatedNinthCoverageChunkIndex (⟨0, by decide⟩ : Fin 4)
      (generatedNinthSlotSubpacketIndex64 (⟨5, by decide⟩ : Fin 8) m))
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve every original source and target field on the next eight source addresses.
private theorem slot_coverage_00_00_06 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨0, by decide⟩ : Fin 17)
      (generatedNinthCoverageChunkIndex (⟨0, by decide⟩ : Fin 4)
      (generatedNinthSlotSubpacketIndex64 (⟨6, by decide⟩ : Fin 8) m))
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Preserve every original source and target field on the next eight source addresses.
private theorem slot_coverage_00_00_07 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨0, by decide⟩ : Fin 17)
      (generatedNinthCoverageChunkIndex (⟨0, by decide⟩ : Fin 4)
      (generatedNinthSlotSubpacketIndex64 (⟨7, by decide⟩ : Fin 8) m))
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

/-- Complete original source-slot coverage on sixty-four addresses in packet00. -/
theorem generatedNinth_octad_slot_coverage_chunk_00_00 : ∀ m : Fin 64,
    let k := generatedNinthSourcePacketIndex (⟨0, by decide⟩ : Fin 17)
      (generatedNinthCoverageChunkIndex (⟨0, by decide⟩ : Fin 4) m)
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  apply generatedNinth_slot_subpacket_cover_64
  intro t
  fin_cases t
  · exact slot_coverage_00_00_00
  · exact slot_coverage_00_00_01
  · exact slot_coverage_00_00_02
  · exact slot_coverage_00_00_03
  · exact slot_coverage_00_00_04
  · exact slot_coverage_00_00_05
  · exact slot_coverage_00_00_06
  · exact slot_coverage_00_00_07

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
