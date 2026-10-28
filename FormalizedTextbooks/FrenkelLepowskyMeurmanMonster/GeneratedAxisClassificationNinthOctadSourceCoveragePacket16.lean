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
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_coverage_16_0 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨16, by decide⟩ : Fin 17)
      (generatedNinthSlotSubpacketIndex40 (⟨0, by decide⟩ : Fin 5) m)
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_coverage_16_1 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨16, by decide⟩ : Fin 17)
      (generatedNinthSlotSubpacketIndex40 (⟨1, by decide⟩ : Fin 5) m)
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_coverage_16_2 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨16, by decide⟩ : Fin 17)
      (generatedNinthSlotSubpacketIndex40 (⟨2, by decide⟩ : Fin 5) m)
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_coverage_16_3 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨16, by decide⟩ : Fin 17)
      (generatedNinthSlotSubpacketIndex40 (⟨3, by decide⟩ : Fin 5) m)
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check only the next8 original addresses in this unchanged descriptor relation.
private theorem slot_coverage_16_4 : ∀ m : Fin 8,
    let k := generatedNinthSourcePacketIndex (⟨16, by decide⟩ : Fin 17)
      (generatedNinthSlotSubpacketIndex40 (⟨4, by decide⟩ : Fin 5) m)
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  decide +kernel

/-- All original addresses in packet16 satisfy the complete coverage relation. -/
theorem generatedNinth_octad_slot_coverage_packet_16 : ∀ m : Fin 40,
    let k := generatedNinthSourcePacketIndex (⟨16, by decide⟩ : Fin 17) m
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  apply generatedNinth_slot_subpacket_cover_40
  intro b
  fin_cases b
  · exact slot_coverage_16_0
  · exact slot_coverage_16_1
  · exact slot_coverage_16_2
  · exact slot_coverage_16_3
  · exact slot_coverage_16_4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
