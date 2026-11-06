/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoverageChunk01_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoverageChunk01_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoverageChunk01_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoverageChunk01_03

/-! Original finite source and target relations checked on a separately compiled interval. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Every original nonzero source in packet01 occurs in its octad slots. -/
theorem generatedNinth_octad_slot_coverage_packet_01 : ∀ m : Fin 256,
    let k := generatedNinthSourcePacketIndex (⟨1, by decide⟩ : Fin 17) m
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  apply generatedNinth_coverage_chunk_cover
  intro c
  fin_cases c
  · exact generatedNinth_octad_slot_coverage_chunk_01_00
  · exact generatedNinth_octad_slot_coverage_chunk_01_01
  · exact generatedNinth_octad_slot_coverage_chunk_01_02
  · exact generatedNinth_octad_slot_coverage_chunk_01_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
