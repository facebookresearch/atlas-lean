/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceCoveragePacket16

/-! Sparse octad source slots agree with every relevant original target descriptor.
These finite address statements retain the original nonzero source predicate; they do not
replace the integer, binary action or full phase checks on those source rows. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
/-- Every nonempty octad slot uses a genuine nonzero original source and its displayed target. -/
theorem generatedNinth_octad_source_slot_target : ∀ (o : Fin 759) (j : Fin 8),
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
        generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
          Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j)) := by
  apply generatedNinth_octad_packet_cover
  intro b
  fin_cases b
  · exact generatedNinth_octad_slot_target_packet_00
  · exact generatedNinth_octad_slot_target_packet_01
  · exact generatedNinth_octad_slot_target_packet_02
  · exact generatedNinth_octad_slot_target_packet_03
  · exact generatedNinth_octad_slot_target_packet_04
  · exact generatedNinth_octad_slot_target_packet_05
  · exact generatedNinth_octad_slot_target_packet_06
  · exact generatedNinth_octad_slot_target_packet_07
  · exact generatedNinth_octad_slot_target_packet_08
  · exact generatedNinth_octad_slot_target_packet_09
  · exact generatedNinth_octad_slot_target_packet_10
  · exact generatedNinth_octad_slot_target_packet_11

set_option maxHeartbeats 0 in
/-- All original nonzero source rows whose descriptor is an octad occur in its sparse slots. -/
theorem generatedNinth_octad_source_slot_coverage : ∀ k : Fin 4136,
    generatedNinthShortRowNonzero k = true →
      match generatedNinthShortRowTarget k with
      | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
          generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
            generatedNinthOctadSourceSlotIndex o j = k ∧
              generatedNinthOctadSourceSlotSign o j = e
      | _ => True := by
  apply generatedNinth_source_packet_cover
  intro b
  fin_cases b
  · exact generatedNinth_octad_slot_coverage_packet_00
  · exact generatedNinth_octad_slot_coverage_packet_01
  · exact generatedNinth_octad_slot_coverage_packet_02
  · exact generatedNinth_octad_slot_coverage_packet_03
  · exact generatedNinth_octad_slot_coverage_packet_04
  · exact generatedNinth_octad_slot_coverage_packet_05
  · exact generatedNinth_octad_slot_coverage_packet_06
  · exact generatedNinth_octad_slot_coverage_packet_07
  · exact generatedNinth_octad_slot_coverage_packet_08
  · exact generatedNinth_octad_slot_coverage_packet_09
  · exact generatedNinth_octad_slot_coverage_packet_10
  · exact generatedNinth_octad_slot_coverage_packet_11
  · exact generatedNinth_octad_slot_coverage_packet_12
  · exact generatedNinth_octad_slot_coverage_packet_13
  · exact generatedNinth_octad_slot_coverage_packet_14
  · exact generatedNinth_octad_slot_coverage_packet_15
  · exact generatedNinth_octad_slot_coverage_packet_16

set_option maxHeartbeats 0 in
/-- Nonempty source addresses in the same octad are distinct. -/
theorem generatedNinth_octad_source_slot_distinct : ∀ (o : Fin 759) (j l : Fin 8),
    generatedNinthOctadSourceSlotWord o j ≠ 0 →
      generatedNinthOctadSourceSlotWord o l ≠ 0 →
        generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l → j = l := by
  apply generatedNinth_octad_packet_cover
  intro b
  fin_cases b
  · exact generatedNinth_octad_slot_distinct_packet_00
  · exact generatedNinth_octad_slot_distinct_packet_01
  · exact generatedNinth_octad_slot_distinct_packet_02
  · exact generatedNinth_octad_slot_distinct_packet_03
  · exact generatedNinth_octad_slot_distinct_packet_04
  · exact generatedNinth_octad_slot_distinct_packet_05
  · exact generatedNinth_octad_slot_distinct_packet_06
  · exact generatedNinth_octad_slot_distinct_packet_07
  · exact generatedNinth_octad_slot_distinct_packet_08
  · exact generatedNinth_octad_slot_distinct_packet_09
  · exact generatedNinth_octad_slot_distinct_packet_10
  · exact generatedNinth_octad_slot_distinct_packet_11

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
