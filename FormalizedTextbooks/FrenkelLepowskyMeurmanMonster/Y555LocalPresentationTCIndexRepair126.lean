/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The unchanged long replacement chain passes the exact checker by segmented replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepairSegments126

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 32000000 in
-- Combine the separately checked bounds of the exact consecutive context chunks.
/-- All replacement references and signed letters retain their exact original bounds. -/
theorem y322TCIndexRepairAllowed126 :
    ∀ move ∈ y322TCIndexRepairRaw126, move.Allowed 48648 227062 := by
  intro move hm
  simp only [y322TCIndexRepairRaw126, List.mem_flatten, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  obtain ⟨chunk, hc, hm⟩ := hm
  rcases hc with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact y322TCIndexRepair126ChunkAllowed000 move hm
  · exact y322TCIndexRepair126ChunkAllowed001 move hm
  · exact y322TCIndexRepair126ChunkAllowed002 move hm
  · exact y322TCIndexRepair126ChunkAllowed003 move hm
  · exact y322TCIndexRepair126ChunkAllowed004 move hm
  · exact y322TCIndexRepair126ChunkAllowed005 move hm
  · exact y322TCIndexRepair126ChunkAllowed006 move hm
  · exact y322TCIndexRepair126ChunkAllowed007 move hm
  · exact y322TCIndexRepair126ChunkAllowed008 move hm
  · exact y322TCIndexRepair126ChunkAllowed009 move hm
  · exact y322TCIndexRepair126ChunkAllowed010 move hm
  · exact y322TCIndexRepair126ChunkAllowed011 move hm
  · exact y322TCIndexRepair126ChunkAllowed012 move hm
  · exact y322TCIndexRepair126ChunkAllowed013 move hm
  · exact y322TCIndexRepair126ChunkAllowed014 move hm
  · exact y322TCIndexRepair126ChunkAllowed015 move hm

set_option maxHeartbeats 32000000 in
-- Exact replay concatenation combines the kernel-checked consecutive segments.
/-- The unchanged complete replacement chain passes its original exact context checker. -/
theorem y322TCIndexRepairChecked126 :
    y322TCIndexRepairChecked ⟨149819, by decide⟩ y322TCIndexRepairRaw126
      y322TCIndexRepairAllowed126 := by
  unfold y322TCIndexRepairChecked
  rw [← y322TCIndexRepair126Boundary_left, ← y322TCIndexRepair126Boundary_right]
  simp only [y322TCIndexRepairRaw126, List.flatten_cons, List.flatten_nil]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun000, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun001, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun002, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun003, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun004, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun005, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun006, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun007, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun008, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun009, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun010, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun011, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun012, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun013, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun014, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair126SegmentRun015, Option.bind_some]
  rw [y322TCIndexRepairMoves_nil, y322TCIndexRepairRun_nil,
    y322TCIndexRepair126Boundary_reduced]

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid126
    (hp : ∀ j : Fin 174819, j.val < 149819 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149819, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed126
    y322TCIndexRepairChecked126 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
