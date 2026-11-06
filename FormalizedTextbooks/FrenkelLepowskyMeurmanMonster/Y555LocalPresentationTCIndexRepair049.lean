/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The unchanged long replacement chain passes the exact checker by segmented replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepairSegments049

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 32000000 in
-- Combine the separately checked bounds of the exact consecutive context chunks.
/-- All replacement references and signed letters retain their exact original bounds. -/
theorem y322TCIndexRepairAllowed049 :
    ∀ move ∈ y322TCIndexRepairRaw049, move.Allowed 48648 226454 := by
  intro move hm
  simp only [y322TCIndexRepairRaw049, List.mem_flatten, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  obtain ⟨chunk, hc, hm⟩ := hm
  rcases hc with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact y322TCIndexRepair049ChunkAllowed000 move hm
  · exact y322TCIndexRepair049ChunkAllowed001 move hm
  · exact y322TCIndexRepair049ChunkAllowed002 move hm
  · exact y322TCIndexRepair049ChunkAllowed003 move hm
  · exact y322TCIndexRepair049ChunkAllowed004 move hm
  · exact y322TCIndexRepair049ChunkAllowed005 move hm
  · exact y322TCIndexRepair049ChunkAllowed006 move hm
  · exact y322TCIndexRepair049ChunkAllowed007 move hm
  · exact y322TCIndexRepair049ChunkAllowed008 move hm
  · exact y322TCIndexRepair049ChunkAllowed009 move hm
  · exact y322TCIndexRepair049ChunkAllowed010 move hm
  · exact y322TCIndexRepair049ChunkAllowed011 move hm
  · exact y322TCIndexRepair049ChunkAllowed012 move hm
  · exact y322TCIndexRepair049ChunkAllowed013 move hm
  · exact y322TCIndexRepair049ChunkAllowed014 move hm
  · exact y322TCIndexRepair049ChunkAllowed015 move hm
  · exact y322TCIndexRepair049ChunkAllowed016 move hm
  · exact y322TCIndexRepair049ChunkAllowed017 move hm
  · exact y322TCIndexRepair049ChunkAllowed018 move hm
  · exact y322TCIndexRepair049ChunkAllowed019 move hm
  · exact y322TCIndexRepair049ChunkAllowed020 move hm
  · exact y322TCIndexRepair049ChunkAllowed021 move hm
  · exact y322TCIndexRepair049ChunkAllowed022 move hm
  · exact y322TCIndexRepair049ChunkAllowed023 move hm
  · exact y322TCIndexRepair049ChunkAllowed024 move hm
  · exact y322TCIndexRepair049ChunkAllowed025 move hm
  · exact y322TCIndexRepair049ChunkAllowed026 move hm
  · exact y322TCIndexRepair049ChunkAllowed027 move hm
  · exact y322TCIndexRepair049ChunkAllowed028 move hm
  · exact y322TCIndexRepair049ChunkAllowed029 move hm
  · exact y322TCIndexRepair049ChunkAllowed030 move hm
  · exact y322TCIndexRepair049ChunkAllowed031 move hm
  · exact y322TCIndexRepair049ChunkAllowed032 move hm
  · exact y322TCIndexRepair049ChunkAllowed033 move hm
  · exact y322TCIndexRepair049ChunkAllowed034 move hm
  · exact y322TCIndexRepair049ChunkAllowed035 move hm
  · exact y322TCIndexRepair049ChunkAllowed036 move hm
  · exact y322TCIndexRepair049ChunkAllowed037 move hm
  · exact y322TCIndexRepair049ChunkAllowed038 move hm
  · exact y322TCIndexRepair049ChunkAllowed039 move hm
  · exact y322TCIndexRepair049ChunkAllowed040 move hm
  · exact y322TCIndexRepair049ChunkAllowed041 move hm
  · exact y322TCIndexRepair049ChunkAllowed042 move hm
  · exact y322TCIndexRepair049ChunkAllowed043 move hm
  · exact y322TCIndexRepair049ChunkAllowed044 move hm
  · exact y322TCIndexRepair049ChunkAllowed045 move hm
  · exact y322TCIndexRepair049ChunkAllowed046 move hm
  · exact y322TCIndexRepair049ChunkAllowed047 move hm
  · exact y322TCIndexRepair049ChunkAllowed048 move hm
  · exact y322TCIndexRepair049ChunkAllowed049 move hm
  · exact y322TCIndexRepair049ChunkAllowed050 move hm
  · exact y322TCIndexRepair049ChunkAllowed051 move hm
  · exact y322TCIndexRepair049ChunkAllowed052 move hm
  · exact y322TCIndexRepair049ChunkAllowed053 move hm
  · exact y322TCIndexRepair049ChunkAllowed054 move hm
  · exact y322TCIndexRepair049ChunkAllowed055 move hm
  · exact y322TCIndexRepair049ChunkAllowed056 move hm
  · exact y322TCIndexRepair049ChunkAllowed057 move hm
  · exact y322TCIndexRepair049ChunkAllowed058 move hm
  · exact y322TCIndexRepair049ChunkAllowed059 move hm
  · exact y322TCIndexRepair049ChunkAllowed060 move hm
  · exact y322TCIndexRepair049ChunkAllowed061 move hm
  · exact y322TCIndexRepair049ChunkAllowed062 move hm
  · exact y322TCIndexRepair049ChunkAllowed063 move hm
  · exact y322TCIndexRepair049ChunkAllowed064 move hm
  · exact y322TCIndexRepair049ChunkAllowed065 move hm
  · exact y322TCIndexRepair049ChunkAllowed066 move hm
  · exact y322TCIndexRepair049ChunkAllowed067 move hm
  · exact y322TCIndexRepair049ChunkAllowed068 move hm
  · exact y322TCIndexRepair049ChunkAllowed069 move hm
  · exact y322TCIndexRepair049ChunkAllowed070 move hm
  · exact y322TCIndexRepair049ChunkAllowed071 move hm
  · exact y322TCIndexRepair049ChunkAllowed072 move hm
  · exact y322TCIndexRepair049ChunkAllowed073 move hm
  · exact y322TCIndexRepair049ChunkAllowed074 move hm
  · exact y322TCIndexRepair049ChunkAllowed075 move hm

set_option maxHeartbeats 32000000 in
-- Exact replay concatenation combines the kernel-checked consecutive segments.
/-- The unchanged complete replacement chain passes its original exact context checker. -/
theorem y322TCIndexRepairChecked049 :
    y322TCIndexRepairChecked ⟨149211, by decide⟩ y322TCIndexRepairRaw049
      y322TCIndexRepairAllowed049 := by
  unfold y322TCIndexRepairChecked
  rw [← y322TCIndexRepair049Boundary_left, ← y322TCIndexRepair049Boundary_right]
  simp only [y322TCIndexRepairRaw049, List.flatten_cons, List.flatten_nil]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun000, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun001, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun002, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun003, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun004, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun005, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun006, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun007, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun008, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun009, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun010, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun011, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun012, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun013, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun014, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun015, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun016, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun017, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun018, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun019, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun020, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun021, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun022, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun023, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun024, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun025, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun026, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun027, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun028, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun029, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun030, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun031, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun032, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun033, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun034, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun035, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun036, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun037, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun038, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun039, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun040, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun041, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun042, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun043, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun044, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun045, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun046, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun047, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun048, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun049, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun050, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun051, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun052, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun053, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun054, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun055, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun056, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun057, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun058, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun059, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun060, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun061, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun062, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun063, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun064, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun065, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun066, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun067, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun068, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun069, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun070, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun071, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun072, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun073, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun074, Option.bind_some]
  rw [y322TCIndexRepairMoves_append, y322TCIndexRepairRun_append,
    y322TCIndexRepair049SegmentRun075, Option.bind_some]
  rw [y322TCIndexRepairMoves_nil, y322TCIndexRepairRun_nil,
    y322TCIndexRepair049Boundary_reduced]

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid049
    (hp : ∀ j : Fin 174819, j.val < 149211 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149211, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed049
    y322TCIndexRepairChecked049 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
