/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GrandTourDefs

namespace MetaMathlibExt.Complexity.NPComplete.GrandTour

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Adjacency in a box product of graphs with decidable adjacency is decidable. -/
local instance {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α)
    (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := fun _ _ =>
  decidable_of_iff' _ SimpleGraph.boxProd_adj

private theorem accepts_encoding (i : GrandTourInstance) :
    grandTourDec (bitEncode i) = true ↔ WellFormed i ∧ GrandTourFeasible i := by
  simp [grandTourDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : grandTourDec [true] = false := by
  have h : bitDecode (α := GrandTourInstance) [true] = none := rfl
  simp [grandTourDec, h]

/-- A `2 × 2` grid forcing the top edge and the right edge. -/
private abbrev sq : GrandTourInstance :=
  [[(true, false), (false, true)], [(false, false), (false, false)]]

private abbrev p00 : Fin (rows sq) × Fin (cols sq) := (⟨0, by decide⟩, ⟨0, by decide⟩)
private abbrev p01 : Fin (rows sq) × Fin (cols sq) := (⟨0, by decide⟩, ⟨1, by decide⟩)
private abbrev p11 : Fin (rows sq) × Fin (cols sq) := (⟨1, by decide⟩, ⟨1, by decide⟩)
private abbrev p10 : Fin (rows sq) × Fin (cols sq) := (⟨1, by decide⟩, ⟨0, by decide⟩)

/-- The tour around the four points. -/
private abbrev tour : (Grid sq).Walk p00 p00 :=
  .cons (v := p01) (by decide) <| .cons (v := p11) (by decide) <|
    .cons (v := p10) (by decide) <| .cons (by decide) .nil

/-- The tour around a `2 × 2` grid is Hamiltonian and uses both forced edges. -/
example : grandTourDec (bitEncode sq) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, p00, tour, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one,
      SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    decide
  · unfold Forced
    decide

/-- The forced edges are read from the flags: the tour has an edge between the two bottom points,
which is not forced. -/
example : Forced sq p00 p01 ∧ Forced sq p01 p11 ∧ ¬ Forced sq p10 p11 := by
  unfold Forced
  decide

/-- A grid with fewer than three points has no cycle. -/
private theorem no_cycle {V : Type*} [Finite V] {G : SimpleGraph V} (hV : Nat.card V < 3) {u : V}
    (p : G.Walk u u) : ¬ p.IsCycle := fun h => by
  have := h.three_le_length
  have := h.length_le_natCard
  omega

/-- A well-formed row of two points with its edge forced has no Hamiltonian cycle. -/
example : grandTourDec (bitEncode ([[(true, false), (false, false)]] : GrandTourInstance)) =
    false := by
  have h : ¬ GrandTourFeasible [[(true, false), (false, false)]] := by
    rintro ⟨u, c, hc, -⟩
    exact no_cycle (by simp [rows, cols]) c hc.isCycle
  simpa [grandTourDec, bitDecode_bitEncode] using fun _ => h

/-- A forced edge to the right of the last column is malformed. -/
example : grandTourDec (bitEncode ([[(false, false), (true, false)],
    [(false, false), (false, false)]] : GrandTourInstance)) = false := by
  have h : ¬ WellFormed [[(false, false), (true, false)], [(false, false), (false, false)]] := by
    unfold WellFormed
    decide
  simp [grandTourDec, bitDecode_bitEncode, h]

end MetaMathlibExt.Complexity.NPComplete.GrandTour
