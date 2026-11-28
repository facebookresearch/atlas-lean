/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RuralPostmanDefs

namespace MetaMathlibExt.Complexity.NPComplete.RuralPostman

open MetaMathlibExt.BitstringEncoding

/-- The triangle `0, 1, 2` with unit lengths; the edges `{0, 1}` and `{1, 2}` are required;
the bound is `3`. -/
private abbrev triangle : RuralPostmanInstance :=
  (3, [(0, 1, 1), (1, 2, 1), (0, 2, 1)], [(0, 1), (1, 2)], 3)

private theorem triangle_wellFormed : WellFormed triangle := by unfold WellFormed; decide

private theorem tri01 : (Graph triangle : SimpleGraph (Fin 3)).Adj 0 1 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem tri12 : (Graph triangle : SimpleGraph (Fin 3)).Adj 1 2 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem tri20 : (Graph triangle : SimpleGraph (Fin 3)).Adj 2 0 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The closed walk `0, 1, 2, 0` traverses both required edges and has length `3`; walking
`0, 1, 2, 1, 0` instead would cost `4`. -/
private theorem triangle_feasible : RuralPostmanFeasible triangle :=
  ⟨0, .cons tri01 (.cons tri12 (.cons tri20 .nil)), by decide, by decide⟩

/-- A single edge `{0, 1}` of length `2`, required, with bound `B`. -/
private abbrev single (B : ℕ) : RuralPostmanInstance := (2, [(0, 1, 2)], [(0, 1)], B)

/-- `single 3` is well formed. -/
example : WellFormed (single 3) := by unfold WellFormed; decide

private theorem single_four_wellFormed : WellFormed (single 4) := by unfold WellFormed; decide

private theorem single01 : (Graph (single 4) : SimpleGraph (Fin 2)).Adj 0 1 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- Going to `1` and back costs `2 + 2 = 4`. -/
private theorem single_four_feasible : RuralPostmanFeasible (single 4) :=
  ⟨0, .cons single01 (.cons single01.symm .nil), by decide, by decide⟩

/-- Every edge of `single 3` has length `2`. -/
private theorem single_edgeLength {e : Sym2 (Fin 2)}
    (he : e ∈ (Graph (single 3) : SimpleGraph (Fin 2)).edgeSet) :
    edgeLength (single 3) e = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    fin_cases a <;> fin_cases b
    · exact absurd he (SimpleGraph.irrefl _)
    · decide
    · decide
    · exact absurd he (SimpleGraph.irrefl _)

/-- A closed walk with an edge has at least two edges: a simple graph has no loops. -/
private theorem closed_walk_two {V : Type} {G : SimpleGraph V} {v : V} (c : G.Walk v v)
    (hne : c.edges ≠ []) : 2 ≤ c.length := by
  cases c with
  | nil => simp at hne
  | cons h q =>
    cases q with
    | nil => exact absurd h (SimpleGraph.irrefl _)
    | cons _ _ => simp

/-- `single 3` is infeasible: a closed walk through `{0, 1}` must come back over it, which
costs `4 > 3`, although one traversal alone (`2`) is within the bound. -/
private theorem single_three_infeasible : ¬ RuralPostmanFeasible (single 3) := by
  rintro ⟨v, c, hreq, hle⟩
  have hne : c.edges ≠ [] := by
    intro h
    have := hreq (0, 1) (by simp)
    simp [h] at this
  have hconst : c.edges.map (edgeLength (single 3)) = c.edges.map fun _ => 2 :=
    List.map_congr_left fun e he => single_edgeLength (c.edges_subset_edgeSet he)
  rw [hconst, List.map_const', List.sum_replicate, SimpleGraph.Walk.length_edges] at hle
  have := closed_walk_two c hne
  simp at hle
  omega

/-- A required pair that is not an edge is malformed. -/
example : ¬ WellFormed ((3, [(0, 1, 1)], [(1, 2)], 5) : RuralPostmanInstance) := by
  unfold WellFormed; decide

/-- The decision problem accepts the encodings of the triangle and of `single 4`. -/
example : ruralPostmanDec (bitEncode triangle) = true ∧
    ruralPostmanDec (bitEncode (single 4)) = true :=
  ⟨by simp [ruralPostmanDec, triangle_wellFormed, triangle_feasible],
    by simp [ruralPostmanDec, single_four_wellFormed, single_four_feasible]⟩

/-- It rejects the encoding of the well-formed but infeasible `single 3`. -/
example : ruralPostmanDec (bitEncode (single 3)) = false := by
  simp [ruralPostmanDec, single_three_infeasible]

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : ruralPostmanDec [true] = false := by
  have h : bitDecode (α := RuralPostmanInstance) [true] = none := rfl
  simp [ruralPostmanDec, h]

end MetaMathlibExt.Complexity.NPComplete.RuralPostman
