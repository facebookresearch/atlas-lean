/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RuralPostmanUnitLengthsDefs

namespace MetaMathlibExt.Complexity.NPComplete.RuralPostmanUnitLengths

open MetaMathlibExt.BitstringEncoding
open RuralPostman (RuralPostmanInstance RuralPostmanFeasible Graph edgeLength)

/-- The triangle `0, 1, 2` with unit lengths; the edges `{0, 1}` and `{1, 2}` are required;
the bound is `3`. -/
private abbrev triangle : RuralPostmanInstance :=
  (3, [(0, 1, 1), (1, 2, 1), (0, 2, 1)], [(0, 1), (1, 2)], 3)

private theorem triangle_wellFormed : WellFormed triangle := by
  unfold WellFormed RuralPostman.WellFormed; decide

private theorem tri01 : (Graph triangle : SimpleGraph (Fin 3)).Adj 0 1 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem tri12 : (Graph triangle : SimpleGraph (Fin 3)).Adj 1 2 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem tri20 : (Graph triangle : SimpleGraph (Fin 3)).Adj 2 0 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The closed walk `0, 1, 2, 0` traverses both required edges and has length `3`. -/
private theorem triangle_feasible : RuralPostmanFeasible triangle :=
  ⟨0, .cons tri01 (.cons tri12 (.cons tri20 .nil)), by decide, by decide⟩

/-- A single unit edge `{0, 1}`, required, with bound `1`. -/
private abbrev single : RuralPostmanInstance := (2, [(0, 1, 1)], [(0, 1)], 1)

private theorem single_wellFormed : WellFormed single := by
  unfold WellFormed RuralPostman.WellFormed; decide

/-- Every edge of `single` has length `1`. -/
private theorem single_edgeLength {e : Sym2 (Fin 2)}
    (he : e ∈ (Graph single : SimpleGraph (Fin 2)).edgeSet) : edgeLength single e = 1 := by
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

/-- `single` is infeasible: a closed walk through `{0, 1}` must come back over it, which costs
`2 > 1`, although a single traversal would fit the bound. -/
private theorem single_infeasible : ¬ RuralPostmanFeasible single := by
  rintro ⟨v, c, hreq, hle⟩
  have hne : c.edges ≠ [] := by
    intro h
    have := hreq (0, 1) (by simp)
    simp [h] at this
  have hconst : c.edges.map (edgeLength single) = c.edges.map fun _ => 1 :=
    List.map_congr_left fun e he => single_edgeLength (c.edges_subset_edgeSet he)
  rw [hconst, List.map_const', List.sum_replicate, SimpleGraph.Walk.length_edges] at hle
  have := closed_walk_two c hne
  simp at hle
  omega

/-- The edge `{0, 1}` of length `2` with bound `4`: a feasible, well-formed RURAL POSTMAN
instance whose length is not `1`. -/
private abbrev long : RuralPostmanInstance := (2, [(0, 1, 2)], [(0, 1)], 4)

private theorem long01 : (Graph long : SimpleGraph (Fin 2)).Adj 0 1 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem long_feasible : RuralPostmanFeasible long :=
  ⟨0, .cons long01 (.cons long01.symm .nil), by decide, by decide⟩

private theorem long_parent_wellFormed : RuralPostman.WellFormed long := by
  unfold RuralPostman.WellFormed; decide

private theorem long_not_wellFormed : ¬ WellFormed long := by
  unfold WellFormed RuralPostman.WellFormed; decide

/-- The decision problem accepts the encoding of the triangle. -/
example : ruralPostmanUnitLengthsDec (bitEncode triangle) = true := by
  simp [ruralPostmanUnitLengthsDec, triangle_wellFormed, triangle_feasible]

/-- It rejects the encoding of the well-formed but infeasible `single`. -/
example : ruralPostmanUnitLengthsDec (bitEncode single) = false := by
  simp [ruralPostmanUnitLengthsDec, single_infeasible]

/-- `single` is well formed, so infeasibility is what rejects it. -/
example : WellFormed single := single_wellFormed

/-- The general problem accepts `long`; the restriction rejects it for its length `2`. -/
example : RuralPostman.ruralPostmanDec (bitEncode long) = true ∧
    ruralPostmanUnitLengthsDec (bitEncode long) = false :=
  ⟨by simp [RuralPostman.ruralPostmanDec, long_parent_wellFormed, long_feasible],
    by simp [ruralPostmanUnitLengthsDec, long_not_wellFormed]⟩

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : ruralPostmanUnitLengthsDec [true] = false := by
  have h : bitDecode (α := RuralPostmanInstance) [true] = none := rfl
  simp [ruralPostmanUnitLengthsDec, h]

end MetaMathlibExt.Complexity.NPComplete.RuralPostmanUnitLengths
