/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.MaxCut
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# MAX-CUT tests

The constant assignment cuts nothing. On the single edge `(0, 1)` of `Fin 2`, the assignment
`(true, false)` cuts it, the cut summed over the four assignments is `2 = 2 ^ (2 - 1) * 1`, and the
assignment is locally optimal, so the local-search bound reads `1 ≤ 2 * 1`.
-/

namespace Cslib.Algorithms.Lean.MaxCut

/-- Boundary check: the cut of the constant assignment is zero. -/
example (E : EdgeSet 2) : cutCount E (fun _ => true) = 0 := by
  simp [cutCount]

/-- The single edge `(0, 1)` on two vertices. -/
private def singleEdge : EdgeSet 2 where
  edges := {(0, 1)}
  lt_of_mem := by decide

private lemma cutCount_singleEdge (x : Fin 2 → Bool) :
    cutCount singleEdge x = if x 0 ≠ x 1 then 1 else 0 := by
  simp only [cutCount, singleEdge, Finset.filter_singleton]
  split_ifs <;> simp

/-- The assignment `(true, false)` cuts the edge. -/
example : cutCount singleEdge ![true, false] = 1 := by
  simp [cutCount_singleEdge]

/-- Direct count: the single edge is cut by two of the four assignments. -/
example : (∑ x : Fin 2 → Bool, cutCount singleEdge x) = 2 := by
  simp only [cutCount_singleEdge]
  rw [Fintype.sum_equiv (finTwoArrowEquiv Bool)
    (fun x : Fin 2 → Bool => if x 0 ≠ x 1 then (1 : ℝ) else 0)
    (fun p : Bool × Bool => if p.1 ≠ p.2 then (1 : ℝ) else 0) (fun _ => rfl)]
  simp [Fintype.sum_prod_type]
  norm_num

/-- The identity `sum_cutCount` at `n = 2` with one edge: `2 ^ (2 - 1) * 1 = 2`. -/
example : (∑ x : Fin 2 → Bool, cutCount singleEdge x) = 2 := by
  rw [sum_cutCount (by norm_num) singleEdge]
  norm_num [singleEdge]

/-- `(true, false)` is locally optimal: flipping either vertex leaves the edge uncut. -/
private lemma singleEdge_locallyOptimal (v : Fin 2) :
    cutCount singleEdge ![true, false] ≥
      cutCount singleEdge
        (Function.update ![true, false] v (!(![true, false] : Fin 2 → Bool) v)) := by
  rw [cutCount_singleEdge, cutCount_singleEdge]
  fin_cases v <;> simp

/-- The local-search bound on the fixture: `|E| = 1 ≤ 2 * 1`. -/
example : (singleEdge.edges.card : ℝ) ≤ 2 * cutCount singleEdge ![true, false] :=
  locally_optimal_cut_ge singleEdge ![true, false] singleEdge_locallyOptimal

end Cslib.Algorithms.Lean.MaxCut
