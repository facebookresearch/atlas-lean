/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.MaxCut
import Mathlib.Data.Fin.VecNotation

/-!
# MAX-CUT tests

`cutCount` is computable, so the fixtures are checked by `decide`. The constant assignment cuts
nothing. On `⊤ : SimpleGraph (Fin 2)`, a single edge, the assignment `(true, false)` cuts it, the
cut summed over the four assignments is `2 = 2 ^ (2 - 1) * 1`, and the assignment is locally
optimal, so the local-search bound reads `1 ≤ 2 * 1`.
-/

namespace Cslib.Algorithms.Lean.MaxCut

/-- Boundary check: the cut of the constant assignment is zero. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    cutCount G (fun _ => true) = 0 := by
  rw [cutCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e _
  induction e using Sym2.ind with
  | _ a b => simp

/-- The complete graph on two vertices has a single edge. -/
example : (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1 := by decide

/-- The assignment `(true, false)` cuts that edge. -/
example : cutCount (⊤ : SimpleGraph (Fin 2)) ![true, false] = 1 := by decide

/-- Direct count: the edge is cut by two of the four assignments. -/
example : ∑ x : Fin 2 → Bool, cutCount (⊤ : SimpleGraph (Fin 2)) x = 2 := by decide

/-- The identity `sum_cutCount` on the same graph: `2 ^ (2 - 1) * 1 = 2`. -/
example : ∑ x : Fin 2 → Bool, cutCount (⊤ : SimpleGraph (Fin 2)) x = 2 := by
  rw [sum_cutCount]
  decide

/-- `(true, false)` is locally optimal, so the local-search bound gives `1 ≤ 2 * 1`. -/
example : (⊤ : SimpleGraph (Fin 2)).edgeFinset.card ≤ 2 * cutCount ⊤ ![true, false] :=
  locally_optimal_cut_ge ⊤ ![true, false] (by decide)

end Cslib.Algorithms.Lean.MaxCut
