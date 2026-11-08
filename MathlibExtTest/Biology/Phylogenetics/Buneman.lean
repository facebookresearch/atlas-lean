/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.Buneman
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Tests for tree metrics and the four-point condition

Non-vacuity of `IsTreeMetric` (the zero dissimilarity, realized on a one-vertex tree), the
four-point condition for it, the converse on a concrete metric (the discrete metric on three
points, realized by a star), the empty set of taxa, and a non-example: the path metric of the
4-cycle violates the four-point condition, so by `IsTreeMetric.fourPointCondition` it is not a
tree metric.
-/

@[expose] public section

namespace MathlibExtTest.Biology.Phylogenetics.Buneman

open MathlibExt.Biology.Phylogenetics.Buneman

-- Non-vacuity: the zero dissimilarity is a tree metric (all taxa on one vertex).
theorem isTreeMetric_zero (X : Type*) : IsTreeMetric (fun _ _ : X => (0 : ℝ)) := by
  refine ⟨Unit, inferInstance, ⊥, .of_subsingleton, fun _ => 0, fun _ => (), ?_, ?_⟩
  · simp
  · intro x y p _
    cases p with
    | nil => simp
    | cons h _ => exact absurd h (by simp)

example (X : Type*) : FourPointCondition (fun _ _ : X => (0 : ℝ)) :=
  (isTreeMetric_zero X).fourPointCondition

/-- The path metric of the 4-cycle `0 - 1 - 2 - 3 - 0`. -/
def cycleMetric (i j : Fin 4) : ℝ :=
  if i = j then 0 else if (i : ℕ) % 2 = (j : ℕ) % 2 then 2 else 1

-- It violates the four-point condition at `(0, 2, 1, 3)`: `4 > max 2 2`.
theorem not_fourPointCondition_cycleMetric : ¬ FourPointCondition cycleMetric := by
  intro h
  have := h 0 2 1 3
  norm_num [cycleMetric] at this

-- Hence the 4-cycle metric is not a tree metric.
example : ¬ IsTreeMetric cycleMetric := fun h =>
  not_fourPointCondition_cycleMetric h.fourPointCondition

/-- The discrete metric on three points. -/
def discreteMetric (i j : Fin 3) : ℝ := if i = j then 0 else 1

theorem fourPointCondition_discreteMetric : FourPointCondition discreteMetric := by
  intro x y z t
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases t <;> norm_num [discreteMetric]

-- The converse: the discrete metric on three points is a tree metric.
example : IsTreeMetric discreteMetric :=
  isTreeMetric_of_fourPointCondition _ (fun _ => by simp [discreteMetric])
    (fun _ _ => by simp [discreteMetric, eq_comm]) fourPointCondition_discreteMetric

-- Buneman's theorem as an equivalence, on the 4-cycle metric.
example : ¬ IsTreeMetric cycleMetric := by
  rw [isTreeMetric_iff_fourPointCondition _ (fun _ => by simp [cycleMetric])
    (fun i j => by unfold cycleMetric; split_ifs <;> simp_all [eq_comm])]
  exact not_fourPointCondition_cycleMetric

-- No taxa: every dissimilarity is a tree metric.
example (d : Empty → Empty → ℝ) : IsTreeMetric d :=
  isTreeMetric_of_fourPointCondition d (fun x => x.elim) (fun x => x.elim) (fun x => x.elim)

end MathlibExtTest.Biology.Phylogenetics.Buneman
