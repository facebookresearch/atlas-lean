/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.SlackForm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the slack form of a system of linear inequalities

* The zero system `0 x ≤ 0`: every nonnegative vector is feasible, and its slack is `0`.
* `x ≤ 1` at `x = 0`: extension gives the nonzero slack `1`, projection recovers the feasible
  point, and `1` is the only slack.
* `x ≤ 1` at `x = 2`: no slack vector exists; the pair `(2, -1)` satisfies the equation but
  fails `s ≥ 0`.
* A two-constraint system `x₀ + x₁ ≤ 4`, `x₀ ≤ 3` at `(1, 2)`: the slack is `(1, 2)`, one entry
  per constraint.
-/

namespace MathlibExtTest.Algorithms.SlackForm

open MathlibExt.Algorithms.SlackForm
open scoped Matrix

/-- For the zero system, every nonnegative vector is feasible and extends with slack `0`. -/
example {m n : ℕ} (x : Fin n → ℚ) (hx : ∀ j, 0 ≤ x j) :
    SlackFeasible (0 : Matrix (Fin m) (Fin n) ℚ) 0 x 0 := by
  have h : Feasible (0 : Matrix (Fin m) (Fin n) ℚ) 0 x := ⟨fun i => by simp, hx⟩
  simpa using slackFeasible_of_feasible h

/-- The constraint matrix of the one-variable system `x ≤ 1`. -/
def A1 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]

/-- `x = 0` is feasible for `x ≤ 1`. -/
theorem feasible_zero : Feasible A1 ![1] ![0] := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [A1, Matrix.mulVec, dotProduct]

/-- Extension: `x ≤ 1` at `x = 0` has the nonzero slack `1`. -/
example : SlackFeasible A1 ![1] ![0] ![1] := by
  have h := slackFeasible_of_feasible feasible_zero
  have hs : (![1] : Fin 1 → ℚ) - A1 *ᵥ ![0] = ![1] := by
    ext i
    fin_cases i
    norm_num [A1, Matrix.mulVec, dotProduct]
  rwa [hs] at h

/-- Projection: the slack-feasible pair `(0, 1)` gives back the feasible point `0`. -/
example (h : SlackFeasible A1 ![1] ![0] ![1]) : Feasible A1 ![1] ![0] :=
  feasible_of_slackFeasible h

/-- The slack is forced: `1` is the only slack of `x = 0` for `x ≤ 1`. -/
example (s : Fin 1 → ℚ) (h : SlackFeasible A1 ![1] ![0] s) : s = ![1] := by
  rw [slack_eq_of_slackFeasible h]
  ext i
  fin_cases i
  norm_num [A1, Matrix.mulVec, dotProduct]

/-- `x = 2` violates `x ≤ 1`, so no slack vector exists. -/
example : ¬ ∃ s, SlackFeasible A1 ![1] ![2] s := by
  rw [← feasible_iff_exists_slackFeasible]
  intro h
  have h0 := h.1 0
  norm_num [A1, Matrix.mulVec, dotProduct] at h0

/-- The pair `(2, -1)` satisfies the equation `x + s = 1` but not `s ≥ 0`, so it is not
slack-feasible: the sign condition on the slack carries the inequality `x ≤ 1`. -/
example : (A1 *ᵥ ![2]) 0 + (![-1] : Fin 1 → ℚ) 0 = 1 ∧
    ¬ SlackFeasible A1 ![1] ![2] ![-1] := by
  refine ⟨by norm_num [A1, Matrix.mulVec, dotProduct], fun h => ?_⟩
  have h0 := h.2.2 0
  norm_num at h0

/-- The constraint matrix of `x₀ + x₁ ≤ 4`, `x₀ ≤ 3`. -/
def A2 : Matrix (Fin 2) (Fin 2) ℚ := ![![1, 1], ![1, 0]]

/-- `(1, 2)` is feasible for `x₀ + x₁ ≤ 4`, `x₀ ≤ 3`, with slack `(1, 2)`. -/
example : SlackFeasible A2 ![4, 3] ![1, 2] ![1, 2] := by
  have h : Feasible A2 ![4, 3] ![1, 2] := by
    constructor <;> intro i <;> fin_cases i <;>
      norm_num [A2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hs : (![4, 3] : Fin 2 → ℚ) - A2 *ᵥ ![1, 2] = ![1, 2] := by
    ext i
    fin_cases i <;> norm_num [A2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h' := slackFeasible_of_feasible h
  rwa [hs] at h'

end MathlibExtTest.Algorithms.SlackForm
