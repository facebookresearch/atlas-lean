/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.LPCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for LP optimality certificates

The LP that maximizes `3 x₀ + x₁ + 2 x₂` subject to `x₀ + x₁ + x₂ = 4`, `x₀ - x₁ + 2 x₂ = 2`
and `x ≥ 0` has the feasible point `x = (3, 1, 0)` with objective `10`. The dual vector
`y = (2, 1)` gives `∑ i, y i * A i j = (3, 1, 4) ≥ c = (3, 1, 2)` with slack `(0, 0, 2)`: the
positive variables `x₀` and `x₁` have zero slack, and the zero variable `x₂` has positive slack
`2`. So every feasible point has objective at most `10`.
-/

@[expose] public section

/-- Every feasible point of the LP above has objective at most `10`, the objective of
`x = (3, 1, 0)`, certified by the dual vector `y = (2, 1)`. -/
example (x' : Fin 3 → ℚ) (hx'0 : ∀ j, 0 ≤ x' j)
    (hx'b : ∀ i : Fin 2, ∑ j, ![![(1 : ℚ), 1, 1], ![1, -1, 2]] i j * x' j = ![4, 2] i) :
    3 * x' 0 + x' 1 + 2 * x' 2 ≤ 10 := by
  have h := lp_optimal_of_certificate ![![(1 : ℚ), 1, 1], ![1, -1, 2]] ![4, 2] ![3, 1, 2]
    ![3, 1, 0] ![2, 1]
    (fun j => by fin_cases j <;> norm_num)
    (fun i => by fin_cases i <;> norm_num [Fin.sum_univ_three])
    (fun j => by fin_cases j <;> norm_num [Fin.sum_univ_two])
    (fun j => by fin_cases j <;> norm_num [Fin.sum_univ_two])
    x' hx'0 hx'b
  norm_num [Fin.sum_univ_three] at h
  exact h

end
