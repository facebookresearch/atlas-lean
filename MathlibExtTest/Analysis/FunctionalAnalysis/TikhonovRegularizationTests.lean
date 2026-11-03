/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.TikhonovRegularization

/-!
# Tests for Tikhonov regularization in Hilbert spaces
-/

open Filter Metric Set Topology
open scoped InnerProduct

namespace TikhonovRegularizationTests

open MathlibExt.Analysis.FunctionalAnalysis.TikhonovRegularization

/-- The normal operator for the identity: `x + Λ • x`. -/
example : tikhonovOperator (1 : ℂ →L[ℂ] ℂ) 3 (1 / 2 : ℂ) = 2 := by
  norm_num [tikhonovOperator_apply]

/-- The zero operator: `0` solves the normal equations, so it minimizes `J`. -/
example : IsMinOn (tikhonovFunctional (0 : ℂ →L[ℂ] ℂ) 1 2) univ 0 := by
  apply isMinOn_tikhonovFunctional_of_normal_equations _ _ _ (by norm_num) _
  simp [tikhonovOperator_apply]

/-- The value of the Tikhonov functional at the zero minimizer, for `A = 0`. -/
example : tikhonovFunctional (0 : ℂ →L[ℂ] ℂ) 1 2 (0 : ℂ) = 1 := by
  simp [tikhonovFunctional]

/-- The identity operator on `ℂ`, `b = 2`, `Λ = 3`: the minimizer is `1 / 2`. -/
example : ∃! x : ℂ, ∀ y : ℂ,
    tikhonovFunctional (1 : ℂ →L[ℂ] ℂ) 2 3 x ≤ tikhonovFunctional (1 : ℂ →L[ℂ] ℂ) 2 3 y :=
  existsUnique_tikhonov_minimizer _ _ _ (by norm_num)

/-- The identity operator on `ℂ`, `b = 2`, `Λ = 3`: `1 / 2` solves the normal
equations, hence it is the minimizer. -/
example : tikhonovOperator (1 : ℂ →L[ℂ] ℂ) 3 (1 / 2 : ℂ)
    = ((1 : ℂ →L[ℂ] ℂ)†) 2 := by
  norm_num [tikhonovOperator_apply]

/-- The stability bound at the `ℂ` identity example: `‖1 / 2‖ ≤ 1 * 2 / 3`. -/
example : ‖(1 / 2 : ℂ)‖ ≤ ‖(1 : ℂ →L[ℂ] ℂ)‖ * ‖(2 : ℂ)‖ / 3 :=
  norm_le_of_tikhonov_normal_equations _ _ _ (by norm_num)
    (by norm_num [tikhonovOperator_apply])

/-- Solutions for the identity operator tend to `0` as `Λ → ∞`: here
`Λ n = n + 1` and the solutions are `x n = 2 / (n + 2)`. -/
example : Tendsto (fun n : ℕ => (2 : ℂ) / (n + 2 : ℂ)) atTop (𝓝 0) := by
  have hΛ : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
  have hΛtop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hx : ∀ n : ℕ, tikhonovOperator (1 : ℂ →L[ℂ] ℂ) ((n : ℝ) + 1)
      ((2 : ℂ) / (n + 2 : ℂ)) = ((1 : ℂ →L[ℂ] ℂ)†) 2 := by
    intro n
    have hne : ((n : ℂ) + 2) ≠ 0 := by
      rw [show ((n : ℂ) + 2) = (((n : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < (n : ℝ) + 2)
    simp only [tikhonovOperator_apply, ContinuousLinearMap.adjoint_one,
      one_apply_eq_self]
    push_cast
    rw [smul_eq_mul]
    field_simp [hne]
    ring
  exact tendsto_tikhonov_solution_zero (A := (1 : ℂ →L[ℂ] ℂ)) (b := 2)
    (Λ := fun n : ℕ => (n : ℝ) + 1) hΛ hΛtop _ hx

end TikhonovRegularizationTests
