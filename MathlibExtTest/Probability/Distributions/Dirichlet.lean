/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Dirichlet

@[expose] public section

/-!
# Tests for the Dirichlet integral and the Dirichlet distribution
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace MathlibExtTest.Probability.Distributions.Dirichlet

/-- In two categories the multivariate Beta function is Mathlib's Beta function. -/
example (a b : ℝ) : multiBeta ![a, b] = beta a b := by
  simp [multiBeta, beta, Fin.prod_univ_two, Fin.sum_univ_two]

/-- The Dirichlet integral in two categories is the Beta integral. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x, dirichletDensity ![a, b] x = ENNReal.ofReal (beta a b) := by
  rw [lintegral_dirichletDensity (fun i ↦ by fin_cases i <;> simpa)]
  simp [multiBeta, beta, Fin.prod_univ_two, Fin.sum_univ_two]

/-- The uniform distribution on the triangle: `B(1, 1, 1) = 1/2`, the area of the triangle. -/
example : ∫⁻ x, dirichletDensity ![1, 1, 1] x = ENNReal.ofReal (1 / 2) := by
  rw [lintegral_dirichletDensity (fun i ↦ by fin_cases i <;> simp)]
  congr 1
  have h3 : Gamma 3 = 2 := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Gamma_add_one two_ne_zero, Gamma_two, mul_one]
  simp [multiBeta, Fin.prod_univ_succ, Fin.sum_univ_succ]
  norm_num [h3]

/-- Under the uniform distribution on the triangle each coordinate has mean `1/3`. -/
example (i : Fin 3) :
    ∫⁻ θ, ENNReal.ofReal (θ i) ∂dirichletMeasure ![1, 1, 1] = ENNReal.ofReal (1 / 3) := by
  rw [lintegral_dirichletMeasure_apply (fun j ↦ by fin_cases j <;> simp)]
  congr 1
  fin_cases i <;> simp [Fin.sum_univ_three] <;> norm_num

/-- `Dir(α)` is a probability measure on probability vectors. -/
example : IsProbabilityMeasure (dirichletMeasure ![2, 3]) :=
  isProbabilityMeasure_dirichletMeasure fun i ↦ by fin_cases i <;> norm_num

/-- Conjugacy: two observations of category `0` turn the uniform prior `Dir(1, 1)` into
`Dir(3, 1)`, with total weight `B(3, 1) / B(1, 1) = 1/3`. -/
example : (dirichletMeasure ![1, 1]).withDensity
      (fun θ ↦ ∏ i, ENNReal.ofReal (θ i) ^ (![2, 0] : Fin 2 → ℕ) i) =
    ENNReal.ofReal (multiBeta (fun i ↦ (![1, 1] : Fin 2 → ℝ) i + (![2, 0] : Fin 2 → ℕ) i) /
      multiBeta ![1, 1]) • dirichletMeasure (fun i ↦ (![1, 1] : Fin 2 → ℝ) i +
        (![2, 0] : Fin 2 → ℕ) i) :=
  withDensity_prod_pow_dirichletMeasure (fun i ↦ by fin_cases i <;> simp) _

end MathlibExtTest.Probability.Distributions.Dirichlet
