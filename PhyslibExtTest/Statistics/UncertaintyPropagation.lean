/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Statistics.UncertaintyPropagation
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Tests for uncertainty propagation

Exact numeric checks: affine mean/covariance entries on two-point data, the
correlated two-input variance with its cross term, the nonzero `x ^ 2` Jacobian
remainder with its bound, a nonzero Lipschitz budget with the zero-error case, and
rank-deficient vs identifiable calibration designs.

## i. Overview

Section A evaluates `meanVec`/`covMatrix` entries on `p = ![1/2, 1/2]`,
`X = ![![1, 2], ![3, 4]]` and checks the two-input variance is `4`, not the
quadrature value `2`. Section B shows the `x ^ 2` remainder at `δ = 1` equals `1`
(nonzero) and satisfies the `H = 2` bound. Section C checks a Lipschitz budget of
`6` and the zero-error case. Section D exhibits a `2 × 3` design with an explicit
nonzero kernel vector and non-unique estimates, plus an identifiable `3 × 2` design.

## ii. Key results

These are computational checks of the production API, not new results.

## iii. Table of contents

- A. Finite affine propagation on two-point data
- B. The nonlinear Jacobian remainder is nonzero and bounded
- C. Lipschitz budgets, nonzero and zero-error
- D. Rank-deficient and identifiable calibration designs

## iv. References

- `PhyslibExt.Statistics.UncertaintyPropagation`
-/

@[expose] public section

open Statistics.UncertaintyPropagation Matrix

namespace PhyslibExtTest.Statistics.UncertaintyPropagation

/-! ## A. Finite affine propagation on two-point data -/

example : meanVec ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 = 2 := by
  simp only [meanVec_apply, mean, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

example : meanVec ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 1 = 3 := by
  simp only [meanVec_apply, mean, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

example : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 0 = 1 := by
  simp only [covMatrix_apply, meanVec_apply, mean, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

example : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 1 1 = 1 := by
  simp only [covMatrix_apply, meanVec_apply, mean, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The cross-covariance is nonzero: the two inputs are correlated. -/
example : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 1 = 1 := by
  simp only [covMatrix_apply, meanVec_apply, mean, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The variance of `X₁ + X₂` is `1 + 1 + 2 = 4`: the cross term counts. Quadrature
would give `2`. -/
example : covMatrix ![1 / 2, 1 / 2]
    (fun ω => Matrix.of ![![1, 1]] *ᵥ ![![1, 2], ![3, 4]] ω) 0 0 = 4 := by
  have hp1 : ∑ ω, (![1 / 2, 1 / 2] : Fin 2 → ℝ) ω = 1 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hC00 : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 0 = 1 := by
    simp only [covMatrix_apply, meanVec_apply, mean, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hC11 : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 1 1 = 1 := by
    simp only [covMatrix_apply, meanVec_apply, mean, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hC01 : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 1 = 1 := by
    simp only [covMatrix_apply, meanVec_apply, mean, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [covMatrix_two_linear _ _ 1 1 hp1, hC00, hC11, hC01]
  norm_num

/-! ## B. The nonlinear Jacobian remainder is nonzero and bounded -/

/-- For `f x = x ^ 2` at `x = 0`, `δ = 1`, the first-order remainder is `1`. -/
example : |(0 + 1 : ℝ) ^ 2 - (0 : ℝ) ^ 2 - deriv (fun x : ℝ => x ^ 2) 0 * 1| = 1 := by
  have hd : deriv (fun x : ℝ => x ^ 2) 0 = 0 := by
    rw [deriv_pow_field]
    norm_num
  rw [hd]
  norm_num

/-- Hence the remainder is NONZERO: Jacobian propagation is not exact. -/
example : |(0 + 1 : ℝ) ^ 2 - (0 : ℝ) ^ 2 - deriv (fun x : ℝ => x ^ 2) 0 * 1| ≠ 0 := by
  have hd : deriv (fun x : ℝ => x ^ 2) 0 = 0 := by
    rw [deriv_pow_field]
    norm_num
  rw [hd]
  norm_num

/-- ... while satisfying the `H = 2` bound `1 ≤ 2 / 2 * 1 ^ 2`. -/
example : |(0 + 1 : ℝ) ^ 2 - (0 : ℝ) ^ 2 - deriv (fun x : ℝ => x ^ 2) 0 * 1|
    ≤ 2 / 2 * (1 : ℝ) ^ 2 := by
  have hcont : ContDiff ℝ 2 (fun x : ℝ => x ^ 2) := by fun_prop
  have h1 : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
    funext x
    simp
  have h2 : ∀ y : ℝ, deriv (deriv (fun x : ℝ => x ^ 2)) y = 2 := by
    intro y
    rw [h1]
    simp
  have hH : ∀ y ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (fun x : ℝ => x ^ 2)) y| ≤ 2 := by
    intro y _
    rw [h2 y]
    norm_num
  have hbound := taylor_first_order_bound (a := 0) (b := 1) (H := 2)
    (f := fun x : ℝ => x ^ 2) hcont hH (x := 0) (δ := 1)
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) + 1 ∈ Set.Icc 0 1)
  exact hbound

/-- A constant map has zero Jacobian remainder: the linearization is exact. -/
example (c : Fin 1 → ℝ) (x δ : Fin 1 → ℝ) : jacobianRemainder (fun _ => c) x δ = 0 := by
  simp [jacobianRemainder]

/-! ## C. Lipschitz budgets, nonzero and zero-error -/

/-- Doubling is `2`-Lipschitz on `ℝ`. -/
lemma lipschitz_two_mul : LipschitzWith 2 (fun x : ℝ => 2 * x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (2 * x) (2 * y) ≤ ↑(2 : NNReal) * dist x y
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul,
    show ((2 : NNReal) : ℝ) = 2 from rfl, show ‖(2 : ℝ)‖ = 2 by norm_num [Real.norm_eq_abs]]

/-- A nonzero budget: input error `3` gives output error at most `2 * 3 = 6`. -/
example : ‖(fun x : ℝ => 2 * x) (0 + 3) - (fun x : ℝ => 2 * x) 0‖ ≤ (2 : ℝ) * 3 :=
  lipschitz_error_budget lipschitz_two_mul (by norm_num [Real.norm_eq_abs])

/-- The budget `2 * 3` is nonzero: the bound is not vacuous. -/
example : (2 : ℝ) * 3 ≠ 0 := by norm_num

/-- Zero input error gives zero output error. -/
example : ‖(fun x : ℝ => 2 * x) (5 + 0) - (fun x : ℝ => 2 * x) 5‖ ≤ (2 : ℝ) * 0 :=
  lipschitz_error_budget lipschitz_two_mul (by norm_num [Real.norm_eq_abs])

/-! ## D. Rank-deficient and identifiable calibration designs -/

/-- The `2 × 3` design with a repeated column has a nontrivial kernel, so estimates
are not unique: `0` and `![1, 0, -1]` give the same observation `0`. -/
example : ∃ θ' : Fin 3 → ℝ, θ' ≠ 0 ∧ Matrix.of ![![1, 0, 1], ![0, 1, 0]] *ᵥ θ' = 0 := by
  have hker : Matrix.of ![![1, 0, 1], ![0, 1, 0]] *ᵥ ![1, 0, -1] = (0 : Fin 2 → ℝ) := by
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
  have hne : ![1, 0, -1] ≠ (0 : Fin 3 → ℝ) := by
    intro h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
    exact one_ne_zero h0
  exact exists_distinct_of_nontrivial_ker _ ⟨_, hne, hker⟩ 0 0 (Matrix.mulVec_zero _)

/-- The `3 × 2` example calibration design. -/
noncomputable def exampleDesign : Matrix (Fin 3) (Fin 2) ℝ :=
  Matrix.of ![![1, 0], ![0, 1], ![1, 1]]

/-- The `3 × 2` example design is identifiable. -/
lemma identifiable_example : Identifiable exampleDesign := by
  intro θ₁ θ₂ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [exampleDesign, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  norm_num at h0 h1
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- ... so its normal equations have at most one solution. -/
example (y : Fin 3 → ℝ) (θ₁ θ₂ : Fin 2 → ℝ)
    (h₁ : (exampleDesignᵀ * exampleDesign) *ᵥ θ₁ = exampleDesignᵀ *ᵥ y)
    (h₂ : (exampleDesignᵀ * exampleDesign) *ᵥ θ₂ = exampleDesignᵀ *ᵥ y) :
    θ₁ = θ₂ :=
  normalEquations_unique exampleDesign identifiable_example y θ₁ θ₂ h₁ h₂

end PhyslibExtTest.Statistics.UncertaintyPropagation
