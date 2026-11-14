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
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Tests for uncertainty propagation

Exact numeric checks: affine mean/covariance entries on two-point data, the
correlated two-input variance with its cross term, the nonzero `x ^ 2` Taylor
remainder with its bound, the nonzero Jacobian remainder of the square map with all three
componentwise bounds, a nonzero Lipschitz budget with the zero-error case, and
rank-deficient vs identifiable calibration designs.

## i. Overview

Section A evaluates `meanVec`/`covMatrix` entries on `p = ![1/2, 1/2]`,
`X = ![![1, 2], ![3, 4]]` and checks the two-input variance is `4`, not the
quadrature value `2`. Section B shows the `x ^ 2` remainder at `δ = 1` equals `1`
(nonzero) and satisfies the `H = 2` bound. For the square map `y ↦ (y 0) ^ 2` on
`Fin 1 → ℝ` at `x = 0` and the small step `δ = 1 / 2`, the Jacobian remainder is `1 / 4`;
the unit-step, scaled and Hessian bounds all equal `1 / 4`, while the unscaled hypothesis
with the `‖δ‖ ^ 2` conclusion would give `1 / 16`, which fails. Section C checks a Lipschitz
budget of
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

open Statistics.UncertaintyPropagation Matrix MathlibExt.Probability.FiniteProbability

namespace PhyslibExtTest.Statistics.UncertaintyPropagation

/-! ## A. Finite affine propagation on two-point data -/

example : meanVec ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 = 2 := by
  simp only [meanVec_apply, expectation, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

example : meanVec ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 1 = 3 := by
  simp only [meanVec_apply, expectation, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

example : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 0 = 1 := by
  simp only [covMatrix_apply, covariance, expectation, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

example : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 1 1 = 1 := by
  simp only [covMatrix_apply, covariance, expectation, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The cross-covariance is nonzero: the two inputs are correlated. -/
example : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 1 = 1 := by
  simp only [covMatrix_apply, covariance, expectation, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The variance of `X₁ + X₂` is `1 + 1 + 2 = 4`: the cross term counts. Quadrature
would give `2`. -/
example : covMatrix ![1 / 2, 1 / 2]
    (fun ω => Matrix.of ![![1, 1]] *ᵥ ![![1, 2], ![3, 4]] ω) 0 0 = 4 := by
  have hC00 : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 0 = 1 := by
    simp only [covMatrix_apply, covariance, expectation, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hC11 : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 1 1 = 1 := by
    simp only [covMatrix_apply, covariance, expectation, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hC01 : covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![3, 4]] 0 1 = 1 := by
    simp only [covMatrix_apply, covariance, expectation, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [covMatrix_two_linear _ _ 1 1, hC00, hC11, hC01]
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

/-- The square map on `Fin 1 → ℝ`: its single component is `y ↦ (y 0) ^ 2`. -/
noncomputable def sqMap : (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun y _ => y 0 ^ 2

/-- The small step `δ = 1 / 2` in `Fin 1 → ℝ`. -/
noncomputable def halfStep : Fin 1 → ℝ := fun _ => 1 / 2

/-- The coordinate functional `y ↦ y 0` on `Fin 1 → ℝ`. -/
noncomputable def coord0 : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0

/-- The derivative map `y ↦ (2 * y 0) • coord0` of the component `y ↦ (y 0) ^ 2`. It is
linear in `y`, so it is also its own derivative: the constant Hessian of the component. -/
noncomputable def sqDeriv : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) →L[ℝ] ℝ :=
  ((2 : ℝ) • coord0).smulRight coord0

lemma norm_halfStep : ‖halfStep‖ = 1 / 2 := by
  change ‖(fun _ : Fin 1 => (1 / 2 : ℝ))‖ = 1 / 2
  rw [pi_norm_const]
  norm_num

lemma hasFDerivAt_sqMap_component (y : Fin 1 → ℝ) :
    HasFDerivAt (fun z : Fin 1 → ℝ => sqMap z 0) (sqDeriv y) y := by
  have h := coord0.hasFDerivAt.mul (coord0.hasFDerivAt (x := y))
  convert h using 1
  · funext z
    simp [sqMap, coord0, sq]
  · ext v
    simp [sqDeriv, coord0]
    ring

lemma fderiv_sqMap_component :
    fderiv ℝ (fun z : Fin 1 → ℝ => sqMap z 0) = sqDeriv :=
  funext fun y => (hasFDerivAt_sqMap_component y).fderiv

/-- The Hessian of the component `y ↦ (y 0) ^ 2` has operator norm at most `2`. -/
lemma norm_fderiv_fderiv_sqMap_le (y : Fin 1 → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (fun z : Fin 1 → ℝ => sqMap z 0)) y‖ ≤ 2 := by
  have hc : ‖coord0‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa [coord0] using norm_le_pi_norm v 0
  rw [fderiv_sqMap_component, ContinuousLinearMap.fderiv, sqDeriv,
    ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_two]
  have h0 : 0 ≤ ‖coord0‖ := norm_nonneg _
  nlinarith

lemma hasFDerivAt_sqMap_zero : HasFDerivAt sqMap (0 : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ)) 0 := by
  rw [hasFDerivAt_pi']
  intro i
  have h := hasFDerivAt_sqMap_component 0
  simpa [sqMap, sqDeriv] using h

lemma contDiff_sqMap : ContDiff ℝ 2 sqMap :=
  contDiff_pi.2 fun _ => by
    change ContDiff ℝ 2 fun y : Fin 1 → ℝ => y 0 ^ 2
    fun_prop

/-- Along the segment from `0` in direction `halfStep`, the component is `t ^ 2 / 4`. -/
lemma sqMap_segment (i : Fin 1) :
    (fun t : ℝ => sqMap (0 + t • halfStep) i) = fun t => t ^ 2 / 4 := by
  funext t
  simp only [sqMap, halfStep, zero_add, Pi.smul_apply, smul_eq_mul]
  ring

lemma deriv_deriv_sqMap_segment (i : Fin 1) (t : ℝ) :
    deriv (deriv (fun t : ℝ => sqMap (0 + t • halfStep) i)) t = 1 / 2 := by
  have h1 : deriv (fun t : ℝ => t ^ 2 / 4) = fun t => t / 2 := by
    funext t
    rw [((hasDerivAt_pow 2 t).div_const 4).deriv]
    push_cast
    ring
  rw [sqMap_segment, h1]
  exact ((hasDerivAt_id t).div_const 2).deriv

/-- The square map at `x = 0` with the small step `δ = 1 / 2` has the NONZERO Jacobian
remainder `1 / 4`. -/
lemma jacobianRemainder_sqMap : jacobianRemainder sqMap 0 halfStep 0 = 1 / 4 := by
  rw [jacobianRemainder, hasFDerivAt_sqMap_zero.fderiv]
  norm_num [sqMap, halfStep]

/-- Unit-step bound: the segment second derivative is `1 / 2`, so the bound is
`(1 / 2) / 2 = 1 / 4`, attained by the remainder. -/
example : |jacobianRemainder sqMap 0 halfStep 0| ≤ (1 / 2) / 2 :=
  jacobianRemainder_component_le sqMap 0 halfStep 0 (fun _ => 1 / 2)
    hasFDerivAt_sqMap_zero.differentiableAt
    (fun i => by rw [sqMap_segment]; fun_prop)
    (fun i t _ => by rw [deriv_deriv_sqMap_segment]; norm_num)

/-- `‖δ‖ ^ 2`-scaled bound: `1 / 2 ≤ 2 * ‖δ‖ ^ 2`, so the bound is
`2 / 2 * ‖δ‖ ^ 2 = 1 / 4`. -/
example : |jacobianRemainder sqMap 0 halfStep 0| ≤ 2 / 2 * ‖halfStep‖ ^ 2 :=
  jacobianRemainder_component_le_of_scaled sqMap 0 halfStep 0 (fun _ => 2)
    hasFDerivAt_sqMap_zero.differentiableAt
    (fun i => by rw [sqMap_segment]; fun_prop)
    (fun i t _ => by rw [deriv_deriv_sqMap_segment, norm_halfStep]; norm_num)

/-- Hessian bound: the component `y ↦ (y 0) ^ 2` has Hessian norm at most `2`, so the
bound is `2 / 2 * ‖δ‖ ^ 2 = 1 / 4`. -/
example : |jacobianRemainder sqMap 0 halfStep 0| ≤ 2 / 2 * ‖halfStep‖ ^ 2 :=
  jacobianRemainder_component_le_of_hessian sqMap 0 halfStep 0 (fun _ => 2)
    (lo := 0) (hi := halfStep) isOpen_univ (Set.subset_univ _) contDiff_sqMap.contDiffOn
    (fun y _ => norm_fderiv_fderiv_sqMap_le y)
    ⟨le_rfl, fun _ => by norm_num [halfStep]⟩ ⟨fun _ => by norm_num [halfStep], by simp⟩

/-- Each of the three bounds above equals the remainder `1 / 4`. -/
example : 2 / 2 * ‖halfStep‖ ^ 2 = 1 / 4 ∧ (1 / 2 : ℝ) / 2 = 1 / 4 := by
  rw [norm_halfStep]
  norm_num

/-- The unscaled hypothesis does not give the `‖δ‖ ^ 2` conclusion: the segment second
derivative is bounded by `1 / 2`, but the remainder `1 / 4` exceeds
`(1 / 2) / 2 * ‖δ‖ ^ 2 = 1 / 16`. -/
example : ¬ |jacobianRemainder sqMap 0 halfStep 0| ≤ (1 / 2) / 2 * ‖halfStep‖ ^ 2 := by
  rw [jacobianRemainder_sqMap, norm_halfStep]
  norm_num

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
