/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public import MathlibExt.Probability.Finance.PortfolioVariance

open ProbabilityTheory

/-!
# Spatial covariance and unbiased linear prediction

## i. Overview

Square-integrable observations at supplied locations have a
covariance matrix (positive semidefinite, hence a valid
covariance) and a target covariance vector; a common-mean linear
predictor with weights summing to one is unbiased, with error
variance `Var X - 2 (w . c) + w . (K w)`.

## ii. Key results

- `SpatialPredictor.covMatrix_posSemidef`: valid covariance.
- `SpatialPredictor.predictor_unbiased_and_error_variance`:
  unbiasedness and error variance.

## iii. Table of contents

- A. Covariance bridge

## iv. References

- Standard ordinary-kriging / best linear unbiased prediction
  covariance algebra.

## A. Covariance bridge
-/

@[expose] public section

namespace SpatialPredictor

/-- Covariance matrix of the observations, reusing the existing
covariance-matrix API (`K i j = Cov(Y i, Y j)`). -/
noncomputable abbrev covMatrix {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  MathlibExt.Probability.Finance.PortfolioVariance.covMatrix μ Y

/-- Covariance vector between target and observations:
`c i = Cov(X, Y i)`. -/
noncomputable def covVector {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (X : Ω → ℝ)
    (Y : Fin n → Ω → ℝ) : Fin n → ℝ :=
  fun i => ProbabilityTheory.covariance X (Y i) μ

/-- The covariance matrix of square-integrable observations is
positive semidefinite (it is a valid covariance), and the target
covariance vector is as named. -/
theorem covMatrix_posSemidef {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {n : ℕ} (Y : Fin n → Ω → ℝ) (hY : ∀ i, MeasureTheory.MemLp (Y i) 2 μ) :
    (covMatrix μ Y).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.isHermitian_iff_isSymm]
    apply Matrix.IsSymm.ext
    intro i j
    simp only [covMatrix, MathlibExt.Probability.Finance.PortfolioVariance.covMatrix, Matrix.of_apply]
    exact ProbabilityTheory.covariance_comm _ _
  · intro x
    have hstar : star x = x := by simp
    rw [hstar]
    have hmem : ∀ i, MeasureTheory.MemLp (fun ω => x i * Y i ω) 2 μ :=
      fun i => (hY i).const_mul (x i)
    have hvar : ProbabilityTheory.variance (fun ω => ∑ i, x i * Y i ω) μ
        = dotProduct x (Matrix.mulVec (covMatrix μ Y) x) := by
      have h1 : ProbabilityTheory.variance (fun ω => ∑ i, x i * Y i ω) μ
          = ∑ i, ∑ j, ProbabilityTheory.covariance (fun ω => x i * Y i ω)
            (fun ω => x j * Y j ω) μ :=
        ProbabilityTheory.variance_fun_sum hmem
      rw [h1]
      simp only [ProbabilityTheory.covariance_const_mul_left,
        ProbabilityTheory.covariance_const_mul_right, dotProduct,
        Matrix.mulVec_apply_eq_sum, covMatrix, MathlibExt.Probability.Finance.PortfolioVariance.covMatrix, Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [← hvar]
    exact ProbabilityTheory.variance_nonneg _ _

/-- Common-mean unbiased linear predictor: observations `Y i` and
target `X` are square-integrable with a common mean, and weights
`w` sum to `1`. Then the predictor `∑ i, w i * Y i` is unbiased for
`X`, and the prediction-error variance is
`Var X - 2 * (w ⬝ᵥ c) + w ⬝ᵥ (K *ᵥ w)` in terms of the covariance
matrix `K` and vector `c`. -/
theorem predictor_unbiased_and_error_variance {Ω : Type*}
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (X : Ω → ℝ) (Y : Fin n → Ω → ℝ) (w : Fin n → ℝ)
    (hX : MeasureTheory.MemLp X 2 μ)
    (hY : ∀ i, MeasureTheory.MemLp (Y i) 2 μ)
    (hm : ∀ i, μ[Y i] = μ[X]) (hw : ∑ i, w i = 1) :
    μ[fun ω => ∑ i, w i * Y i ω] = μ[X]
      ∧ ProbabilityTheory.variance (fun ω => X ω - ∑ i, w i * Y i ω) μ
        = ProbabilityTheory.variance X μ
          - 2 * dotProduct w (covVector μ X Y)
          + dotProduct w (Matrix.mulVec (covMatrix μ Y) w) := by
  have hmem : ∀ i, MeasureTheory.MemLp (fun ω => w i * Y i ω) 2 μ :=
    fun i => (hY i).const_mul (w i)
  have hS : MeasureTheory.MemLp (fun ω => ∑ i, w i * Y i ω) 2 μ :=
    MeasureTheory.memLp_finsetSum Finset.univ (fun i _ => hmem i)
  constructor
  · have hint : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        MeasureTheory.Integrable (fun ω => w i * Y i ω) μ :=
      fun i _ => (hmem i).integrable one_le_two
    have h1 : μ[fun ω => ∑ i, w i * Y i ω]
        = ∑ i, w i * μ[Y i] := by
      have e := MeasureTheory.integral_finsetSum (μ := μ)
        (Finset.univ : Finset (Fin n))
        (f := fun i ω => w i * Y i ω) hint
      simp only [MeasureTheory.integral_const_mul] at e ⊢
      exact e
    rw [h1]
    simp only [hm]
    rw [← Finset.sum_mul, hw, one_mul]
  · have hvar : ProbabilityTheory.variance (fun ω => X ω - ∑ i, w i * Y i ω) μ
        = ProbabilityTheory.variance X μ
          - 2 * ProbabilityTheory.covariance X (fun ω => ∑ i, w i * Y i ω) μ
          + ProbabilityTheory.variance (fun ω => ∑ i, w i * Y i ω) μ :=
        ProbabilityTheory.variance_fun_sub hX hS
    have hcov : ProbabilityTheory.covariance X (fun ω => ∑ i, w i * Y i ω) μ
        = dotProduct w (covVector μ X Y) := by
      have e : ProbabilityTheory.covariance X (fun ω => ∑ i, w i * Y i ω) μ
          = ∑ i, ProbabilityTheory.covariance X (fun ω => w i * Y i ω) μ :=
        ProbabilityTheory.covariance_fun_sum_right hmem hX
      rw [e]
      simp only [ProbabilityTheory.covariance_const_mul_right, dotProduct, covVector]
    have hvarS : ProbabilityTheory.variance (fun ω => ∑ i, w i * Y i ω) μ
        = dotProduct w (Matrix.mulVec (covMatrix μ Y) w) := by
      have h1 : ProbabilityTheory.variance (fun ω => ∑ i, w i * Y i ω) μ
          = ∑ i, ∑ j, ProbabilityTheory.covariance (fun ω => w i * Y i ω)
            (fun ω => w j * Y j ω) μ :=
        ProbabilityTheory.variance_fun_sum hmem
      rw [h1]
      simp only [ProbabilityTheory.covariance_const_mul_left,
        ProbabilityTheory.covariance_const_mul_right, dotProduct,
        Matrix.mulVec_apply_eq_sum, covMatrix, MathlibExt.Probability.Finance.PortfolioVariance.covMatrix, Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hvar, hcov, hvarS]

end SpatialPredictor
