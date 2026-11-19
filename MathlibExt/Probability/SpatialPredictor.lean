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

- Valid covariance: `ProbabilityTheory.posSemidef_covariance_matrix`
  (existing API, reused here).
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

/-- Covariance vector between target and observations:
`c i = Cov(X, Y i)`. -/
noncomputable def covVector {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (X : Ω → ℝ)
    (Y : Fin n → Ω → ℝ) : Fin n → ℝ :=
  fun i => ProbabilityTheory.covariance X (Y i) μ

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
          + dotProduct w (Matrix.mulVec (MathlibExt.Probability.Finance.PortfolioVariance.covMatrix μ Y) w) := by
  have hSmem : MeasureTheory.MemLp (fun ω => ∑ i, w i * Y i ω) 2 μ := by
    have h := MeasureTheory.memLp_finsetSum (p := 2) (μ := μ) Finset.univ
      (f := fun i ω => w i * Y i ω) (fun i _ => (hY i).const_mul (w i))
    simpa using h
  have hSint : ∀ i, MeasureTheory.Integrable (fun ω => w i * Y i ω) μ :=
    fun i => ((hY i).integrable (by simp)).const_mul (w i)
  refine ⟨?_, ?_⟩
  · have h1 : ∫ ω, ∑ i, w i * Y i ω ∂μ = ∑ i, w i * μ[Y i] := by
      have h := MeasureTheory.integral_finsetSum (μ := μ) Finset.univ
        (f := fun i ω => w i * Y i ω) (fun i _ => hSint i)
      simp only [MeasureTheory.integral_const_mul] at h
      simpa using h
    rw [show μ[fun ω => ∑ i, w i * Y i ω] = ∫ ω, ∑ i, w i * Y i ω ∂μ from rfl, h1]
    simp_rw [hm, ← Finset.sum_mul, hw, one_mul]
  · have hvar : ProbabilityTheory.variance (fun ω => X ω - ∑ i, w i * Y i ω) μ
        = ProbabilityTheory.variance X μ
          - 2 * ProbabilityTheory.covariance X (fun ω => ∑ i, w i * Y i ω) μ
          + ProbabilityTheory.variance (fun ω => ∑ i, w i * Y i ω) μ :=
      ProbabilityTheory.variance_fun_sub hX hSmem
    have hcov : ProbabilityTheory.covariance X (fun ω => ∑ i, w i * Y i ω) μ
        = dotProduct w (covVector μ X Y) := by
      have h := ProbabilityTheory.covariance_fun_sum_right
        (X := fun i ω => w i * Y i ω) (Y := X) (μ := μ)
        (fun i => (hY i).const_mul (w i)) hX
      simp_rw [ProbabilityTheory.covariance_const_mul_right] at h
      simpa [dotProduct, covVector] using h
    have hvarS : ProbabilityTheory.variance (fun ω => ∑ i, w i * Y i ω) μ
        = dotProduct w (Matrix.mulVec (MathlibExt.Probability.Finance.PortfolioVariance.covMatrix μ Y) w) :=
      MathlibExt.Probability.Finance.PortfolioVariance.portfolio_variance_eq_dotProduct_mulVec hY
    rw [hvar, hcov, hvarS]

end SpatialPredictor
