/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Portfolio variance is wᵀ Σ w

For square-integrable asset returns `R` with covariance matrix `Σ`, the
variance of the weighted return `∑ i, w i * R i` is the quadratic form
`w ⬝ᵥ (Σ *ᵥ w)`. No positive-definiteness and no full-investment
(`∑ w = 1`) hypothesis is used.

## Main results

* `covMatrix`: the covariance matrix of the returns.
* `portfolio_variance_eq_dotProduct_mulVec`: portfolio variance is `wᵀ Σ w`.

Atlas roadmap target FI05.T03.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Probability.Finance.PortfolioVariance

/-- Covariance matrix of the returns `R`: entry `(i, j)` is `cov[R i, R j; μ]`
(source clause: "Σ is the covariance matrix of the asset returns"). -/
noncomputable def covMatrix {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : MeasureTheory.Measure Ω) (R : ι → Ω → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ProbabilityTheory.covariance (R i) (R j) μ

/-- **Portfolio variance is wᵀ Σ w.** The variance of the weighted return
`∑ i, w i * R i` equals the quadratic form `w ⬝ᵥ (Σ *ᵥ w)` in the covariance
matrix (Atlas roadmap FI05.T03). No positive-definiteness or full-investment
(`∑ w = 1`) hypothesis is used. -/
theorem portfolio_variance_eq_dotProduct_mulVec {ι : Type*} {Ω : Type*}
    [MeasurableSpace Ω] [Fintype ι] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {R : ι → Ω → ℝ}
    (hR : ∀ i, MeasureTheory.MemLp (R i) 2 μ) {w : ι → ℝ} :
    ProbabilityTheory.variance (fun ω => ∑ i, w i * R i ω) μ =
      w ⬝ᵥ (covMatrix μ R *ᵥ w) := by
  have hX : ∀ i, MeasureTheory.MemLp (fun ω => w i * R i ω) 2 μ :=
    fun i => (hR i).const_mul (w i)
  rw [ProbabilityTheory.variance_fun_sum hX]
  have hcov : ∀ i j, ProbabilityTheory.covariance (fun ω => w i * R i ω) (fun ω => w j * R j ω) μ
      = w i * w j * ProbabilityTheory.covariance (R i) (R j) μ := by
    intro i j
    rw [ProbabilityTheory.covariance_const_mul_left,
        ProbabilityTheory.covariance_const_mul_right, mul_assoc]
  simp_rw [hcov]
  rw [Matrix.dotProduct_mulVec]
  simp only [covMatrix, Matrix.vecMul, dotProduct, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end MathlibExt.Probability.Finance.PortfolioVariance
