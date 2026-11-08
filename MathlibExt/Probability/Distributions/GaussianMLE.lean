/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianDensity
public import MathlibExt.LinearAlgebra.Matrix.LogDetTrace
public import MathlibExt.LinearAlgebra.Matrix.WeightedScatter

/-!
# Maximum likelihood for the multivariate Gaussian

For positive weights `wᵢ` on points `xᵢ` in `EuclideanSpace ℝ n` not all in an affine hyperplane,
the weighted log-likelihood `∑ i, wᵢ log N(xᵢ | μ, S)` over all means `μ` and positive definite
covariances `S` is largest at the weighted mean and the weighted sample covariance
(`sum_mul_log_multivariateGaussianPDFReal_le`). With all weights one this is the classical
Gaussian MLE (sample mean and sample covariance); with EM responsibilities it is the M-step of a
full-covariance Gaussian mixture.

Main results:

* `multivariateGaussianPDFReal_pos`, `log_multivariateGaussianPDFReal`:
  `log N(x | μ, S) = -(n / 2) log (2 π) - (1 / 2) log det S - (x - μ)ᵀ S⁻¹ (x - μ) / 2`.
* `sum_mul_log_multivariateGaussianPDFReal_eq`: the weighted log-likelihood in terms of the
  weighted scatter matrix, `-(W / 2) (n log (2 π) + log det S + tr (S⁻¹ C(μ)))`.
* `sum_mul_log_multivariateGaussianPDFReal_le_weightedMean`: for a fixed covariance the weighted
  mean is the MLE of the mean.
* `sum_mul_log_multivariateGaussianPDFReal_le_of_posDef`: **the weighted Gaussian MLE**, for a
  positive total weight and a positive definite weighted sample covariance;
  `sum_mul_log_multivariateGaussianPDFReal_le`: the same for positive weights on points in general
  position. The proof splits
  off the bias of `μ` (`sum_mul_quad_sub_eq`) and applies the log-determinant trace inequality
  `Matrix.PosDef.log_det_mul_le_trace`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open Real Matrix WithLp
open scoped RealInnerProductSpace

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

theorem multivariateGaussianPDFReal_pos (μ : EuclideanSpace ℝ n) {S : Matrix n n ℝ}
    (hS : S.PosDef) (x : EuclideanSpace ℝ n) : 0 < multivariateGaussianPDFReal μ S x := by
  unfold multivariateGaussianPDFReal
  have h1 : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < √S.det := Real.sqrt_pos.2 hS.det_pos
  positivity

/-- The log-density: `log N(x | μ, S) = -(n / 2) log (2 π) - (1 / 2) log det S
- (x - μ)ᵀ S⁻¹ (x - μ) / 2`. -/
theorem log_multivariateGaussianPDFReal (μ : EuclideanSpace ℝ n) {S : Matrix n n ℝ}
    (hS : S.PosDef) (x : EuclideanSpace ℝ n) :
    log (multivariateGaussianPDFReal μ S x) = -(Fintype.card n / 2) * log (2 * π) -
      log S.det / 2 - ofLp (x - μ) ⬝ᵥ S⁻¹ *ᵥ ofLp (x - μ) / 2 := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have h1 : 0 < √(2 * π) := Real.sqrt_pos.2 h2π
  have h2 : 0 < √S.det := Real.sqrt_pos.2 hS.det_pos
  unfold multivariateGaussianPDFReal
  rw [log_mul (by positivity) (exp_pos _).ne', log_mul (by positivity) (by positivity), log_exp,
    log_inv, log_inv, log_pow, log_sqrt h2π.le, log_sqrt hS.det_pos.le]
  ring

/-- The weighted Gaussian log-likelihood in terms of the weighted scatter matrix `C(μ)`:
`∑ w log N(x | μ, S) = -(W / 2) (n log (2 π) + log det S + tr (S⁻¹ C(μ)))`, `W = ∑ w`. -/
theorem sum_mul_log_multivariateGaussianPDFReal_eq {w : ι → ℝ} (hw : ∑ i, w i ≠ 0)
    (xs : ι → EuclideanSpace ℝ n) (μ : EuclideanSpace ℝ n) {S : Matrix n n ℝ} (hS : S.PosDef) :
    ∑ i, w i * log (multivariateGaussianPDFReal μ S (xs i)) =
      -((∑ i, w i) / 2) * (Fintype.card n * log (2 * π) + log S.det +
        (S⁻¹ * weightedScatter w xs μ).trace) := by
  have h := sum_mul_quad_eq_trace hw xs S⁻¹ μ
  simp only [log_multivariateGaussianPDFReal _ hS]
  have : ∀ i, w i * (-(Fintype.card n / 2) * log (2 * π) - log S.det / 2 -
      ofLp (xs i - μ) ⬝ᵥ S⁻¹ *ᵥ ofLp (xs i - μ) / 2) =
      w i * (-(Fintype.card n / 2) * log (2 * π) - log S.det / 2) -
        w i * (ofLp (xs i - μ) ⬝ᵥ S⁻¹ *ᵥ ofLp (xs i - μ)) / 2 := fun i => by ring
  simp only [this, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, h]
  ring

/-- **The mean MLE**: for any fixed positive definite covariance `S` and positive total weight,
the weighted mean maximizes the weighted Gaussian log-likelihood over all means. -/
theorem sum_mul_log_multivariateGaussianPDFReal_le_weightedMean {w : ι → ℝ}
    (hw : 0 < ∑ i, w i) (xs : ι → EuclideanSpace ℝ n) (μ : EuclideanSpace ℝ n)
    {S : Matrix n n ℝ} (hS : S.PosDef) :
    ∑ i, w i * log (multivariateGaussianPDFReal μ S (xs i)) ≤
      ∑ i, w i * log (multivariateGaussianPDFReal (weightedMean w xs) S (xs i)) := by
  set m := weightedMean w xs
  have hSsym : (S⁻¹)ᵀ = S⁻¹ := by
    rw [transpose_nonsing_inv]
    congr 1
    simpa [conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have hq0 : 0 ≤ ofLp (m - μ) ⬝ᵥ S⁻¹ *ᵥ ofLp (m - μ) := by
    simpa using (posSemidef_iff_dotProduct_mulVec.1 hS.inv.posSemidef).2 (ofLp (m - μ))
  have hbias : (∑ i, w i) * (S⁻¹ * weightedScatter w xs μ).trace =
      (∑ i, w i) * (S⁻¹ * weightedScatter w xs m).trace +
        (∑ i, w i) * (ofLp (m - μ) ⬝ᵥ S⁻¹ *ᵥ ofLp (m - μ)) := by
    rw [← sum_mul_quad_eq_trace hw.ne' xs, ← sum_mul_quad_eq_trace hw.ne' xs,
      sum_mul_quad_sub_eq hw.ne' xs hSsym]
  rw [sum_mul_log_multivariateGaussianPDFReal_eq hw.ne' xs μ hS,
    sum_mul_log_multivariateGaussianPDFReal_eq hw.ne' xs m hS]
  have h2 := mul_nonneg hw.le hq0
  nlinarith

/-- **The weighted Gaussian MLE**: if the total weight is positive and the weighted sample
covariance is positive definite, then the weighted mean and the weighted sample covariance
maximize the weighted Gaussian log-likelihood `∑ i, wᵢ log N(xᵢ | μ, S)` over all means `μ` and
positive definite covariances `S`. -/
theorem sum_mul_log_multivariateGaussianPDFReal_le_of_posDef {w : ι → ℝ} (hW : 0 < ∑ i, w i)
    {xs : ι → EuclideanSpace ℝ n} (hC : (weightedScatter w xs (weightedMean w xs)).PosDef)
    (μ : EuclideanSpace ℝ n) {S : Matrix n n ℝ} (hS : S.PosDef) :
    ∑ i, w i * log (multivariateGaussianPDFReal μ S (xs i)) ≤
      ∑ i, w i * log (multivariateGaussianPDFReal (weightedMean w xs)
        (weightedScatter w xs (weightedMean w xs)) (xs i)) := by
  set m := weightedMean w xs
  set C := weightedScatter w xs m
  have hSsym : (S⁻¹)ᵀ = S⁻¹ := by
    rw [transpose_nonsing_inv]
    congr 1
    simpa [conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have hq0 : 0 ≤ ofLp (m - μ) ⬝ᵥ S⁻¹ *ᵥ ofLp (m - μ) := by
    simpa using (posSemidef_iff_dotProduct_mulVec.1 hS.inv.posSemidef).2 (ofLp (m - μ))
  -- the bias of `μ`
  have hbias : (∑ i, w i) * (S⁻¹ * weightedScatter w xs μ).trace =
      (∑ i, w i) * (S⁻¹ * C).trace + (∑ i, w i) * (ofLp (m - μ) ⬝ᵥ S⁻¹ *ᵥ ofLp (m - μ)) := by
    rw [← sum_mul_quad_eq_trace hW.ne' xs, ← sum_mul_quad_eq_trace hW.ne' xs,
      sum_mul_quad_sub_eq hW.ne' xs hSsym]
  -- the log-determinant trace inequality
  have hld := hS.inv.log_det_mul_le_trace hC
  rw [det_nonsing_inv, Ring.inverse_eq_inv', log_mul (inv_ne_zero hS.det_pos.ne') hC.det_pos.ne',
    log_inv] at hld
  have hCinv : C⁻¹ * C = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hC.det_pos.ne')
  rw [sum_mul_log_multivariateGaussianPDFReal_eq hW.ne' xs μ hS,
    sum_mul_log_multivariateGaussianPDFReal_eq hW.ne' xs m hC, hCinv, trace_one]
  have h1 := mul_le_mul_of_nonneg_left hld hW.le
  have h2 := mul_nonneg hW.le hq0
  nlinarith

/-- **The weighted Gaussian MLE** on points in general position: for positive weights and points
not all in an affine hyperplane, the weighted mean and the weighted sample covariance maximize the
weighted Gaussian log-likelihood `∑ i, wᵢ log N(xᵢ | μ, S)` over all means `μ` and positive
definite covariances `S`. -/
theorem sum_mul_log_multivariateGaussianPDFReal_le {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {xs : ι → EuclideanSpace ℝ n}
    (hspan : ∀ v : EuclideanSpace ℝ n, v ≠ 0 → ∃ i j, ⟪v, xs i⟫ ≠ ⟪v, xs j⟫) [Nonempty ι]
    (μ : EuclideanSpace ℝ n) {S : Matrix n n ℝ} (hS : S.PosDef) :
    ∑ i, w i * log (multivariateGaussianPDFReal μ S (xs i)) ≤
      ∑ i, w i * log (multivariateGaussianPDFReal (weightedMean w xs)
        (weightedScatter w xs (weightedMean w xs)) (xs i)) :=
  sum_mul_log_multivariateGaussianPDFReal_le_of_posDef
    (Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty) (weightedScatter_posDef hw hspan _) μ hS

end MetaMathlibExt
