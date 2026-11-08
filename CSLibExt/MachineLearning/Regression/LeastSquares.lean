/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Least squares, ridge and lasso regression as maximum likelihood and MAP estimation

A linear regression model predicts responses `y : Fin m → ℝ` from a design matrix
`X : Matrix (Fin m) ι ℝ` (one row per example) by `X *ᵥ θ`. The residual sum of squares is
`rss X y θ = ∑ k, (y k - (X θ) k)²`, written as the dot product `(y - X θ) ⬝ᵥ (y - X θ)`. (Vectors
`Fin m → ℝ` carry the sup norm in Mathlib, so sums of squares are written as dot products, not
norms.)

## Main results

* `rss_add`, `rss_eq_of_normal`: expansion of the residual sum of squares around any `θ₀`;
  if `θ₀` solves the normal equations `Xᵀ X θ₀ = Xᵀ y`, then
  `rss θ = rss θ₀ + (X (θ - θ₀)) ⬝ᵥ (X (θ - θ₀))` (Pythagoras).
* `rss_le_iff_normal`: `θ₀` minimizes the residual sum of squares if and only if it solves the
  normal equations; `exists_normal`: the normal equations always have a solution (for any design,
  including rank-deficient ones), so a least-squares estimate exists. `normal_inv`: when `Xᵀ X` is
  invertible the solution is
  `(Xᵀ X)⁻¹ Xᵀ y`, the least-squares matrix of MathlibExt's Gauss–Markov theorem
  (`MathlibExt.Probability.Statistics.GaussMarkov.gaussMarkov_covariance_minimality`).
* `gaussLikelihood_eq`, `gaussLikelihood_le_iff`: with independent Gaussian noise of variance
  `σ²`, the likelihood is a decreasing function of the residual sum of squares, so **least
  squares is maximum likelihood** (`isMaxOn_gaussLikelihood_iff`, and
  `exists_isMaxOn_gaussLikelihood` for existence).
* Ridge regression `rss + λ θ ⬝ᵥ θ`: `ridge_eq_of_normal`, `ridge_le_of_normal`; for `λ > 0`
  the matrix `Xᵀ X + λ I` is positive definite (`posDef_ridge`) and `ridgeEstimate` is the unique
  minimizer. `ridgePosterior_le_iff`: under the Gaussian prior `θ i ~ N(0, τ²)` the posterior
  kernel is a decreasing function of the ridge objective with `λ = σ² / τ²`, so **ridge is the
  MAP estimate** (`isMaxOn_ridgePosterior`).
* Lasso `rss + λ ∑ |θ i|`: `lassoPosterior_le_iff`: under the Laplace prior with scale `b` the
  posterior kernel is a decreasing function of the lasso objective with `λ = 2 σ² / b`, so
  **lasso is the MAP estimate**; `convexOn_lasso`. For an orthonormal design (`Xᵀ X = 1`),
  `lasso_softThreshold_le`: soft thresholding of `Xᵀ y` at `λ / 2` minimizes the lasso
  objective (`softThreshold_le` in one dimension).

The Gaussian MLE of linear regression is the Gaussian case of a canonical generalized linear
model; see `glmLoss_sq` in `CSLibExt/MachineLearning/Discriminative/ExponentialFamily.lean`.
-/

@[expose] public section

namespace Cslib.MachineLearning.LeastSquares

open Matrix Finset Real

variable {ι : Type*} [Fintype ι] {m : ℕ}

private theorem dot_self_nonneg {n : Type*} [Fintype n] (w : n → ℝ) : 0 ≤ w ⬝ᵥ w := by
  simpa using dotProduct_star_self_nonneg w

/-- The residual sum of squares `∑ k, (y k - (X θ) k)²`. -/
noncomputable def rss (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (θ : ι → ℝ) : ℝ :=
  (y - X *ᵥ θ) ⬝ᵥ (y - X *ᵥ θ)

theorem rss_eq_sum (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (θ : ι → ℝ) :
    rss X y θ = ∑ k, (y k - (X *ᵥ θ) k) ^ 2 := by
  simp [rss, dotProduct, sq]

theorem mulVec_dotProduct_eq (X : Matrix (Fin m) ι ℝ) (v : ι → ℝ) (r : Fin m → ℝ) :
    (X *ᵥ v) ⬝ᵥ r = v ⬝ᵥ (Xᵀ *ᵥ r) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- Expansion of the residual sum of squares around `θ`. -/
theorem rss_add (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (θ v : ι → ℝ) :
    rss X y (θ + v) =
      rss X y θ - 2 * (v ⬝ᵥ (Xᵀ *ᵥ (y - X *ᵥ θ))) + (X *ᵥ v) ⬝ᵥ (X *ᵥ v) := by
  have h : y - X *ᵥ (θ + v) = (y - X *ᵥ θ) - X *ᵥ v := by rw [mulVec_add]; abel
  rw [rss, h, rss, ← mulVec_dotProduct_eq]
  set r := y - X *ᵥ θ
  set w := X *ᵥ v
  clear_value r w
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm r w]
  ring

theorem normal_iff (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (θ : ι → ℝ) :
    Xᵀ *ᵥ (X *ᵥ θ) = Xᵀ *ᵥ y ↔ Xᵀ *ᵥ (y - X *ᵥ θ) = 0 := by
  rw [mulVec_sub, sub_eq_zero, eq_comm]

/-- **Pythagoras for least squares**: at a solution `θ₀` of the normal equations,
`rss θ = rss θ₀ + (X (θ - θ₀)) ⬝ᵥ (X (θ - θ₀))`. -/
theorem rss_eq_of_normal {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {θ₀ : ι → ℝ}
    (h : Xᵀ *ᵥ (X *ᵥ θ₀) = Xᵀ *ᵥ y) (θ : ι → ℝ) :
    rss X y θ = rss X y θ₀ + (X *ᵥ (θ - θ₀)) ⬝ᵥ (X *ᵥ (θ - θ₀)) := by
  have := rss_add X y θ₀ (θ - θ₀)
  rwa [add_sub_cancel, (normal_iff X y θ₀).1 h, dotProduct_zero, mul_zero, sub_zero] at this

theorem rss_le_of_normal {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {θ₀ : ι → ℝ}
    (h : Xᵀ *ᵥ (X *ᵥ θ₀) = Xᵀ *ᵥ y) (θ : ι → ℝ) : rss X y θ₀ ≤ rss X y θ := by
  rw [rss_eq_of_normal h θ]
  exact le_add_of_nonneg_right (dot_self_nonneg _)

theorem eq_zero_of_forall_quadratic {b q : ℝ} (hq : 0 ≤ q)
    (h : ∀ t : ℝ, 0 ≤ -2 * t * b + t ^ 2 * q) : b = 0 := by
  by_contra hb
  have hq1 : 0 < q + 1 := by linarith
  have key : -2 * (b / (q + 1)) * b + (b / (q + 1)) ^ 2 * q =
      -(b ^ 2 * (q + 2) / (q + 1) ^ 2) := by
    field_simp
    ring
  have hpos : 0 < b ^ 2 * (q + 2) / (q + 1) ^ 2 := by positivity
  linarith [h (b / (q + 1))]

/-- **Least squares and the normal equations**: `θ₀` minimizes the residual sum of squares if
and only if `Xᵀ X θ₀ = Xᵀ y`. -/
theorem rss_le_iff_normal (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (θ₀ : ι → ℝ) :
    (∀ θ, rss X y θ₀ ≤ rss X y θ) ↔ Xᵀ *ᵥ (X *ᵥ θ₀) = Xᵀ *ᵥ y := by
  refine ⟨fun hmin => ?_, rss_le_of_normal⟩
  rw [normal_iff]
  have hg : (Xᵀ *ᵥ (y - X *ᵥ θ₀)) ⬝ᵥ (Xᵀ *ᵥ (y - X *ᵥ θ₀)) = 0 := by
    refine eq_zero_of_forall_quadratic (dot_self_nonneg (X *ᵥ (Xᵀ *ᵥ (y - X *ᵥ θ₀))))
      fun t => ?_
    have := hmin (θ₀ + t • (Xᵀ *ᵥ (y - X *ᵥ θ₀)))
    rw [rss_add, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul, smul_eq_mul] at this
    nlinarith
  exact dotProduct_self_eq_zero.1 hg

/-- **Least-squares estimates exist**: the normal equations `Xᵀ X θ = Xᵀ y` always have a
solution, because `Xᵀ X` and `Xᵀ` have the same range (`Matrix.rank_transpose_mul_self`). -/
theorem exists_normal (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) :
    ∃ θ, Xᵀ *ᵥ (X *ᵥ θ) = Xᵀ *ᵥ y := by
  classical
  have hle : LinearMap.range (Xᵀ * X).mulVecLin ≤ LinearMap.range Xᵀ.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    exact ⟨X *ᵥ v, by simp⟩
  have heq : LinearMap.range (Xᵀ * X).mulVecLin = LinearMap.range Xᵀ.mulVecLin := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    change (Xᵀ * X).rank = Xᵀ.rank
    rw [rank_transpose_mul_self, rank_transpose]
  obtain ⟨θ, hθ⟩ : Xᵀ *ᵥ y ∈ LinearMap.range (Xᵀ * X).mulVecLin := heq ▸ ⟨y, rfl⟩
  exact ⟨θ, by rw [mulVec_mulVec]; exact hθ⟩

theorem exists_rss_le (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) :
    ∃ θ₀, ∀ θ, rss X y θ₀ ≤ rss X y θ :=
  (exists_normal X y).imp fun _ h => rss_le_of_normal h

variable [DecidableEq ι]

/-- When `Xᵀ X` is invertible, `(Xᵀ X)⁻¹ Xᵀ y` solves the normal equations. -/
theorem normal_inv {X : Matrix (Fin m) ι ℝ} (hX : IsUnit (Xᵀ * X).det) (y : Fin m → ℝ) :
    Xᵀ *ᵥ (X *ᵥ (((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y)) = Xᵀ *ᵥ y := by
  rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hX, Matrix.one_mul]

omit [DecidableEq ι] in
/-- The residual sum of squares is convex. -/
theorem convexOn_rss (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) :
    ConvexOn ℝ Set.univ (rss X y) := by
  refine ⟨convex_univ, fun θ _ θ' _ a b ha hb hab => ?_⟩
  simp only [rss_eq_sum, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun k _ => ?_
  have hlin : (X *ᵥ (a • θ + b • θ')) k = a * (X *ᵥ θ) k + b * (X *ᵥ θ') k := by
    simp [mulVec_add, mulVec_smul]
  rw [hlin]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg ha hb, sq_nonneg ((X *ᵥ θ) k - (X *ᵥ θ') k)]

/-! ### Gaussian noise: least squares is maximum likelihood -/

section Gaussian

open NNReal ProbabilityTheory

omit [DecidableEq ι] in
/-- The likelihood of the responses under independent Gaussian noise with variance `v`. Following
Mathlib's `gaussianPDFReal`, the variance is in `ℝ≥0` and `v = 0` gives the zero function, not a
Dirac kernel; the probabilistic statements below assume `v ≠ 0`. -/
noncomputable def gaussLikelihood (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (v : ℝ≥0)
    (θ : ι → ℝ) : ℝ :=
  ∏ k, gaussianPDFReal ((X *ᵥ θ) k) v (y k)

omit [DecidableEq ι] in
theorem gaussLikelihood_eq (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (v : ℝ≥0) (θ : ι → ℝ) :
    gaussLikelihood X y v θ = (√(2 * π * v))⁻¹ ^ m * exp (-rss X y θ / (2 * v)) := by
  rw [gaussLikelihood]
  simp only [gaussianPDFReal]
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← exp_sum, rss_eq_sum,
    ← sum_div, ← sum_neg_distrib]

theorem normConst_pos {v : ℝ≥0} (hv : v ≠ 0) (n : ℕ) : 0 < (√(2 * π * v))⁻¹ ^ n := by
  have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (by exact_mod_cast hv))
  positivity

omit [DecidableEq ι] in
/-- With Gaussian noise the likelihood is a decreasing function of the residual sum of
squares. -/
theorem gaussLikelihood_le_iff {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (θ θ' : ι → ℝ) :
    gaussLikelihood X y v θ ≤ gaussLikelihood X y v θ' ↔ rss X y θ' ≤ rss X y θ := by
  have hv' : (0 : ℝ) < 2 * v := by
    have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (by exact_mod_cast hv))
    linarith
  rw [gaussLikelihood_eq, gaussLikelihood_eq, mul_le_mul_iff_right₀ (normConst_pos hv m),
    exp_le_exp, div_le_div_iff_of_pos_right hv', neg_le_neg_iff]

omit [DecidableEq ι] in
/-- **Least squares is maximum likelihood**: with Gaussian noise, `θ₀` maximizes the likelihood
if and only if it solves the normal equations. -/
theorem isMaxOn_gaussLikelihood_iff {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (θ₀ : ι → ℝ) :
    IsMaxOn (gaussLikelihood X y v) Set.univ θ₀ ↔ Xᵀ *ᵥ (X *ᵥ θ₀) = Xᵀ *ᵥ y := by
  rw [← rss_le_iff_normal]
  exact ⟨fun h θ => (gaussLikelihood_le_iff hv θ θ₀).1 (h (Set.mem_univ θ)),
    fun h θ _ => (gaussLikelihood_le_iff hv θ θ₀).2 (h θ)⟩

omit [DecidableEq ι] in
/-- A maximum likelihood estimate exists for every design. -/
theorem exists_isMaxOn_gaussLikelihood (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) : ∃ θ₀, IsMaxOn (gaussLikelihood X y v) Set.univ θ₀ :=
  (exists_normal X y).imp fun θ₀ h => (isMaxOn_gaussLikelihood_iff hv θ₀).2 h

end Gaussian

/-! ### Ridge regression: MAP under a Gaussian prior -/

section Ridge

open NNReal ProbabilityTheory

omit [DecidableEq ι] in
/-- The ridge objective `rss X y θ + λ θ ⬝ᵥ θ`. -/
noncomputable def ridge (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (lam : ℝ) (θ : ι → ℝ) : ℝ :=
  rss X y θ + lam * (θ ⬝ᵥ θ)

/-- At a solution of the ridge normal equations `(Xᵀ X + λ I) θ₀ = Xᵀ y`,
`ridge θ = ridge θ₀ + (X (θ - θ₀)) ⬝ᵥ (X (θ - θ₀)) + λ (θ - θ₀) ⬝ᵥ (θ - θ₀)`. -/
theorem ridge_eq_of_normal {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {lam : ℝ} {θ₀ : ι → ℝ}
    (h : (Xᵀ * X + lam • 1) *ᵥ θ₀ = Xᵀ *ᵥ y) (θ : ι → ℝ) :
    ridge X y lam θ = ridge X y lam θ₀ + (X *ᵥ (θ - θ₀)) ⬝ᵥ (X *ᵥ (θ - θ₀)) +
      lam * ((θ - θ₀) ⬝ᵥ (θ - θ₀)) := by
  have hres : Xᵀ *ᵥ (y - X *ᵥ θ₀) = lam • θ₀ := by
    rw [add_mulVec, smul_mulVec, one_mulVec, ← mulVec_mulVec] at h
    rw [mulVec_sub, ← h]
    abel
  have hr := rss_add X y θ₀ (θ - θ₀)
  rw [add_sub_cancel, hres, dotProduct_smul, smul_eq_mul] at hr
  rw [ridge, ridge, hr]
  have hθ : θ = θ₀ + (θ - θ₀) := by abel
  set d := θ - θ₀
  rw [hθ]
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm d θ₀]
  ring

/-- Solutions of the ridge normal equations minimize the ridge objective (for `λ ≥ 0`). -/
theorem ridge_le_of_normal {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    {θ₀ : ι → ℝ} (h : (Xᵀ * X + lam • 1) *ᵥ θ₀ = Xᵀ *ᵥ y) (θ : ι → ℝ) :
    ridge X y lam θ₀ ≤ ridge X y lam θ := by
  rw [ridge_eq_of_normal h θ, add_assoc]
  exact le_add_of_nonneg_right (add_nonneg (dot_self_nonneg _)
    (mul_nonneg hlam (dot_self_nonneg _)))

omit [Fintype ι] in
/-- For `λ > 0` the ridge matrix `Xᵀ X + λ I` is positive definite. -/
theorem posDef_ridge [Finite ι] (X : Matrix (Fin m) ι ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (Xᵀ * X + lam • (1 : Matrix ι ι ℝ)).PosDef := by
  have := Fintype.ofFinite ι
  have h1 : (Xᵀ * X).PosSemidef := by
    have := posSemidef_conjTranspose_mul_self X
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  simpa [add_comm] using (PosDef.one.smul hlam).add_posSemidef h1

/-- The ridge estimate `(Xᵀ X + λ I)⁻¹ Xᵀ y`. -/
noncomputable def ridgeEstimate (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (lam : ℝ) : ι → ℝ :=
  (Xᵀ * X + lam • 1)⁻¹ *ᵥ (Xᵀ *ᵥ y)

theorem ridgeEstimate_normal (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {lam : ℝ}
    (hlam : 0 < lam) : (Xᵀ * X + lam • 1) *ᵥ ridgeEstimate X y lam = Xᵀ *ᵥ y := by
  rw [ridgeEstimate, mulVec_mulVec, mul_nonsing_inv _ ((posDef_ridge X hlam).det_pos.ne').isUnit,
    one_mulVec]

/-- **Closed form of ridge regression**: for `λ > 0`, `(Xᵀ X + λ I)⁻¹ Xᵀ y` is the unique
minimizer of the ridge objective. -/
theorem ridge_le_ridgeEstimate (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {lam : ℝ}
    (hlam : 0 < lam) (θ : ι → ℝ) : ridge X y lam (ridgeEstimate X y lam) ≤ ridge X y lam θ :=
  ridge_le_of_normal hlam.le (ridgeEstimate_normal X y hlam) θ

theorem eq_ridgeEstimate_of_ridge_le (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {lam : ℝ}
    (hlam : 0 < lam) {θ : ι → ℝ} (hθ : ridge X y lam θ ≤ ridge X y lam (ridgeEstimate X y lam)) :
    θ = ridgeEstimate X y lam := by
  have h := ridge_eq_of_normal (ridgeEstimate_normal X y hlam) θ
  have h1 := dot_self_nonneg (X *ᵥ (θ - ridgeEstimate X y lam))
  have h2 : (θ - ridgeEstimate X y lam) ⬝ᵥ (θ - ridgeEstimate X y lam) = 0 := by
    have h3 := dot_self_nonneg (θ - ridgeEstimate X y lam)
    nlinarith
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h2)

omit [DecidableEq ι] in
/-- The density of independent `N(0, τ)` coordinates (for `τ ≠ 0`; at `τ = 0` Mathlib's
`gaussianPDFReal` is the zero function). -/
theorem prod_gaussianPDFReal_zero (τ : ℝ≥0) (θ : ι → ℝ) :
    ∏ i, gaussianPDFReal 0 τ (θ i) =
      (√(2 * π * τ))⁻¹ ^ Fintype.card ι * exp (-(θ ⬝ᵥ θ) / (2 * τ)) := by
  simp only [gaussianPDFReal, sub_zero]
  rw [prod_mul_distrib, prod_const, card_univ, ← exp_sum]
  congr 2
  rw [← sum_div, sum_neg_distrib]
  simp [dotProduct, sq]

omit [DecidableEq ι] in
/-- The posterior kernel of linear regression with Gaussian noise of variance `v` and the
Gaussian prior `θ i ~ N(0, τ)`, a meaningful kernel for `v ≠ 0` and `τ ≠ 0` (as for
`gaussLikelihood`, zero variances give the zero function). -/
noncomputable def ridgePosterior (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (v τ : ℝ≥0)
    (θ : ι → ℝ) : ℝ :=
  gaussLikelihood X y v θ * ∏ i, gaussianPDFReal 0 τ (θ i)

omit [DecidableEq ι] in
theorem ridgePosterior_eq (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (τ : ℝ≥0) (θ : ι → ℝ) :
    ridgePosterior X y v τ θ = (√(2 * π * v))⁻¹ ^ m * (√(2 * π * τ))⁻¹ ^ Fintype.card ι *
      exp (-ridge X y (v / τ) θ / (2 * v)) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [ridgePosterior, gaussLikelihood_eq, prod_gaussianPDFReal_zero, mul_mul_mul_comm, ← exp_add,
    ridge]
  congr 2
  by_cases hτ : (τ : ℝ) = 0
  · simp [hτ]
  · field_simp
    ring

omit [DecidableEq ι] in
/-- **Ridge regression is MAP estimation**: under Gaussian noise of variance `v` and the
Gaussian prior `θ i ~ N(0, τ)`, the posterior kernel is a decreasing function of the ridge
objective with `λ = v / τ`. -/
theorem ridgePosterior_le_iff {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {v τ : ℝ≥0} (hv : v ≠ 0)
    (hτ : τ ≠ 0) (θ θ' : ι → ℝ) :
    ridgePosterior X y v τ θ ≤ ridgePosterior X y v τ θ' ↔
      ridge X y (v / τ) θ' ≤ ridge X y (v / τ) θ := by
  have hv' : (0 : ℝ) < 2 * v := by
    have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (by exact_mod_cast hv))
    linarith
  rw [ridgePosterior_eq X y hv, ridgePosterior_eq X y hv,
    mul_le_mul_iff_right₀ (mul_pos (normConst_pos hv m) (normConst_pos hτ _)), exp_le_exp,
    div_le_div_iff_of_pos_right hv', neg_le_neg_iff]

/-- The ridge estimate with `λ = v / τ` maximizes the posterior kernel. -/
theorem isMaxOn_ridgePosterior (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {v τ : ℝ≥0}
    (hv : v ≠ 0) (hτ : τ ≠ 0) :
    IsMaxOn (ridgePosterior X y v τ) Set.univ (ridgeEstimate X y (v / τ)) := by
  have hlam : (0 : ℝ) < v / τ := by
    have h1 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (by exact_mod_cast hv))
    have h2 : (0 : ℝ) < τ := lt_of_le_of_ne τ.2 (Ne.symm (by exact_mod_cast hτ))
    positivity
  exact fun θ _ => (ridgePosterior_le_iff hv hτ θ _).2 (ridge_le_ridgeEstimate X y hlam θ)

end Ridge

/-! ### Lasso: MAP under a Laplace prior -/

section Lasso

omit [DecidableEq ι] in
/-- The lasso objective `rss X y θ + λ ∑ i, |θ i|`. -/
noncomputable def lasso (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (lam : ℝ) (θ : ι → ℝ) : ℝ :=
  rss X y θ + lam * ∑ i, |θ i|

/-- The density of the Laplace distribution with location `0` and scale `b`. As for Mathlib's
`gaussianPDFReal`, the scale is in `ℝ≥0`; `b = 0` gives the zero function, and the probabilistic
statements assume `b ≠ 0`. -/
noncomputable def laplacePDF (b : NNReal) (x : ℝ) : ℝ :=
  exp (-|x| / b) / (2 * b)

theorem laplacePDF_pos {b : NNReal} (hb : b ≠ 0) (x : ℝ) : 0 < laplacePDF b x := by
  have : (0 : ℝ) < b := lt_of_le_of_ne b.2 (Ne.symm (by exact_mod_cast hb))
  unfold laplacePDF
  positivity

omit [DecidableEq ι] in
theorem prod_laplacePDF (b : NNReal) (θ : ι → ℝ) :
    ∏ i, laplacePDF b (θ i) = (2 * b)⁻¹ ^ Fintype.card ι * exp (-(∑ i, |θ i|) / b) := by
  simp only [laplacePDF, div_eq_mul_inv (exp _)]
  rw [prod_mul_distrib, prod_const, card_univ, ← exp_sum, mul_comm]
  congr 2
  rw [← sum_div, sum_neg_distrib]

omit [DecidableEq ι] in
/-- The posterior kernel of linear regression with Gaussian noise of variance `v` and the
Laplace prior with scale `b` on each coordinate, a meaningful kernel for `v ≠ 0` and `b ≠ 0`. -/
noncomputable def lassoPosterior (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (v b : NNReal)
    (θ : ι → ℝ) : ℝ :=
  gaussLikelihood X y v θ * ∏ i, laplacePDF b (θ i)

omit [DecidableEq ι] in
theorem lassoPosterior_eq (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {v : NNReal} (hv : v ≠ 0)
    {b : NNReal} (hb : b ≠ 0) (θ : ι → ℝ) :
    lassoPosterior X y v b θ = (√(2 * π * v))⁻¹ ^ m * (2 * b)⁻¹ ^ Fintype.card ι *
      exp (-lasso X y (2 * v / b) θ / (2 * v)) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  rw [lassoPosterior, gaussLikelihood_eq, prod_laplacePDF, mul_mul_mul_comm, ← exp_add, lasso]
  congr 2
  field_simp
  ring

omit [DecidableEq ι] in
/-- **Lasso is MAP estimation**: under Gaussian noise of variance `v` and the Laplace prior with
scale `b`, the posterior kernel is a decreasing function of the lasso objective with
`λ = 2 v / b`. -/
theorem lassoPosterior_le_iff {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {v : NNReal} (hv : v ≠ 0)
    {b : NNReal} (hb : b ≠ 0) (θ θ' : ι → ℝ) :
    lassoPosterior X y v b θ ≤ lassoPosterior X y v b θ' ↔
      lasso X y (2 * v / b) θ' ≤ lasso X y (2 * v / b) θ := by
  have hv' : (0 : ℝ) < 2 * v := by
    have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (by exact_mod_cast hv))
    linarith
  have hb' : (0 : ℝ) < b := lt_of_le_of_ne b.2 (Ne.symm (by exact_mod_cast hb))
  rw [lassoPosterior_eq X y hv hb, lassoPosterior_eq X y hv hb,
    mul_le_mul_iff_right₀ (mul_pos (normConst_pos hv m) (by positivity)), exp_le_exp,
    div_le_div_iff_of_pos_right hv', neg_le_neg_iff]

omit [DecidableEq ι] in
/-- The lasso objective is convex for `λ ≥ 0`. -/
theorem convexOn_lasso (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ConvexOn ℝ Set.univ (lasso X y lam) := by
  refine (convexOn_rss X y).add ⟨convex_univ, fun θ _ θ' _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  rw [← mul_assoc, ← mul_assoc, mul_comm a lam, mul_comm b lam, mul_assoc, mul_assoc, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hlam
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  calc |a * θ i + b * θ' i| ≤ |a * θ i| + |b * θ' i| := abs_add_le _ _
    _ = a * |θ i| + b * |θ' i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- Soft thresholding at `t`: for `t ≥ 0`, shrink `z` towards `0` by `t`, and set it to `0` when
`|z| ≤ t`. -/
noncomputable def softThreshold (t z : ℝ) : ℝ :=
  if t < z then z - t else if z < -t then z + t else 0

/-- **Soft thresholding solves the one-dimensional lasso**: for `t ≥ 0` it minimizes
`(z - s)² + 2 t |s|`. -/
theorem softThreshold_le {t : ℝ} (ht : 0 ≤ t) (z s : ℝ) :
    (z - softThreshold t z) ^ 2 + 2 * t * |softThreshold t z| ≤ (z - s) ^ 2 + 2 * t * |s| := by
  unfold softThreshold
  split_ifs with h1 h2
  · rw [abs_of_pos (by linarith)]
    rcases abs_cases s with ⟨hs, hs0⟩ | ⟨hs, hs0⟩ <;> rw [hs]
    · nlinarith [sq_nonneg (z - s - t)]
    · nlinarith [sq_nonneg (z - s - t), mul_nonneg ht (neg_nonneg.2 hs0.le)]
  · rw [abs_of_neg (by linarith)]
    rcases abs_cases s with ⟨hs, hs0⟩ | ⟨hs, hs0⟩ <;> rw [hs]
    · nlinarith [sq_nonneg (z - s + t), mul_nonneg ht hs0]
    · nlinarith [sq_nonneg (z - s + t)]
  · simp only [sub_zero, abs_zero, mul_zero, add_zero]
    rcases abs_cases s with ⟨hs, hs0⟩ | ⟨hs, hs0⟩ <;> rw [hs]
    · nlinarith [mul_nonneg hs0 (show 0 ≤ t - z by linarith)]
    · nlinarith [mul_nonneg (neg_nonneg.2 hs0.le) (show 0 ≤ t + z by linarith)]

/-- **Lasso with an orthonormal design**: when `Xᵀ X = 1`, soft thresholding of `Xᵀ y` at `λ / 2`
coordinatewise minimizes the lasso objective. -/
theorem lasso_softThreshold_le {X : Matrix (Fin m) ι ℝ} (hX : Xᵀ * X = 1) (y : Fin m → ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (θ : ι → ℝ) :
    lasso X y lam (fun i => softThreshold (lam / 2) ((Xᵀ *ᵥ y) i)) ≤ lasso X y lam θ := by
  have hnormal : Xᵀ *ᵥ (X *ᵥ (Xᵀ *ᵥ y)) = Xᵀ *ᵥ y := by
    rw [mulVec_mulVec, hX, one_mulVec]
  have hsq : ∀ d : ι → ℝ, (X *ᵥ d) ⬝ᵥ (X *ᵥ d) = d ⬝ᵥ d := fun d => by
    rw [mulVec_dotProduct_eq, mulVec_mulVec, hX, one_mulVec]
  have hsep : ∀ θ : ι → ℝ, lasso X y lam θ = rss X y (Xᵀ *ᵥ y) +
      ∑ i, ((θ i - (Xᵀ *ᵥ y) i) ^ 2 + lam * |θ i|) := fun θ => by
    rw [lasso, rss_eq_of_normal hnormal θ, hsq, sum_add_distrib, ← mul_sum]
    simp [dotProduct, sq, add_assoc]
  rw [hsep, hsep]
  refine add_le_add le_rfl (sum_le_sum fun i _ => ?_)
  have h := softThreshold_le (t := lam / 2) (by linarith) ((Xᵀ *ᵥ y) i) (θ i)
  rw [show 2 * (lam / 2) = lam by ring] at h
  calc (softThreshold (lam / 2) ((Xᵀ *ᵥ y) i) - (Xᵀ *ᵥ y) i) ^ 2 +
        lam * |softThreshold (lam / 2) ((Xᵀ *ᵥ y) i)|
      = ((Xᵀ *ᵥ y) i - softThreshold (lam / 2) ((Xᵀ *ᵥ y) i)) ^ 2 +
        lam * |softThreshold (lam / 2) ((Xᵀ *ᵥ y) i)| := by ring
    _ ≤ ((Xᵀ *ᵥ y) i - θ i) ^ 2 + lam * |θ i| := h
    _ = (θ i - (Xᵀ *ᵥ y) i) ^ 2 + lam * |θ i| := by ring

end Lasso

end Cslib.MachineLearning.LeastSquares
