/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import MathlibExt.Biology.StatisticalGenetics.MixedModel
public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# BOLT-LMM: the linear mixed model, GLS, the score test and Henderson's equations

BOLT-LMM (Loh et al. 2015) tests each SNP for association with a quantitative phenotype under
the linear mixed model

  `y = X β + g + e`,  `g ~ N(0, σ_g² K)`,  `e ~ N(0, σ_e² I)`,

for `n` individuals, a fixed-effect design `X : Matrix (Fin n) (Fin p) ℝ` (covariates), a
positive semidefinite genetic relationship matrix `K`, a genetic variance `σ_g² ≥ 0` and an
environmental variance `σ_e² > 0`. Integrating out `g` gives the marginal model
`y ~ N(X β, V)` with `V = σ_g² K + σ_e² I`, which is positive definite (`Model.posDef_V`).

* **GLS.** The marginal log-likelihood `Model.logLik y μ` is the log of the `N(μ, V)` density
  at `y`. When `X` has full column rank, the generalized least-squares estimator
  `β̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y` (`Model.gls`) is its unique maximizer over the mean `X β`
  (`Model.logLik_le_logLik_gls`, `Model.logLik_eq_logLik_gls_iff`), and the maximum is
  `-(n log 2π + log det V + yᵀ P y) / 2` with
  `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` (`Model.logLik_gls`).
* **Score test for one SNP.** Adding a SNP `x` with effect `γ`, the profile log-likelihood
  `Model.profileLogLik γ = sup_β logLik y (X β + γ x)` is exactly the quadratic
  `ℓ(0) + γ xᵀ P y - γ² xᵀ P x / 2` (`Model.profileLogLik_eq_quadratic`). So the score at
  `γ = 0` is `U = xᵀ P y = xᵀ V⁻¹ (y - X β̂)` (`Model.hasDerivAt_profileLogLik`,
  `Model.score_eq`), the observed information is `xᵀ P x`, positive when `x` is not in the
  column space of `X` (`Model.info_pos`), and the score statistic is
  `U² / xᵀ P x` (`Model.scoreStat`). Since `P X = 0` and `P V P = P`
  (`Model.proj_mul_X`, `Model.proj_mul_V_mul_proj`), under the null model the score does not
  depend on `β` and its variance `xᵀ P V P x` equals the information; these are the facts
  that calibrate the statistic as a `χ²₁` score test (the distributional statement is not
  formalized here).
* **Henderson's mixed-model equations.** With `R = σ_e² I` and `G = σ_g² K` invertible
  (`K` positive definite, `σ_g² > 0`), a pair `(β, g)` solves Henderson's equations
  `Xᵀ R⁻¹ X β + Xᵀ R⁻¹ g = Xᵀ R⁻¹ y`, `R⁻¹ X β + (R⁻¹ + G⁻¹) g = R⁻¹ y` iff `β` is the GLS
  estimator and `g = G V⁻¹ (y - X β̂)` (`Model.isMMESolution_iff`). We call
  `G V⁻¹ (y - X β̂)` the BLUP (`Model.blup`) as Henderson does; its best-linear-unbiased
  optimality is not proved here.

BOLT-LMM computes a related score-type statistic with `V⁻¹ y` obtained by conjugate gradients
(`MathlibExt.LinearAlgebra.Matrix.ConjugateGradient`) instead of an explicit inverse; its
calibration via LD score regression and its non-infinitesimal (mixture-prior) model are not
covered here (the variational fit of the mixture model is in `BOLTLMMVariational`).

## Main results

* `Model.posDef_V`: `V = σ_g² K + σ_e² I` is positive definite.
* `Model.logLik_le_logLik_gls`, `Model.logLik_eq_logLik_gls_iff`, `Model.logLik_gls`.
* `Model.proj_mul_X`, `Model.proj_mul_V_mul_proj`.
* `Model.profileLogLik_eq_quadratic`, `Model.hasDerivAt_profileLogLik`, `Model.score_eq`,
  `Model.info_pos`.
* `Model.isMMESolution_iff`: Henderson's equations give the GLS estimator and the BLUP.

## References

* P.-R. Loh, G. Tucker, B. K. Bulik-Sullivan, B. J. Vilhjálmsson, H. K. Finucane, R. M. Salem,
  D. I. Chasman, P. M. Ridker, B. M. Neale, B. Berger, N. Patterson, A. L. Price, *Efficient
  Bayesian mixed-model analysis increases association power in large cohorts*, Nat. Genet. 47
  (2015), 284–290.
* C. R. Henderson, *Best linear unbiased estimation and prediction under a selection model*,
  Biometrics 31 (1975), 423–447.
* A. C. Aitken, *On least squares and linear combination of observations*, Proc. Roy. Soc.
  Edinburgh 55 (1936), 42–48 (generalized least squares).
-/

@[expose] public section

open Matrix

namespace MathlibExt.Biology.StatisticalGenetics.BOLTLMM

/-- The variance components of the linear mixed model `y = X β + g + e` with
`g ~ N(0, σ_g² K)` and `e ~ N(0, σ_e² I)` on `n` individuals: a positive semidefinite genetic
relationship matrix `K`, a genetic variance `σ_g² ≥ 0` and an environmental variance
`σ_e² > 0`. -/
structure Model (n : ℕ) where
  /-- The genetic relationship (kinship) matrix. -/
  K : Matrix (Fin n) (Fin n) ℝ
  /-- The genetic variance `σ_g²`. -/
  σg2 : ℝ
  /-- The environmental (residual) variance `σ_e²`. -/
  σe2 : ℝ
  posSemidef_K : K.PosSemidef
  σg2_nonneg : 0 ≤ σg2
  σe2_pos : 0 < σe2

namespace Model

/-- The marginal phenotypic covariance `V = σ_g² K + σ_e² I` of `y = X β + g + e`. -/
noncomputable def V {n : ℕ} (M : Model n) : Matrix (Fin n) (Fin n) ℝ := M.σg2 • M.K + M.σe2 • 1

/-- `V = σ_g² K + σ_e² I` is positive definite. -/
theorem posDef_V {n : ℕ} (M : Model n) : M.V.PosDef :=
  Matrix.PosDef.posSemidef_add (M.posSemidef_K.smul M.σg2_nonneg)
    (Matrix.PosDef.one.smul M.σe2_pos)

/-- The marginal log-likelihood of the mean `μ`: the log of the `N(μ, V)` density at `y`,
`-(n log 2π + log det V + (y - μ)ᵀ V⁻¹ (y - μ)) / 2` (`det V > 0` by `posDef_V`). -/
noncomputable def logLik {n : ℕ} (M : Model n) (y μ : Fin n → ℝ) : ℝ :=
  -(n * Real.log (2 * Real.pi) + Real.log M.V.det + (y - μ) ⬝ᵥ (M.V⁻¹ *ᵥ (y - μ))) / 2

/-- The generalized least-squares estimator `β̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y`. -/
noncomputable def gls {n p : ℕ} (M : Model n) (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) :
    Fin p → ℝ :=
  (Xᵀ * M.V⁻¹ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (M.V⁻¹ *ᵥ y))

/-- The residual-forming matrix `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`. -/
noncomputable def proj {n p : ℕ} (M : Model n) (X : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  M.V⁻¹ - M.V⁻¹ * X * (Xᵀ * M.V⁻¹ * X)⁻¹ * Xᵀ * M.V⁻¹


/-! ### Proof-only algebra -/

private lemma isUnit_det_V {n : ℕ} (M : Model n) : IsUnit M.V.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp M.posDef_V.isUnit

private lemma transpose_V_inv {n : ℕ} (M : Model n) : (M.V⁻¹)ᵀ = M.V⁻¹ := by
  have h := M.posDef_V.inv.isHermitian
  rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

private lemma posDef_S {n p : ℕ} (M : Model n) {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) : (Xᵀ * M.V⁻¹ * X).PosDef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using
    M.posDef_V.inv.conjTranspose_mul_mul_same hX

private lemma isUnit_det_S {n p : ℕ} (M : Model n) {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) : IsUnit (Xᵀ * M.V⁻¹ * X).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (posDef_S M hX).isUnit

private lemma dotProduct_mulVec_comm {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} (hW : Wᵀ = W)
    (a b : Fin n → ℝ) : a ⬝ᵥ (W *ᵥ b) = b ⬝ᵥ (W *ᵥ a) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hW, dotProduct_comm]

private lemma mulVec_dotProduct_mulVec {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) (u : Fin n → ℝ) (d : Fin p → ℝ) :
    (X *ᵥ d) ⬝ᵥ (W *ᵥ u) = d ⬝ᵥ (Xᵀ *ᵥ (W *ᵥ u)) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

/-- The normal equations `Xᵀ V⁻¹ (y - X β̂) = 0`. -/
private lemma normal_eq {n p : ℕ} (M : Model n) {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) (y : Fin n → ℝ) :
    Xᵀ *ᵥ (M.V⁻¹ *ᵥ (y - X *ᵥ M.gls X y)) = 0 := by
  have key : ∀ c : Fin p → ℝ,
      Xᵀ *ᵥ (M.V⁻¹ *ᵥ (X *ᵥ ((Xᵀ * M.V⁻¹ * X)⁻¹ *ᵥ c))) = c := fun c => by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_S M hX),
      one_mulVec]
  rw [mulVec_sub, mulVec_sub, gls, key, sub_self]

/-- `P y = V⁻¹ (y - X β̂)`. -/
private lemma proj_mulVec {n p : ℕ} (M : Model n) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) : M.proj X *ᵥ y = M.V⁻¹ *ᵥ (y - X *ᵥ M.gls X y) := by
  simp only [proj, gls, sub_mulVec, mulVec_sub, ← mulVec_mulVec]

/-- Completing the square: `Q(β) = Q(β̂) + (β - β̂)ᵀ (Xᵀ V⁻¹ X) (β - β̂)`. -/
private lemma quad_eq {n p : ℕ} (M : Model n) {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) (y : Fin n → ℝ) (β : Fin p → ℝ) :
    (y - X *ᵥ β) ⬝ᵥ (M.V⁻¹ *ᵥ (y - X *ᵥ β)) =
      (y - X *ᵥ M.gls X y) ⬝ᵥ (M.V⁻¹ *ᵥ (y - X *ᵥ M.gls X y)) +
        (β - M.gls X y) ⬝ᵥ ((Xᵀ * M.V⁻¹ * X) *ᵥ (β - M.gls X y)) := by
  have key : ∀ (u : Fin n → ℝ) (d : Fin p → ℝ), Xᵀ *ᵥ (M.V⁻¹ *ᵥ u) = 0 →
      (u - X *ᵥ d) ⬝ᵥ (M.V⁻¹ *ᵥ (u - X *ᵥ d)) =
        u ⬝ᵥ (M.V⁻¹ *ᵥ u) + d ⬝ᵥ ((Xᵀ * M.V⁻¹ * X) *ᵥ d) := fun u d hn => by
    have h1 : (X *ᵥ d) ⬝ᵥ (M.V⁻¹ *ᵥ u) = 0 := by
      rw [mulVec_dotProduct_mulVec, hn, dotProduct_zero]
    have h2 : u ⬝ᵥ (M.V⁻¹ *ᵥ (X *ᵥ d)) = 0 := by
      rw [dotProduct_mulVec_comm (transpose_V_inv M), h1]
    have h3 : (X *ᵥ d) ⬝ᵥ (M.V⁻¹ *ᵥ (X *ᵥ d)) = d ⬝ᵥ ((Xᵀ * M.V⁻¹ * X) *ᵥ d) := by
      rw [mulVec_dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
    rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, h1, h2, h3]
    ring
  have hy : y - X *ᵥ β = (y - X *ᵥ M.gls X y) - X *ᵥ (β - M.gls X y) := by
    rw [mulVec_sub]; abel
  rw [hy]
  exact key _ _ (normal_eq M hX y)

/-- The minimal quadratic form is `yᵀ P y`. -/
private lemma quad_gls {n p : ℕ} (M : Model n) {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) (y : Fin n → ℝ) :
    (y - X *ᵥ M.gls X y) ⬝ᵥ (M.V⁻¹ *ᵥ (y - X *ᵥ M.gls X y)) = y ⬝ᵥ (M.proj X *ᵥ y) := by
  rw [proj_mulVec, sub_dotProduct, mulVec_dotProduct_mulVec, normal_eq M hX y, dotProduct_zero,
    sub_zero]

private lemma transpose_proj {n p : ℕ} (M : Model n) (X : Matrix (Fin n) (Fin p) ℝ) :
    (M.proj X)ᵀ = M.proj X := by
  have hV : M.Vᵀ = M.V := by
    have h := M.posDef_V.isHermitian
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  simp only [proj, transpose_sub, transpose_mul, transpose_transpose, transpose_nonsing_inv, hV,
    Matrix.mul_assoc]

private lemma logLik_mulVec {n p : ℕ} (M : Model n) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (β : Fin p → ℝ) :
    M.logLik y (X *ᵥ β) = -(n * Real.log (2 * Real.pi) + Real.log M.V.det +
      (y - X *ᵥ β) ⬝ᵥ (M.V⁻¹ *ᵥ (y - X *ᵥ β))) / 2 := rfl

/-- **GLS maximizes the marginal likelihood**: for `X` of full column rank, every mean `X β`
has marginal log-likelihood at most that of the GLS fit `X β̂`. -/
theorem logLik_le_logLik_gls {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) (y : Fin n → ℝ)
    (β : Fin p → ℝ) : M.logLik y (X *ᵥ β) ≤ M.logLik y (X *ᵥ M.gls X y) := by
  have h := (posDef_S M hX).posSemidef.dotProduct_mulVec_nonneg (β - M.gls X y)
  rw [star_trivial] at h
  rw [logLik_mulVec, logLik_mulVec, quad_eq M hX y β]
  linarith

/-- **The GLS maximizer is unique**: for `X` of full column rank, `X β` attains the maximal
marginal log-likelihood only at `β = β̂`. -/
theorem logLik_eq_logLik_gls_iff {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) (y : Fin n → ℝ)
    (β : Fin p → ℝ) :
    M.logLik y (X *ᵥ β) = M.logLik y (X *ᵥ M.gls X y) ↔ β = M.gls X y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [logLik_mulVec, logLik_mulVec, quad_eq M hX y β] at h
  by_contra hne
  have hpos := (posDef_S M hX).dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
  rw [star_trivial] at hpos
  linarith

/-- The maximal marginal log-likelihood is `-(n log 2π + log det V + yᵀ P y) / 2`. -/
theorem logLik_gls {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) (y : Fin n → ℝ) :
    M.logLik y (X *ᵥ M.gls X y) =
      -(n * Real.log (2 * Real.pi) + Real.log M.V.det + y ⬝ᵥ (M.proj X *ᵥ y)) / 2 := by
  rw [logLik_mulVec, quad_gls M hX y]

/-- `P X = 0`: the residual-forming matrix annihilates the fixed effects. -/
theorem proj_mul_X {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) : M.proj X * X = 0 := by
  have h := isUnit_det_S M hX
  rw [Matrix.mul_assoc] at h
  simp only [proj, Matrix.sub_mul, Matrix.mul_assoc]
  rw [nonsing_inv_mul _ h, Matrix.mul_one, sub_self]

/-- `P V P = P`. With `P X = 0`, this says that under the null model `y = X β + ε` with
`Cov ε = V` the score `xᵀ P y = xᵀ P ε` has variance `xᵀ P V P x = xᵀ P x`. -/
theorem proj_mul_V_mul_proj {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) :
    M.proj X * M.V * M.proj X = M.proj X := by
  have hVW : M.V * M.V⁻¹ = 1 := mul_nonsing_inv _ (isUnit_det_V M)
  have hPX := proj_mul_X (M := M) hX
  have hVH : M.V * (M.V⁻¹ * X * (Xᵀ * M.V⁻¹ * X)⁻¹ * Xᵀ * M.V⁻¹) =
      X * ((Xᵀ * M.V⁻¹ * X)⁻¹ * Xᵀ * M.V⁻¹) := by
    simp only [← Matrix.mul_assoc, hVW, Matrix.one_mul]
  calc M.proj X * M.V * M.proj X
      = M.proj X * (M.V * M.V⁻¹) -
          M.proj X * (M.V * (M.V⁻¹ * X * (Xᵀ * M.V⁻¹ * X)⁻¹ * Xᵀ * M.V⁻¹)) := by
        rw [Matrix.mul_assoc, proj, Matrix.mul_sub, Matrix.mul_sub, ← proj]
    _ = M.proj X := by
        rw [hVW, Matrix.mul_one, hVH, ← Matrix.mul_assoc, hPX, Matrix.zero_mul, sub_zero]

/-- The profile marginal log-likelihood of a SNP effect `γ` for the SNP genotype vector `x`:
`sup_β logLik y (X β + γ x)`. -/
noncomputable def profileLogLik {n p : ℕ} (M : Model n)
    (X : Matrix (Fin n) (Fin p) ℝ) (x y : Fin n → ℝ) (γ : ℝ) : ℝ :=
  ⨆ β : Fin p → ℝ, M.logLik y (X *ᵥ β + γ • x)

/-- The score statistic `(xᵀ P y)² / (xᵀ P x)` for one SNP `x`. Its denominator is positive
when `x` is not in the column space of `X` (`info_pos`); otherwise the statistic is `0` by
the convention `a / 0 = 0` and carries no information. -/
noncomputable def scoreStat {n p : ℕ} (M : Model n) (X : Matrix (Fin n) (Fin p) ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ (M.proj X *ᵥ y)) ^ 2 / (x ⬝ᵥ (M.proj X *ᵥ x))

private lemma profileLogLik_eq {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) (x y : Fin n → ℝ) (γ : ℝ) :
    M.profileLogLik X x y γ = -(n * Real.log (2 * Real.pi) + Real.log M.V.det +
      (y - γ • x) ⬝ᵥ (M.proj X *ᵥ (y - γ • x))) / 2 := by
  have hshift : ∀ β, M.logLik y (X *ᵥ β + γ • x) = M.logLik (y - γ • x) (X *ᵥ β) := fun β => by
    have h : y - (X *ᵥ β + γ • x) = y - γ • x - X *ᵥ β := by abel
    simp only [logLik, h]
  unfold profileLogLik
  simp_rw [hshift]
  rw [← logLik_gls hX]
  exact ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun β => logLik_le_logLik_gls hX _ β)
    (fun w hw => ⟨M.gls X (y - γ • x), hw⟩)

/-- **The profile log-likelihood of a SNP effect is an exact quadratic**:
`ℓ(γ) = ℓ(0) + γ xᵀ P y - γ² xᵀ P x / 2`, so its score at `γ = 0` is `xᵀ P y` and its
information is `xᵀ P x`. -/
theorem profileLogLik_eq_quadratic {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) (x y : Fin n → ℝ)
    (γ : ℝ) :
    M.profileLogLik X x y γ = M.profileLogLik X x y 0 + γ * (x ⬝ᵥ (M.proj X *ᵥ y)) -
      γ ^ 2 / 2 * (x ⬝ᵥ (M.proj X *ᵥ x)) := by
  have hsym : y ⬝ᵥ (M.proj X *ᵥ x) = x ⬝ᵥ (M.proj X *ᵥ y) :=
    dotProduct_mulVec_comm (transpose_proj M X) y x
  rw [profileLogLik_eq hX, profileLogLik_eq hX, zero_smul, sub_zero]
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hsym]
  ring

/-- **The score of a SNP effect** at `γ = 0` is `xᵀ P y`. -/
theorem hasDerivAt_profileLogLik {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) (x y : Fin n → ℝ) :
    HasDerivAt (M.profileLogLik X x y) (x ⬝ᵥ (M.proj X *ᵥ y)) 0 := by
  rw [show M.profileLogLik X x y = fun γ => M.profileLogLik X x y 0 +
      γ * (x ⬝ᵥ (M.proj X *ᵥ y)) - γ ^ 2 / 2 * (x ⬝ᵥ (M.proj X *ᵥ x)) from
    funext (profileLogLik_eq_quadratic hX x y)]
  set B := x ⬝ᵥ (M.proj X *ᵥ y)
  set C := x ⬝ᵥ (M.proj X *ᵥ x)
  have h1 : HasDerivAt (fun γ : ℝ => M.profileLogLik X x y 0 + γ * B) (1 * B) 0 :=
    HasDerivAt.const_add _ (HasDerivAt.mul_const (hasDerivAt_id' 0) B)
  have h2 : HasDerivAt (fun γ : ℝ => γ ^ 2 / 2 * C) ((↑2 * 0 ^ (2 - 1)) / 2 * C) 0 :=
    HasDerivAt.mul_const (HasDerivAt.div_const (hasDerivAt_pow 2 0) 2) C
  refine HasDerivAt.congr_deriv (HasDerivAt.sub h1 h2) ?_
  norm_num

/-- The score is evaluated at the null GLS fit: `xᵀ P y = xᵀ V⁻¹ (y - X β̂)`. -/
theorem score_eq {n p : ℕ} (M : Model n) (X : Matrix (Fin n) (Fin p) ℝ) (x y : Fin n → ℝ) :
    x ⬝ᵥ (M.proj X *ᵥ y) = x ⬝ᵥ (M.V⁻¹ *ᵥ (y - X *ᵥ M.gls X y)) := by
  rw [proj_mulVec]

/-- The information `xᵀ P x` is positive when the SNP `x` is not in the column space of `X`. -/
theorem info_pos {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hX : Function.Injective X.mulVec) {x : Fin n → ℝ}
    (hx : x ∉ Set.range X.mulVec) : 0 < x ⬝ᵥ (M.proj X *ᵥ x) := by
  rw [← quad_gls M hX x]
  have hne : x - X *ᵥ M.gls X x ≠ 0 := fun h => hx ⟨M.gls X x, (sub_eq_zero.mp h).symm⟩
  simpa [star_trivial] using M.posDef_V.inv.dotProduct_mulVec_pos hne

/-- The BLUP `ĝ = G V⁻¹ (y - X β̂)` of the genetic effects, with `G = σ_g² K`
(Henderson 1975). -/
noncomputable def blup {n p : ℕ} (M : Model n) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) : Fin n → ℝ :=
  (M.σg2 • M.K) *ᵥ (M.V⁻¹ *ᵥ (y - X *ᵥ M.gls X y))

/-- `(β, g)` solves Henderson's mixed-model equations with `R = σ_e² I` and `G = σ_g² K`,
i.e. the specialization of `MixedModel.IsMMESolution` to `Z = 1` (every individual has its
own genetic effect), `G = σ_g² K`, `R = σ_e² I`. In unfolded form this is
`Xᵀ R⁻¹ X β + Xᵀ R⁻¹ g = Xᵀ R⁻¹ y` and `R⁻¹ X β + (R⁻¹ + G⁻¹) g = R⁻¹ y`. The equations
are meaningful when `G` is invertible (`isMMESolution_iff`); otherwise `G⁻¹` is Lean's
junk inverse `0`. -/
def IsMMESolution {n p : ℕ} (M : Model n) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (β : Fin p → ℝ) (g : Fin n → ℝ) : Prop :=
  MathlibExt.Biology.StatisticalGenetics.MixedModel.IsMMESolution X 1 (M.σg2 • M.K)
    (M.σe2 • 1) y β g

/-- **Henderson's mixed-model equations give the GLS estimator and the BLUP**: for positive
definite `K`, `σ_g² > 0` and `X` of full column rank, `(β, g)` solves the mixed-model equations
iff `β = β̂` and `g = σ_g² K V⁻¹ (y - X β̂)`. This is the specialization of
`MixedModel.isMMESolution_iff_gls` to `Z = 1`, `G = σ_g² K`, `R = σ_e² I`; the generic
theorem gives `β = glsMatrix X V *ᵥ y` and `g = G V⁻¹ (y - X β̂)`, which are `Model.gls`
and `Model.blup` by the two conversion lemmas below. -/
theorem isMMESolution_iff {n p : ℕ} {M : Model n} {X : Matrix (Fin n) (Fin p) ℝ}
    (hK : M.K.PosDef) (hg : 0 < M.σg2) (hX : Function.Injective X.mulVec)
    (y : Fin n → ℝ) (β : Fin p → ℝ) (g : Fin n → ℝ) :
    M.IsMMESolution X y β g ↔ β = M.gls X y ∧ g = M.blup X y := by
  have hG : (M.σg2 • M.K).PosDef := hK.smul hg
  have hR : (M.σe2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    Matrix.PosDef.one.smul M.σe2_pos
  have hV : MathlibExt.Biology.StatisticalGenetics.MixedModel.phenCov
      (1 : Matrix (Fin n) (Fin n) ℝ) (M.σg2 • M.K) (M.σe2 • 1) = M.V := by
    simp [MathlibExt.Biology.StatisticalGenetics.MixedModel.phenCov, V,
      Matrix.transpose_one]
  have hX' : IsUnit (Xᵀ *
      (MathlibExt.Biology.StatisticalGenetics.MixedModel.phenCov
        (1 : Matrix (Fin n) (Fin n) ℝ) (M.σg2 • M.K) (M.σe2 • 1))⁻¹ * X) := by
    rw [hV]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_S M hX)
  have hgen := MathlibExt.Biology.StatisticalGenetics.MixedModel.isMMESolution_iff_gls
    (X := X) (Z := (1 : Matrix (Fin n) (Fin n) ℝ)) (G := M.σg2 • M.K)
    (R := M.σe2 • 1) hG hR hX' y β g
  rw [hV] at hgen
  have hgls : MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix X M.V *ᵥ y =
      M.gls X y := by
    simp [MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix, gls,
      Matrix.mulVec_mulVec]
  have hblup : ((M.σg2 • M.K) * (1 : Matrix (Fin n) (Fin n) ℝ)ᵀ * M.V⁻¹) *ᵥ
      (y - X *ᵥ M.gls X y) = M.blup X y := by
    simp [blup, Matrix.mulVec_mulVec, Matrix.transpose_one]
  show MathlibExt.Biology.StatisticalGenetics.MixedModel.IsMMESolution X 1 (M.σg2 • M.K)
      (M.σe2 • 1) y β g ↔ β = M.gls X y ∧ g = M.blup X y
  rw [hgen]
  constructor
  · rintro ⟨hβ, hg'⟩
    rw [hgls] at hβ
    refine ⟨hβ, ?_⟩
    rw [hβ] at hg'
    rw [hg', hblup]
  · rintro ⟨hβ, hg'⟩
    refine ⟨?_, ?_⟩
    · rw [hβ, hgls]
    · rw [hg', hβ, hblup]

end Model

end MathlibExt.Biology.StatisticalGenetics.BOLTLMM
