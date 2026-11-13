/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Filter.Extr
public import MathlibExt.Analysis.Calculus.DotProductGradient
public import MathlibExt.Probability.Distributions.NegativeBinomial
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Negative binomial regression with a log link and fixed shape

The response law is `negBinomialReal θ μ` from
`MathlibExt.Probability.Distributions.NegativeBinomial`: size (shape) `θ > 0` and mean `μ ≥ 0`,

`NB(k; θ, μ) = θ⁽ᵏ⁾ / k! · (θ / (θ + μ)) ^ θ · (μ / (θ + μ)) ^ k`,

with variance `μ + μ² / θ`; it is the canonical `p`-parametrization at `p = θ / (θ + μ)`
(`negBinomialReal_eq_negBinomialPMF`). This file keeps the name `θ` for the shape, as in that
file. The regression uses the log link: observation `i` has mean `μᵢ = exp ηᵢ` with linear
predictor `ηᵢ = (X β)ᵢ + oᵢ` for a design `X : Matrix ι κ ℝ` and an offset `o` that is held fixed.
The shape `θ` is a known constant throughout; estimating it is out of scope.

## The kernel

`log_negBinomialReal_exp`: for a count `y` and `μ = exp η`,

`log NB(y; θ, e^η) = log (θ⁽ʸ⁾ / y!) + θ log θ + (y η - (y + θ) log (θ + e^η))`,

so the part depending on `η` (hence on `β`) is exactly
`nbKernel θ y η = y η - (y + θ) log (θ + e^η)`.
The kernel and all results about it are stated for real responses `y`; the counts are `y ≥ 0`.

## Main results

* `hasDerivAt_nbKernel`: `∂ℓ/∂η = θ (y - μ) / (θ + μ)` (`nbScore`).
* `hasDerivAt_nbScore`: `∂²ℓ/∂η² = -θ (y + θ) μ / (θ + μ)²`, i.e. minus the observed weight
  `nbObsWeight`. The observed weight depends on `y`; `nbObsWeight_pos` needs `y > -θ`, which counts
  satisfy.
* `hasSum_nbObsWeight_mul_negBinomialReal`: under `y ~ NB(θ, μ)` the observed weight has mean the
  expected (Fisher) weight `nbFisherWeight θ η = θ μ / (θ + μ)`;
  `hasSum_nbScore_mul_negBinomialReal`: the score has mean `0`.
* In the mean parametrization (`nbKernelMean`, `hasDerivAt_nbKernelMean`,
  `hasDerivAt_nbKernelMean_deriv`) the second derivative is `-y / μ² + (y + θ) / (θ + μ)²`, which is
  positive at `y = 0`: concavity is a property of the log link, not of the mean scale.
* `hasFDerivAt_nbLogLik`, `hasGradientAt_nbLogLik`: the gradient of
  `ℓ(β) = ∑ᵢ nbKernel θ yᵢ ηᵢ(β)` is `Xᵀ s(β)` with `sᵢ = θ (yᵢ - μᵢ) / (θ + μᵢ)` (`nbGradient`).
* `hasDerivAt_nbGradient_dotProduct`: the Hessian quadratic form is
  `-∑ᵢ wᵢ ((X u)ᵢ)²` with the observed weights `wᵢ = nbObsWeight θ yᵢ ηᵢ`.
* `concaveOn_nbLogLik`: for `θ > 0` and counts `yᵢ ≥ 0`, `ℓ` is concave on all of `κ → ℝ`;
  `nbLogLik_maximizer_unique`: with `X` injective (`mulVec_injective_of_isUnit_gram`: e.g. an
  invertible Gram matrix `Xᵀ X`) there is at most one maximizer. Existence is not claimed.
* `nbLogLik_zero_not_isMaxOn`: with all counts zero and a nonnegative, nonzero design column (such
  as an intercept) the score equation has no root and `ℓ` has no maximizer.

The Poisson limit `θ → ∞` is not treated.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM.NegativeBinomial

open Finset Real Matrix ProbabilityTheory
open scoped Nat

/-! ### The scalar kernel in the linear predictor -/

/-- The `η`-dependent part of the negative binomial log mass function under the log link,
`y η - (y + θ) log (θ + e^η)`, for shape `θ`, response `y` and linear predictor `η` (mean
`μ = e^η`). See `log_negBinomialReal_exp`. -/
noncomputable def nbKernel (θ y η : ℝ) : ℝ := y * η - (y + θ) * log (θ + exp η)

/-- The score of one observation with respect to the linear predictor,
`∂ nbKernel / ∂η = θ (y - μ) / (θ + μ)` with `μ = e^η`. -/
noncomputable def nbScore (θ y η : ℝ) : ℝ := θ * (y - exp η) / (θ + exp η)

/-- The observed-information weight of one observation, `-∂² nbKernel / ∂η²
= θ (y + θ) μ / (θ + μ)²` with `μ = e^η`. It depends on the response `y`. -/
noncomputable def nbObsWeight (θ y η : ℝ) : ℝ := θ * (y + θ) * exp η / (θ + exp η) ^ 2

/-- The expected (Fisher) information weight of one observation, `θ μ / (θ + μ)` with
`μ = e^η`: the mean of `nbObsWeight` under `y ~ NB(θ, μ)`
(`hasSum_nbObsWeight_mul_negBinomialReal`). -/
noncomputable def nbFisherWeight (θ η : ℝ) : ℝ := θ * exp η / (θ + exp η)

private lemma add_exp_pos {θ : ℝ} (hθ : 0 < θ) (η : ℝ) : 0 < θ + exp η := by positivity

/-- **The score.** For `θ > 0`, `∂/∂η (y η - (y + θ) log (θ + e^η)) = θ (y - e^η) / (θ + e^η)`. -/
theorem hasDerivAt_nbKernel {θ : ℝ} (hθ : 0 < θ) (y η : ℝ) :
    HasDerivAt (nbKernel θ y) (nbScore θ y η) η := by
  have hpos := add_exp_pos hθ η
  have hlog : HasDerivAt (fun η => log (θ + exp η)) (exp η / (θ + exp η)) η :=
    ((hasDerivAt_exp η).const_add θ).log hpos.ne'
  convert ((hasDerivAt_id η).const_mul y).fun_sub (hlog.const_mul (y + θ)) using 1
  · funext x; simp [nbKernel]
  unfold nbScore
  field_simp
  ring

/-- **The observed second derivative.** For `θ > 0`, the derivative of the score in `η` is
`-θ (y + θ) e^η / (θ + e^η)²`. -/
theorem hasDerivAt_nbScore {θ : ℝ} (hθ : 0 < θ) (y η : ℝ) :
    HasDerivAt (nbScore θ y) (-nbObsWeight θ y η) η := by
  have hpos := add_exp_pos hθ η
  convert (((hasDerivAt_exp η).const_sub y).const_mul θ).fun_div
    ((hasDerivAt_exp η).const_add θ) hpos.ne' using 1
  · rfl
  unfold nbObsWeight
  field_simp
  ring

/-- The observed weight is positive for `θ > 0` and `y > -θ`, in particular for every count
`y ≥ 0`. -/
theorem nbObsWeight_pos {θ y : ℝ} (hθ : 0 < θ) (hy : -θ < y) (η : ℝ) : 0 < nbObsWeight θ y η := by
  have : 0 < y + θ := by linarith
  unfold nbObsWeight
  positivity

/-- The Fisher weight is positive for `θ > 0`. -/
theorem nbFisherWeight_pos {θ : ℝ} (hθ : 0 < θ) (η : ℝ) : 0 < nbFisherWeight θ η := by
  unfold nbFisherWeight
  positivity

/-- **The kernel is the log mass function up to a `β`-free constant.** For `θ > 0` and a count
`k`, `log NB(k; θ, e^η) = log (θ⁽ᵏ⁾ / k!) + θ log θ + nbKernel θ k η`. -/
theorem log_negBinomialReal_exp {θ : ℝ} (hθ : 0 < θ) (η : ℝ) (k : ℕ) :
    log (negBinomialReal θ (exp η) k) =
      log ((ascPochhammer ℝ k).eval θ / k !) + θ * log θ + nbKernel θ k η := by
  have hpos := add_exp_pos hθ η
  have hA : 0 < (ascPochhammer ℝ k).eval θ / k ! := by
    have := ascPochhammer_pos k θ hθ
    positivity
  have hp : 0 < θ / (θ + exp η) := div_pos hθ hpos
  have hq : 0 < exp η / (θ + exp η) := div_pos (exp_pos η) hpos
  unfold negBinomialReal nbKernel
  rw [log_mul (by positivity) (by positivity), log_mul hA.ne' (by positivity), log_rpow hp,
    log_pow, log_div hθ.ne' hpos.ne', log_div (exp_pos η).ne' hpos.ne', log_exp]
  ring

/-! ### Expected information -/

/-- **The score has mean zero.** For `θ > 0`, `∑ₖ nbScore θ k η · NB(k; θ, e^η) = 0`. -/
theorem hasSum_nbScore_mul_negBinomialReal {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    HasSum (fun k : ℕ => nbScore θ k η * negBinomialReal θ (exp η) k) 0 := by
  have hμ := (exp_pos η).le
  have hpos := add_exp_pos hθ η
  have h := ((hasSum_mul_negBinomialReal hθ hμ).mul_left (θ / (θ + exp η))).add
    ((hasSum_negBinomialReal hθ hμ).mul_left (-(θ * exp η / (θ + exp η))))
  convert h using 1
  · funext k
    unfold nbScore
    field_simp
    ring
  · field_simp
    ring

/-- **Expected information.** For `θ > 0`, the observed weight averaged over `y ~ NB(θ, e^η)` is
the Fisher weight: `∑ₖ nbObsWeight θ k η · NB(k; θ, e^η) = θ e^η / (θ + e^η)`. -/
theorem hasSum_nbObsWeight_mul_negBinomialReal {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    HasSum (fun k : ℕ => nbObsWeight θ k η * negBinomialReal θ (exp η) k)
      (nbFisherWeight θ η) := by
  have hμ := (exp_pos η).le
  have hpos := add_exp_pos hθ η
  set c := θ * exp η / (θ + exp η) ^ 2
  have h := ((hasSum_mul_negBinomialReal hθ hμ).mul_left c).add
    ((hasSum_negBinomialReal hθ hμ).mul_left (c * θ))
  convert h using 1
  · funext k
    unfold nbObsWeight
    simp only [c]
    field_simp
  · unfold nbFisherWeight
    simp only [c]
    field_simp
    ring

/-! ### The mean scale -/

/-- The kernel as a function of the mean `μ`: `y log μ - (y + θ) log (θ + μ)`. -/
noncomputable def nbKernelMean (θ y μ : ℝ) : ℝ := y * log μ - (y + θ) * log (θ + μ)

/-- The log-link kernel is the mean-scale kernel at `μ = e^η`. -/
theorem nbKernel_eq_nbKernelMean (θ y η : ℝ) : nbKernel θ y η = nbKernelMean θ y (exp η) := by
  simp [nbKernel, nbKernelMean, log_exp]

/-- The mean-scale score: for `θ > 0` and `μ > 0`,
`∂/∂μ (y log μ - (y + θ) log (θ + μ)) = θ (y - μ) / (μ (θ + μ))`. -/
theorem hasDerivAt_nbKernelMean {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 < μ) (y : ℝ) :
    HasDerivAt (nbKernelMean θ y) (θ * (y - μ) / (μ * (θ + μ))) μ := by
  have hpos : 0 < θ + μ := by linarith
  convert ((hasDerivAt_log hμ.ne').const_mul y).fun_sub
    ((((hasDerivAt_id μ).const_add θ).log hpos.ne').const_mul (y + θ)) using 1
  · funext x; simp [nbKernelMean]
  · simp only [id_eq]
    field_simp
    ring

/-- The mean-scale second derivative: for `θ > 0` and `μ > 0`, the derivative of
`θ (y - μ) / (μ (θ + μ))` is `-y / μ² + (y + θ) / (θ + μ)²`. Unlike the log-link second derivative
`-nbObsWeight θ y η` it is not sign-definite: it is positive at `y = 0`. -/
theorem hasDerivAt_nbKernelMean_deriv {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 < μ) (y : ℝ) :
    HasDerivAt (fun μ => θ * (y - μ) / (μ * (θ + μ))) (-y / μ ^ 2 + (y + θ) / (θ + μ) ^ 2) μ := by
  have hpos : 0 < θ + μ := by linarith
  have hd : μ * (θ + μ) ≠ 0 := by positivity
  convert ((hasDerivAt_id' (x := μ)).const_sub y |>.const_mul θ).fun_div
    ((hasDerivAt_id' (x := μ)).fun_mul ((hasDerivAt_id' (x := μ)).const_add θ)) hd using 1
  field_simp
  ring

/-- **The log link is what makes the kernel concave.** For `θ > 0` and the count `y = 0`, the
mean-scale kernel `μ ↦ -θ log (θ + μ)` is not concave on `μ > 0`. -/
theorem not_concaveOn_nbKernelMean_zero {θ : ℝ} (hθ : 0 < θ) :
    ¬ ConcaveOn ℝ (Set.Ioi 0) (nbKernelMean θ 0) := by
  intro h
  have h1 := h.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have h2 := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 (by linarith : (0 : ℝ) < θ + 1))
    (Set.mem_Ioi.2 (by linarith : (0 : ℝ) < θ + 2)) (by intro h; linarith)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  simp only [nbKernelMean, smul_eq_mul, zero_mul, zero_add, zero_sub] at h1 h2
  have h3 : 1 / 2 * (θ + 1) + 1 / 2 * (θ + 2) = θ + (1 / 2 * 1 + 1 / 2 * 2) := by ring
  rw [h3] at h2
  nlinarith

/-! ### Strict concavity of the scalar kernel -/

/-- **The log-link kernel is strictly concave** in `η` for `θ > 0` and `y > -θ` (every count
`y ≥ 0`): its derivative `nbScore θ y` is strictly decreasing, with derivative
`-nbObsWeight θ y η < 0`. -/
theorem strictConcaveOn_nbKernel {θ y : ℝ} (hθ : 0 < θ) (hy : -θ < y) :
    StrictConcaveOn ℝ Set.univ (nbKernel θ y) := by
  have hd : deriv (nbKernel θ y) = nbScore θ y :=
    funext fun η => (hasDerivAt_nbKernel hθ y η).deriv
  have hs : StrictAnti (nbScore θ y) := strictAnti_of_deriv_neg fun η => by
    rw [(hasDerivAt_nbScore hθ y η).deriv]
    exact neg_lt_zero.2 (nbObsWeight_pos hθ hy η)
  refine StrictAntiOn.strictConcaveOn_of_deriv convex_univ
    (fun η _ => (hasDerivAt_nbKernel hθ y η).continuousAt.continuousWithinAt) ?_
  rw [interior_univ, hd]
  exact hs.strictAntiOn _

/-! ### The regression log-likelihood -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The negative binomial log-link log-likelihood in `β`, up to the `β`-free constant
`∑ᵢ (log (θ⁽ʸⁱ⁾ / yᵢ!) + θ log θ)` (`log_negBinomialReal_exp`): `∑ᵢ nbKernel θ yᵢ ηᵢ` with linear
predictor `ηᵢ = (X β)ᵢ + oᵢ`, known shape `θ`, design `X`, fixed offset `o` and responses `y`. -/
noncomputable def nbLogLik (θ : ℝ) (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) : ℝ :=
  ∑ i, nbKernel θ (y i) ((X *ᵥ β) i + o i)

/-- The score vector `Xᵀ s` with `sᵢ = θ (yᵢ - μᵢ) / (θ + μᵢ)` and `μᵢ = exp ((X β)ᵢ + oᵢ)`. -/
noncomputable def nbGradient (θ : ℝ) (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) : κ → ℝ :=
  Xᵀ *ᵥ fun i => nbScore θ (y i) ((X *ᵥ β) i + o i)

/-- Component `j` of the score vector is `∑ᵢ X i j · sᵢ`. -/
theorem nbGradient_apply (θ : ℝ) (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) (j : κ) :
    nbGradient θ X o y β j = ∑ i, X i j * nbScore θ (y i) ((X *ᵥ β) i + o i) := by
  simp [nbGradient, mulVec, dotProduct]

omit [Fintype ι] in
private lemma hasFDerivAt_predictor (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) (i : ι) :
    HasFDerivAt (fun β => (X *ᵥ β) i + o i) (Real.dotL (X i)) β := by
  have h : (fun β : κ → ℝ => (X *ᵥ β) i + o i) = fun β => β ⬝ᵥ X i + o i := by
    funext β
    simp [mulVec, dotProduct_comm]
  rw [h]
  exact (Real.hasFDerivAt_dotProduct (X i) β).add_const (o i)

/-- **The score vector.** For `θ > 0`, the Fréchet derivative of the log-likelihood at `β` is
`v ↦ ⟪v, Xᵀ s(β)⟫` (`Real.dotL`). -/
theorem hasFDerivAt_nbLogLik {θ : ℝ} (hθ : 0 < θ) (X : Matrix ι κ ℝ) (o y : ι → ℝ)
    (β : κ → ℝ) : HasFDerivAt (nbLogLik θ X o y) (Real.dotL (nbGradient θ X o y β)) β := by
  have h : HasFDerivAt (nbLogLik θ X o y)
      (∑ i, nbScore θ (y i) ((X *ᵥ β) i + o i) • Real.dotL (X i)) β := by
    unfold nbLogLik
    exact HasFDerivAt.fun_sum fun i _ =>
      (hasDerivAt_nbKernel hθ (y i) _).comp_hasFDerivAt β (hasFDerivAt_predictor X o β i)
  convert h using 1
  ext v
  simp only [nbGradient, Real.dotL_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, dotProduct, mulVec, transpose_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

/-- **The score vector is the gradient** of the log-likelihood transported to
`EuclideanSpace ℝ κ`. -/
theorem hasGradientAt_nbLogLik {θ : ℝ} (hθ : 0 < θ) (X : Matrix ι κ ℝ) (o y : ι → ℝ)
    (β : κ → ℝ) :
    HasGradientAt (fun b : EuclideanSpace ℝ κ => nbLogLik θ X o y b.ofLp)
      (WithLp.toLp 2 (nbGradient θ X o y β)) (WithLp.toLp 2 β) :=
  Real.hasGradientAt_ofLp (hasFDerivAt_nbLogLik hθ X o y β)

/-- **The Hessian quadratic form.** For `θ > 0`, the derivative at `t = 0` of
`t ↦ ⟪Xᵀ s(β + t u), u⟫` is `-∑ᵢ wᵢ ((X u)ᵢ)²` with the observed weights
`wᵢ = nbObsWeight θ yᵢ ηᵢ(β)`. -/
theorem hasDerivAt_nbGradient_dotProduct {θ : ℝ} (hθ : 0 < θ) (X : Matrix ι κ ℝ)
    (o y : ι → ℝ) (β u : κ → ℝ) :
    HasDerivAt (fun t : ℝ => nbGradient θ X o y (β + t • u) ⬝ᵥ u)
      (-∑ i, nbObsWeight θ (y i) ((X *ᵥ β) i + o i) * (X *ᵥ u) i ^ 2) 0 := by
  have hfun : (fun t : ℝ => nbGradient θ X o y (β + t • u) ⬝ᵥ u) = fun t => ∑ i,
      nbScore θ (y i) ((X *ᵥ β) i + o i + t * (X *ᵥ u) i) * (X *ᵥ u) i := by
    funext t
    rw [nbGradient, dotProduct_comm, dotProduct_transpose_mulVec]
    simp only [dotProduct, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_congr rfl fun i _ => by ring_nf
  rw [hfun, ← sum_neg_distrib]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hline := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const ((X *ᵥ u) i)).const_add
    ((X *ᵥ β) i + o i)
  rw [one_mul] at hline
  have hs := (hasDerivAt_nbScore hθ (y i) ((X *ᵥ β) i + o i + 0 * (X *ᵥ u) i)).comp 0 hline
  convert hs.mul_const ((X *ᵥ u) i) using 1
  · rfl
  · simp only [zero_mul, add_zero]
    ring

omit [Fintype ι] in
private lemma predictor_combo (X : Matrix ι κ ℝ) (o : ι → ℝ) (β γ : κ → ℝ) {a b : ℝ}
    (hab : a + b = 1) (i : ι) :
    (X *ᵥ (a • β + b • γ)) i + o i = a * ((X *ᵥ β) i + o i) + b * ((X *ᵥ γ) i + o i) := by
  simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(o i)) * hab

/-- **Concavity.** For known shape `θ > 0` and count responses `yᵢ ≥ 0`, the negative binomial
log-link log-likelihood is concave on all of `κ → ℝ`. -/
theorem concaveOn_nbLogLik {θ : ℝ} (hθ : 0 < θ) (X : Matrix ι κ ℝ) (o : ι → ℝ) {y : ι → ℝ}
    (hy : ∀ i, 0 ≤ y i) : ConcaveOn ℝ Set.univ (nbLogLik θ X o y) := by
  refine ⟨convex_univ, fun β _ γ _ a b ha hb hab => ?_⟩
  simp only [nbLogLik, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [predictor_combo X o β γ hab i]
  have := (strictConcaveOn_nbKernel hθ (by linarith [hy i] : -θ < y i)).concaveOn.2
    (Set.mem_univ ((X *ᵥ β) i + o i)) (Set.mem_univ ((X *ᵥ γ) i + o i)) ha hb hab
  simpa only [smul_eq_mul] using this

/-- **At most one maximizer.** For known shape `θ > 0`, count responses `yᵢ ≥ 0` and an injective
design (`X β = X γ → β = γ`), the log-likelihood has at most one maximizer on `κ → ℝ`. Existence is
not claimed: see `nbLogLik_zero_not_isMaxOn`. -/
theorem nbLogLik_maximizer_unique {θ : ℝ} (hθ : 0 < θ) {X : Matrix ι κ ℝ}
    (hinj : Function.Injective X.mulVec) (o : ι → ℝ) {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i)
    {β₁ β₂ : κ → ℝ} (h₁ : IsMaxOn (nbLogLik θ X o y) Set.univ β₁)
    (h₂ : IsMaxOn (nbLogLik θ X o y) Set.univ β₂) : β₁ = β₂ := by
  by_contra hne
  have hX : X *ᵥ β₁ ≠ X *ᵥ β₂ := fun h => hne (hinj h)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hX
  have hyθ : ∀ i, -θ < y i := fun i => by linarith [hy i]
  have hab : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  set m := (1 / 2 : ℝ) • β₁ + (1 / 2 : ℝ) • β₂
  have hlt : 1 / 2 * nbLogLik θ X o y β₁ + 1 / 2 * nbLogLik θ X o y β₂ <
      nbLogLik θ X o y m := by
    simp only [nbLogLik, mul_sum, ← sum_add_distrib, m]
    refine sum_lt_sum (fun i _ => ?_) ⟨j, mem_univ j, ?_⟩
    · rw [predictor_combo X o β₁ β₂ hab i]
      have := (strictConcaveOn_nbKernel hθ (hyθ i)).concaveOn.2
        (Set.mem_univ ((X *ᵥ β₁) i + o i)) (Set.mem_univ ((X *ᵥ β₂) i + o i))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) hab
      simpa only [smul_eq_mul] using this
    · rw [predictor_combo X o β₁ β₂ hab j]
      have := (strictConcaveOn_nbKernel hθ (hyθ j)).2 (Set.mem_univ ((X *ᵥ β₁) j + o j))
        (Set.mem_univ ((X *ᵥ β₂) j + o j)) (fun h => hj (add_right_cancel h))
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) hab
      simpa only [smul_eq_mul] using this
  have e1 := isMaxOn_iff.1 h₁ m (Set.mem_univ _)
  have e2 := isMaxOn_iff.1 h₂ m (Set.mem_univ _)
  linarith

/-- An invertible Gram matrix `Xᵀ X` makes the design injective, so
`nbLogLik_maximizer_unique` applies. -/
theorem mulVec_injective_of_isUnit_gram [DecidableEq κ] {X : Matrix ι κ ℝ}
    (h : IsUnit (Xᵀ * X)) : Function.Injective X.mulVec := by
  intro v w hvw
  apply mulVec_injective_of_isUnit h
  simp only [← mulVec_mulVec, hvw]

/-! ### All-zero counts -/

/-- With count `y = 0` the score is negative at every `η`: `θ (0 - μ) / (θ + μ) < 0`. -/
theorem nbScore_zero_neg {θ : ℝ} (hθ : 0 < θ) (η : ℝ) : nbScore θ 0 η < 0 := by
  unfold nbScore
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hθ (by linarith [exp_pos η]))
    (add_exp_pos hθ η)

/-- **No root of the score equation for all-zero counts.** If every count is `0` and the design
has a column `j` with nonnegative entries, not all zero (for example an intercept), then component
`j` of the score vector is negative at every `β`. -/
theorem nbGradient_zero_neg {θ : ℝ} (hθ : 0 < θ) {X : Matrix ι κ ℝ} (j : κ)
    (hX0 : ∀ i, 0 ≤ X i j) (hX : ∃ i, 0 < X i j) (o : ι → ℝ) (β : κ → ℝ) :
    nbGradient θ X o 0 β j < 0 := by
  rw [nbGradient_apply]
  obtain ⟨i₀, hi₀⟩ := hX
  calc ∑ i, X i j * nbScore θ ((0 : ι → ℝ) i) ((X *ᵥ β) i + o i) < ∑ _i : ι, (0 : ℝ) :=
        sum_lt_sum (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hX0 i) (nbScore_zero_neg hθ _).le)
          ⟨i₀, mem_univ _, mul_neg_of_pos_of_neg hi₀ (nbScore_zero_neg hθ _)⟩
    _ = 0 := by simp

/-- **No maximizer for all-zero counts.** Under the hypotheses of `nbGradient_zero_neg` the
log-likelihood has no maximizer: a maximizer would be a critical point. -/
theorem nbLogLik_zero_not_isMaxOn {θ : ℝ} (hθ : 0 < θ) {X : Matrix ι κ ℝ} (j : κ)
    (hX0 : ∀ i, 0 ≤ X i j) (hX : ∃ i, 0 < X i j) (o : ι → ℝ) (β : κ → ℝ) :
    ¬ IsMaxOn (nbLogLik θ X o 0) Set.univ β := by
  classical
  intro h
  have h0 := (h.isLocalMax Filter.univ_mem).hasFDerivAt_eq_zero (hasFDerivAt_nbLogLik hθ X o 0 β)
  have := congrArg (fun L => L (Pi.single j 1)) h0
  simp only [Real.dotL_apply, single_dotProduct, one_mul, _root_.zero_apply] at this
  exact (nbGradient_zero_neg hθ j hX0 hX o β).ne this

end MathlibExt.Probability.Statistics.GLM.NegativeBinomial
