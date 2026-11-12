/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.NegativeBinomial
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Negative binomial regression with an estimated shape

`MathlibExt.Probability.Statistics.GLM.NegativeBinomial` treats the log-link negative binomial
regression `yᵢ ~ NB(θ, μᵢ)`, `μᵢ = exp ((X β)ᵢ + oᵢ)`, with the shape (size) `θ` known. This file
estimates `θ` jointly with `β`. The shape is called `θ` as in `negBinomialReal`; it is the `k` of
the NB2 variance `μ + μ² / k` (the dispersion is `1 / θ`).

## Joint score and information of one count

* `nbLogPmf θ y η` is the full log mass function, shape terms included;
  `log_negBinomialReal_exp_eq_nbLogPmf` identifies it with `log NB(y; θ, e^η)`.
* `hasFDerivAt_nbLogPmf`: the joint score in `(θ, η)` is `(nbShapeScore, nbScore)`, with
  `nbShapeScore θ y η = ∑_{j<y} 1 / (θ + j) + log θ + 1 - log (θ + μ) - (y + θ) / (θ + μ)`.
* `hasFDerivAt_nbScore_prod`, `hasFDerivAt_nbShapeScore`: the Hessian in `(θ, η)` is
  `[[-nbShapeObsInfo, nbCross], [nbCross, -nbObsWeight]]` with mixed partial
  `nbCross θ y η = (y - μ) μ / (θ + μ)²`.
* `hasSum_nbCross_mul_negBinomialReal`: the mixed partial has mean zero, so `β` and `θ` are
  orthogonal. `hasSum_nbShapeObsInfo_mul_negBinomialReal`: the observed shape information has mean
  `nbShapeFisherInfo θ η` (a trigamma series, no closed form).
* `nbObsInfoRow`, `nbFisherInfoRow`, `hasSum_nbObsInfoRow`: the observed information of one count
  as a matrix over `κ ⊕ Unit` (coefficients, then the shape) has mean the block-diagonal Fisher
  information.

## The regression

* `nbJointLogLik`, `hasFDerivAt_nbJointLogLik`: the joint score is the fixed-shape score vector
  `nbGradient` in the `β`-block and `nbJointShapeScore` in the `θ`-block.
* `nbJointObsInfo`, `hasDerivAt_nbJointScore_line`: the second derivative of the log-likelihood
  along any direction `d` is `-dᵀ J d`, so `J` is the observed information.
  `nbObsInfoRow_quadratic` expands `dᵀ J d`.
* `nbJointFisherInfo_eq_fromBlocks`: the joint Fisher information is
  `[[Xᵀ diag(F) X, 0], [0, ∑ᵢ nbShapeFisherInfo θ ηᵢ]]`.
* `inv_nbJointFisherInfo`, `toBlocks₁₁_inv_nbJointFisherInfo`: the `β`-block of its inverse is
  `(Xᵀ diag(F) X)⁻¹`, the known-shape value. Estimating `θ` does not change the information-based
  covariance of `β̂`. `tendstoInMeasure_nbFisherWeight_plugIn`: the plug-in Fisher weights at a
  consistent `(β̂, θ̂)` are consistent.

## Consistency

`tendstoInMeasure_nbJointMLE`: a near-maximizer of the averaged joint log-likelihood
`nbAvgLogLik` over a compact set `K` converges in probability to `p₀`. The hypotheses are explicit:
`M` is continuous on `K`, `p₀` is its unique maximizer on `K` (identifiability), and the uniform law
of large numbers holds on `K` in probability. `tendstoInMeasure_snd_of_nbJointMLE`: the estimated
shape is consistent.

## Not proved here

* None of the consistency hypotheses is derived from a sampling model: there is no uniform LLN
  for `nbLogPmf` over compacts, and no proof that the expected log-likelihood is uniquely maximized
  at the true parameter.
* Positivity of `nbShapeFisherInfo` (`E[(∂_θ ℓ)²] > 0`) is not proved. It needs the Bartlett
  identity `E ∂_θ ℓ = 0`, which needs differentiation under the series. `inv_nbJointFisherInfo`
  therefore assumes that the total shape information is nonzero.
* Asymptotic normality of `(β̂, θ̂)`, and plug-in Wald inference with the estimated joint
  information, are not proved. The block-diagonal form shows only that the `β`-block of the
  inverse Fisher information is unchanged.
* The joint log-likelihood is not concave in `(β, θ)`: the observed shape information can be
  negative (at `θ = 1`, `y = 0`, `μ = 1` it is `-1/4`). So no uniqueness or existence of the joint
  maximizer is claimed.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM.NegativeBinomial

open Finset Real Matrix ProbabilityTheory MeasureTheory Filter Topology
open scoped Nat

/-! ### The full log mass function in `(θ, η)` -/

/-- The full negative binomial log mass function of a count `y` under the log link, as a function
of the shape `θ` and the linear predictor `η` (mean `μ = e^η`):
`∑_{j<y} log (θ + j) - log y! + θ log θ + nbKernel θ y η`. For `θ > 0` it is
`log NB(y; θ, e^η)` (`log_negBinomialReal_exp_eq_nbLogPmf`). -/
noncomputable def nbLogPmf (θ : ℝ) (y : ℕ) (η : ℝ) : ℝ :=
  ∑ j ∈ range y, log (θ + j) - log (y ! : ℝ) + θ * log θ + nbKernel θ y η

/-- The score of one count with respect to the shape,
`∂ nbLogPmf / ∂θ = ∑_{j<y} 1 / (θ + j) + log θ + 1 - log (θ + μ) - (y + θ) / (θ + μ)`
with `μ = e^η`. -/
noncomputable def nbShapeScore (θ : ℝ) (y : ℕ) (η : ℝ) : ℝ :=
  ∑ j ∈ range y, (θ + j)⁻¹ + log θ + 1 - log (θ + exp η) - (y + θ) / (θ + exp η)

/-- The mixed second derivative of the log mass function,
`∂² nbLogPmf / ∂θ ∂η = (y - μ) μ / (θ + μ)²` with `μ = e^η`. -/
noncomputable def nbCross (θ y η : ℝ) : ℝ := (y - exp η) * exp η / (θ + exp η) ^ 2

/-- The observed shape information of one count, `-∂² nbLogPmf / ∂θ²
= ∑_{j<y} 1 / (θ + j)² - 1 / θ + 1 / (θ + μ) - (y - μ) / (θ + μ)²` with `μ = e^η`. -/
noncomputable def nbShapeObsInfo (θ : ℝ) (y : ℕ) (η : ℝ) : ℝ :=
  ∑ j ∈ range y, ((θ + j) ^ 2)⁻¹ - θ⁻¹ + (θ + exp η)⁻¹ - (y - exp η) / (θ + exp η) ^ 2

private lemma ascPochhammer_eval_eq_prod (θ : ℝ) (k : ℕ) :
    (ascPochhammer ℝ k).eval θ = ∏ j ∈ range k, (θ + j) := by
  induction k with
  | zero => simp
  | succ k ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]

/-- **`nbLogPmf` is the log mass function.** For `θ > 0` and a count `y`,
`log NB(y; θ, e^η) = nbLogPmf θ y η`. -/
theorem log_negBinomialReal_exp_eq_nbLogPmf {θ : ℝ} (hθ : 0 < θ) (η : ℝ) (y : ℕ) :
    log (negBinomialReal θ (exp η) y) = nbLogPmf θ y η := by
  rw [log_negBinomialReal_exp hθ, ascPochhammer_eval_eq_prod,
    log_div (prod_ne_zero_iff.2 fun j _ => by positivity) (by positivity),
    log_prod fun j _ => by positivity]
  rfl

/-! ### Joint derivatives in `(θ, η)` -/

private lemma hasFDerivAt_shape_add_exp (θ η : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => q.1 + exp q.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ + exp η • ContinuousLinearMap.snd ℝ ℝ ℝ) (θ, η) := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => exp q.2) (exp η • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (θ, η) :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (θ, η)) (E := ℝ) (F := ℝ)).exp
  exact hasFDerivAt_fst.add h

private lemma hasFDerivAt_inv_shape_add_exp {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => (q.1 + exp q.2)⁻¹)
      (-((θ + exp η) ^ 2)⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ +
        exp η • ContinuousLinearMap.snd ℝ ℝ ℝ)) (θ, η) :=
  (hasDerivAt_inv (by positivity : θ + exp η ≠ 0)).comp_hasFDerivAt (θ, η)
    (hasFDerivAt_shape_add_exp θ η)

/-- **Joint score of one count.** For `θ > 0`, the log mass function is differentiable in
`(θ, η)` with partial derivatives `nbShapeScore θ y η` in the shape and `nbScore θ y η` in the
linear predictor. -/
theorem hasFDerivAt_nbLogPmf {θ : ℝ} (hθ : 0 < θ) (y : ℕ) (η : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => nbLogPmf q.1 y q.2)
      (nbShapeScore θ y η • ContinuousLinearMap.fst ℝ ℝ ℝ +
        nbScore θ y η • ContinuousLinearMap.snd ℝ ℝ ℝ) (θ, η) := by
  have hpos : 0 < θ + exp η := by positivity
  have hA : HasDerivAt (fun t : ℝ => ∑ j ∈ range y, log (t + j) - log (y ! : ℝ) + t * log t)
      (∑ j ∈ range y, (θ + j)⁻¹ + (1 * log θ + θ * θ⁻¹)) θ := by
    refine ((HasDerivAt.fun_sum fun j _ => ?_).sub_const _).add
      ((hasDerivAt_id θ).mul (hasDerivAt_log hθ.ne'))
    simpa using ((hasDerivAt_id' (x := θ)).add_const (j : ℝ)).log (by positivity)
  have hL := (hasFDerivAt_shape_add_exp θ η).log hpos.ne'
  have hK := (hasFDerivAt_snd.const_mul (y : ℝ)).sub
    ((hasFDerivAt_fst.const_add (y : ℝ)).mul hL)
  have h := (hA.comp_hasFDerivAt (θ, η) hasFDerivAt_fst).add hK
  convert h using 1
  · funext q
    simp [nbLogPmf, nbKernel]
  · ext <;>
    · simp [nbShapeScore, nbScore]
      field_simp
      ring

/-- **Joint derivative of the `η`-score.** For `θ > 0`, `nbScore θ y η = θ (y - μ) / (θ + μ)` has
partial derivatives `nbCross θ y η` in the shape and `-nbObsWeight θ y η` in `η`. -/
theorem hasFDerivAt_nbScore_prod {θ : ℝ} (hθ : 0 < θ) (y η : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => nbScore q.1 y q.2)
      (nbCross θ y η • ContinuousLinearMap.fst ℝ ℝ ℝ -
        nbObsWeight θ y η • ContinuousLinearMap.snd ℝ ℝ ℝ) (θ, η) := by
  have hpos : 0 < θ + exp η := by positivity
  have h := (hasFDerivAt_fst.mul (hasFDerivAt_snd.exp.const_sub y)).mul
    (hasFDerivAt_inv_shape_add_exp hθ η)
  convert h using 1
  · funext q
    simp [nbScore, div_eq_mul_inv]
  · ext <;>
    · simp [nbCross, nbObsWeight]
      field_simp
      ring

/-- **Joint derivative of the shape score.** For `θ > 0`, `nbShapeScore θ y η` has partial
derivatives `-nbShapeObsInfo θ y η` in the shape and `nbCross θ y η` in `η`; the mixed partials of
`nbLogPmf` agree. -/
theorem hasFDerivAt_nbShapeScore {θ : ℝ} (hθ : 0 < θ) (y : ℕ) (η : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => nbShapeScore q.1 y q.2)
      (-nbShapeObsInfo θ y η • ContinuousLinearMap.fst ℝ ℝ ℝ +
        nbCross θ y η • ContinuousLinearMap.snd ℝ ℝ ℝ) (θ, η) := by
  have hpos : 0 < θ + exp η := by positivity
  have hS : HasFDerivAt (fun q : ℝ × ℝ => ∑ j ∈ range y, (q.1 + j)⁻¹)
      (∑ j ∈ range y, (-((θ + j) ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ) (θ, η) :=
    HasFDerivAt.fun_sum fun j _ => (hasDerivAt_inv (by positivity : θ + j ≠ 0)).comp_hasFDerivAt
      (θ, η) (hasFDerivAt_fst.add_const (j : ℝ))
  have h := ((((hS.add (hasFDerivAt_fst.log hθ.ne')).add_const 1).sub
    ((hasFDerivAt_shape_add_exp θ η).log hpos.ne')).sub
    ((hasFDerivAt_fst.const_add (y : ℝ)).mul (hasFDerivAt_inv_shape_add_exp hθ η)))
  convert h using 1
  · funext q
    simp [nbShapeScore, div_eq_mul_inv]
  · ext <;>
    · simp [nbShapeObsInfo, nbCross]
      field_simp
      ring

/-! ### Expected information of one count -/

/-- **The mixed second derivative has mean zero.** For `θ > 0`,
`∑ₖ nbCross θ k η · NB(k; θ, e^η) = 0`: the shape and the regression coefficients are
orthogonal parameters. -/
theorem hasSum_nbCross_mul_negBinomialReal {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    HasSum (fun k : ℕ => nbCross θ k η * negBinomialReal θ (exp η) k) 0 := by
  have hμ := (exp_pos η).le
  set c := exp η / (θ + exp η) ^ 2
  have h := ((hasSum_mul_negBinomialReal hθ hμ).mul_left c).add
    ((hasSum_negBinomialReal hθ hμ).mul_left (-(c * exp η)))
  convert h using 1
  · funext k
    simp only [nbCross, c]
    ring
  · ring

/-- The trigamma-type part `∑_{j<k} 1 / (θ + j)²` of the observed shape information is at most
`k / θ²`. -/
private lemma sum_inv_sq_le {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    ∑ j ∈ range k, ((θ + j) ^ 2)⁻¹ ≤ k * (θ ^ 2)⁻¹ := by
  calc ∑ j ∈ range k, ((θ + j) ^ 2)⁻¹ ≤ ∑ _j ∈ range k, (θ ^ 2)⁻¹ :=
        sum_le_sum fun j _ => inv_anti₀ (by positivity)
          (pow_le_pow_left₀ hθ.le (by simp) 2)
    _ = k * (θ ^ 2)⁻¹ := by simp

private lemma summable_sum_inv_sq_mul {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    Summable fun k : ℕ => (∑ j ∈ range k, ((θ + j) ^ 2)⁻¹) * negBinomialReal θ (exp η) k := by
  have hμ := (exp_pos η).le
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sum_nonneg fun j _ => by positivity)
    (negBinomialReal_nonneg hθ hμ k)) (fun k => ?_)
    (((hasSum_mul_negBinomialReal hθ hμ).mul_right (θ ^ 2)⁻¹).summable)
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_right (sum_inv_sq_le hθ k) (negBinomialReal_nonneg hθ hμ k)

/-- The expected (Fisher) shape information of one count with linear predictor `η`,
`E[∑_{j<y} 1 / (θ + j)²] - 1 / θ + 1 / (θ + μ)` for `y ~ NB(θ, μ)` and `μ = e^η`: the mean of
`nbShapeObsInfo θ y η` (`hasSum_nbShapeObsInfo_mul_negBinomialReal`). The series is the
trigamma difference `ψ₁(θ) - E ψ₁(θ + y)`; no closed form is used. -/
noncomputable def nbShapeFisherInfo (θ η : ℝ) : ℝ :=
  ∑' k : ℕ, (∑ j ∈ range k, ((θ + j) ^ 2)⁻¹) * negBinomialReal θ (exp η) k - θ⁻¹ +
    (θ + exp η)⁻¹

/-- **Expected shape information.** For `θ > 0`, the observed shape information averaged over
`y ~ NB(θ, e^η)` is `nbShapeFisherInfo θ η`. -/
theorem hasSum_nbShapeObsInfo_mul_negBinomialReal {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    HasSum (fun k : ℕ => nbShapeObsInfo θ k η * negBinomialReal θ (exp η) k)
      (nbShapeFisherInfo θ η) := by
  have hμ := (exp_pos η).le
  set c := (θ + exp η) ^ 2
  have h := (((summable_sum_inv_sq_mul hθ η).hasSum.add
    ((hasSum_negBinomialReal hθ hμ).mul_left (-θ⁻¹ + (θ + exp η)⁻¹ + exp η / c))).add
    ((hasSum_mul_negBinomialReal hθ hμ).mul_left (-c⁻¹)))
  convert h using 1
  · funext k
    simp only [nbShapeObsInfo, c]
    ring
  · simp only [nbShapeFisherInfo, c]
    field_simp
    ring

/-! ### Information matrices

Parameters are `(β, θ)`; matrices are indexed by `κ ⊕ Unit`, with `Sum.inl j` the coefficient
`βⱼ` and `Sum.inr ()` the shape `θ`. -/

variable {ι κ : Type*}

/-- The observed information of one count `y` with covariate row `x` and linear predictor `η`,
i.e. minus the Hessian of `(β, θ) ↦ nbLogPmf θ y (x ⬝ᵥ β + o)`:
`[[w x xᵀ, -c x], [-c xᵀ, v]]` with `w = nbObsWeight θ y η`, `c = nbCross θ y η` and
`v = nbShapeObsInfo θ y η`. -/
noncomputable def nbObsInfoRow (θ : ℝ) (x : κ → ℝ) (y : ℕ) (η : ℝ) :
    Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ :=
  fromBlocks (nbObsWeight θ y η • vecMulVec x x) (of fun j _ => -(nbCross θ y η * x j))
    (of fun _ k => -(nbCross θ y η * x k)) (of fun _ _ => nbShapeObsInfo θ y η)

/-- The expected (Fisher) information of one count with covariate row `x` and linear predictor
`η`: `[[F x xᵀ, 0], [0, nbShapeFisherInfo θ η]]` with `F = nbFisherWeight θ η`. It is block
diagonal (`hasSum_nbObsInfoRow`). -/
noncomputable def nbFisherInfoRow (θ : ℝ) (x : κ → ℝ) (η : ℝ) :
    Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ :=
  fromBlocks (nbFisherWeight θ η • vecMulVec x x) 0 0 (of fun _ _ => nbShapeFisherInfo θ η)

/-- **Expected information of one count.** For `θ > 0`, the observed information matrix averaged
over `y ~ NB(θ, e^η)` is the block-diagonal Fisher information `nbFisherInfoRow θ x η`. -/
theorem hasSum_nbObsInfoRow {θ : ℝ} (hθ : 0 < θ) (x : κ → ℝ) (η : ℝ) :
    HasSum (fun k : ℕ => negBinomialReal θ (exp η) k • nbObsInfoRow θ x k η)
      (nbFisherInfoRow θ x η) := by
  refine Pi.hasSum.2 fun a => Pi.hasSum.2 fun b => ?_
  rcases a with j | _ <;> rcases b with l | _
  · simpa [nbObsInfoRow, nbFisherInfoRow, vecMulVec, mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_nbObsWeight_mul_negBinomialReal hθ η).mul_right (x j * x l)
  · simpa [nbObsInfoRow, nbFisherInfoRow, mul_comm, mul_left_comm, mul_assoc] using
      ((hasSum_nbCross_mul_negBinomialReal hθ η).mul_right (-x j))
  · simpa [nbObsInfoRow, nbFisherInfoRow, mul_comm, mul_left_comm, mul_assoc] using
      ((hasSum_nbCross_mul_negBinomialReal hθ η).mul_right (-x l))
  · simpa [nbObsInfoRow, nbFisherInfoRow, mul_comm] using
      hasSum_nbShapeObsInfo_mul_negBinomialReal hθ η

/-- **The quadratic form of one observed-information row**: along the direction `(u, s)`,
`w (x ⬝ᵥ u)² - 2 s c (x ⬝ᵥ u) + s² v`. -/
theorem nbObsInfoRow_quadratic [Fintype κ] (θ : ℝ) (x : κ → ℝ) (y : ℕ) (η : ℝ) (u : κ → ℝ)
    (s : ℝ) :
    Sum.elim u (fun _ : Unit => s) ⬝ᵥ (nbObsInfoRow θ x y η *ᵥ Sum.elim u (fun _ : Unit => s)) =
      nbObsWeight θ y η * (x ⬝ᵥ u) ^ 2 - 2 * s * nbCross θ y η * (x ⬝ᵥ u) +
        s ^ 2 * nbShapeObsInfo θ y η := by
  rw [nbObsInfoRow, fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Function.comp_def, smul_mulVec, vecMulVec_mulVec, mulVec, of_apply, Finset.univ_unique,
    Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  have h1 : ∀ (w c A : ℝ) (a : κ), u a * (w * (x a * A) + -(c * x a) * s) =
      x a * u a * (w * A - c * s) := fun w c A a => by ring
  have h2 : ∀ (c : ℝ) (a : κ), -(c * x a) * u a = x a * u a * -c := fun c a => by ring
  simp_rw [h1, h2, ← Finset.sum_mul]
  ring

variable [Fintype ι] [Fintype κ]

/-- The joint negative binomial log-likelihood in `(β, θ)` with design `X`, fixed offset `o` and
counts `y`: `∑ᵢ nbLogPmf θ yᵢ ((X β)ᵢ + oᵢ)`. For `θ > 0` it is `∑ᵢ log NB(yᵢ; θ, μᵢ)`
(`log_negBinomialReal_exp_eq_nbLogPmf`), the shape included. -/
noncomputable def nbJointLogLik (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) (p : (κ → ℝ) × ℝ) :
    ℝ :=
  ∑ i, nbLogPmf p.2 (y i) ((X *ᵥ p.1) i + o i)

/-- The shape component of the joint score, `∑ᵢ nbShapeScore θ yᵢ ηᵢ`. -/
noncomputable def nbJointShapeScore (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    (p : (κ → ℝ) × ℝ) : ℝ :=
  ∑ i, nbShapeScore p.2 (y i) ((X *ᵥ p.1) i + o i)

/-- The joint observed information `∑ᵢ nbObsInfoRow θ (X i) yᵢ ηᵢ` of the regression, i.e. minus
the Hessian of `nbJointLogLik` (`hasDerivAt_nbJointScore_line`). -/
noncomputable def nbJointObsInfo (θ : ℝ) (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    (β : κ → ℝ) : Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ :=
  ∑ i, nbObsInfoRow θ (X i) (y i) ((X *ᵥ β) i + o i)

/-- The joint expected (Fisher) information `∑ᵢ nbFisherInfoRow θ (X i) ηᵢ` of the regression: the
sum over observations of the per-count means of `nbObsInfoRow` (`hasSum_nbObsInfoRow`). -/
noncomputable def nbJointFisherInfo (θ : ℝ) (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) :
    Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ :=
  ∑ i, nbFisherInfoRow θ (X i) ((X *ᵥ β) i + o i)

omit [Fintype ι] in
private lemma hasFDerivAt_predictor_prod (X : Matrix ι κ ℝ) (o : ι → ℝ)
    (p : (κ → ℝ) × ℝ) (i : ι) :
    HasFDerivAt (fun q : (κ → ℝ) × ℝ => (q.2, (X *ᵥ q.1) i + o i))
      ((ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ).prod
        ((Real.dotL (X i)).comp (ContinuousLinearMap.fst ℝ (κ → ℝ) ℝ))) p := by
  refine hasFDerivAt_snd.prodMk ?_
  have h : (fun q : (κ → ℝ) × ℝ => (X *ᵥ q.1) i + o i) =
      fun q => Real.dotL (X i) (ContinuousLinearMap.fst ℝ (κ → ℝ) ℝ q) + o i := by
    funext q
    simp [mulVec, dotProduct_comm]
  rw [h]
  exact (((Real.dotL (X i)).comp (ContinuousLinearMap.fst ℝ (κ → ℝ) ℝ)).hasFDerivAt).add_const _

/-- **The joint score.** For `θ > 0`, the joint log-likelihood is differentiable at `(β, θ)` with
derivative `(v, s) ↦ ⟪v, Xᵀ s(β, θ)⟫ + s · ∑ᵢ nbShapeScore θ yᵢ ηᵢ`: the `β`-block is the
fixed-shape score vector `nbGradient`, the `θ`-block is `nbJointShapeScore`. -/
theorem hasFDerivAt_nbJointLogLik (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    {p : (κ → ℝ) × ℝ} (hθ : 0 < p.2) :
    HasFDerivAt (nbJointLogLik X o y)
      ((Real.dotL (nbGradient p.2 X o (fun i => (y i : ℝ)) p.1)).comp
          (ContinuousLinearMap.fst ℝ (κ → ℝ) ℝ) +
        nbJointShapeScore X o y p • ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ) p := by
  have h : HasFDerivAt (nbJointLogLik X o y) (∑ i,
      (nbShapeScore p.2 (y i) ((X *ᵥ p.1) i + o i) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        nbScore p.2 (y i) ((X *ᵥ p.1) i + o i) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ).prod
        ((Real.dotL (X i)).comp (ContinuousLinearMap.fst ℝ (κ → ℝ) ℝ)))) p := by
    unfold nbJointLogLik
    refine HasFDerivAt.fun_sum fun i _ => ?_
    have := (hasFDerivAt_nbLogPmf hθ (y i) ((X *ᵥ p.1) i + o i)).comp p
      (hasFDerivAt_predictor_prod X o p i)
    exact this
  convert h using 1
  ext v
  · simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.snd_comp_inl, smul_zero, add_zero, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_fst', Real.dotL_apply,
      ContinuousLinearMap.fst_comp_prod, ContinuousLinearMap.snd_comp_prod, _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero,
      zero_add, nbGradient, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  · simp [nbJointShapeScore]

/-- **The joint observed information is minus the Hessian.** For `θ > 0` and a direction
`d = (u, s)`, the derivative at `t = 0` of `t ↦ ∇ℓ(p + t d) · d` (the joint score of
`hasFDerivAt_nbJointLogLik` applied to `d`) is `-dᵀ J d` with `J = nbJointObsInfo θ X o y β`. -/
theorem hasDerivAt_nbJointScore_line (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    {p : (κ → ℝ) × ℝ} (hθ : 0 < p.2) (d : (κ → ℝ) × ℝ) :
    HasDerivAt (fun t : ℝ =>
        nbGradient (p + t • d).2 X o (fun i => (y i : ℝ)) (p + t • d).1 ⬝ᵥ d.1 +
          nbJointShapeScore X o y (p + t • d) * d.2)
      (-(Sum.elim d.1 (fun _ : Unit => d.2) ⬝ᵥ
        (nbJointObsInfo p.2 X o y p.1 *ᵥ Sum.elim d.1 (fun _ : Unit => d.2)))) 0 := by
  obtain ⟨β, θ⟩ := p
  obtain ⟨u, s⟩ := d
  simp only at hθ ⊢
  have hfun : (fun t : ℝ => nbGradient ((β, θ) + t • (u, s)).2 X o (fun i => (y i : ℝ))
      ((β, θ) + t • (u, s)).1 ⬝ᵥ u + nbJointShapeScore X o y ((β, θ) + t • (u, s)) * s) =
      fun t => ∑ i, (nbScore (θ + t * s) (y i) ((X *ᵥ β) i + o i + t * (X *ᵥ u) i) * (X *ᵥ u) i +
        nbShapeScore (θ + t * s) (y i) ((X *ᵥ β) i + o i + t * (X *ᵥ u) i) * s) := by
    funext t
    rw [Finset.sum_add_distrib, nbJointShapeScore, Finset.sum_mul, nbGradient, dotProduct_comm,
      dotProduct_transpose_mulVec]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotProduct,
      mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply]
    congr 1
    · exact sum_congr rfl fun i _ => by ring_nf
    · exact sum_congr rfl fun i _ => by ring_nf
  rw [hfun, nbJointObsInfo, sum_mulVec, dotProduct_sum, ← sum_neg_distrib]
  refine HasDerivAt.fun_sum fun i _ => ?_
  rw [nbObsInfoRow_quadratic]
  have hline : HasDerivAt (fun t : ℝ => (θ + t * s, (X *ᵥ β) i + o i + t * (X *ᵥ u) i))
      (s, (X *ᵥ u) i) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using ((hasDerivAt_id' (x := (0 : ℝ))).mul_const s).const_add θ
    · simpa using ((hasDerivAt_id' (x := (0 : ℝ))).mul_const ((X *ᵥ u) i)).const_add
        ((X *ᵥ β) i + o i)
  have h1 := (hasFDerivAt_nbScore_prod hθ (y i) ((X *ᵥ β) i + o i)).comp_hasDerivAt_of_eq
    (0 : ℝ) hline (by simp)
  have h2 := (hasFDerivAt_nbShapeScore hθ (y i) ((X *ᵥ β) i + o i)).comp_hasDerivAt_of_eq
    (0 : ℝ) hline (by simp)
  convert (h1.mul_const ((X *ᵥ u) i)).add (h2.mul_const s) using 1
  · rfl
  · simp [mulVec, dotProduct]
    ring

/-! ### Block-diagonal Fisher information and inference for `β` -/

/-- **The joint Fisher information is block diagonal**: the `β`-block is the fixed-shape Fisher
information `Xᵀ diag(F) X` with weights `Fᵢ = nbFisherWeight θ ηᵢ`, the `θ`-block is
`∑ᵢ nbShapeFisherInfo θ ηᵢ`, and the cross blocks vanish (`hasSum_nbCross_mul_negBinomialReal`). -/
theorem nbJointFisherInfo_eq_fromBlocks [DecidableEq ι] (θ : ℝ) (X : Matrix ι κ ℝ) (o : ι → ℝ)
    (β : κ → ℝ) :
    nbJointFisherInfo θ X o β =
      fromBlocks (Xᵀ * diagonal (fun i => nbFisherWeight θ ((X *ᵥ β) i + o i)) * X) 0 0
        (of fun _ _ => ∑ i, nbShapeFisherInfo θ ((X *ᵥ β) i + o i)) := by
  ext (j | _) (l | _)
  · rw [fromBlocks_apply₁₁, mul_apply]
    simp only [nbJointFisherInfo, nbFisherInfoRow, Matrix.sum_apply, fromBlocks_apply₁₁,
      Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, mul_diagonal, transpose_apply]
    exact sum_congr rfl fun _ _ => by ring
  all_goals simp [nbJointFisherInfo, nbFisherInfoRow, Matrix.sum_apply]

/-- **Estimating the shape does not change the `β`-block of the inverse Fisher information.** If
the fixed-shape Fisher information `A = Xᵀ diag(F) X` is invertible and the total shape information
`D = ∑ᵢ nbShapeFisherInfo θ ηᵢ` is nonzero, the inverse of the joint Fisher information is
`[[A⁻¹, 0], [0, D⁻¹]]`. So the asymptotic covariance `A⁻¹` that the information assigns to `β̂` is
the same whether `θ` is known or estimated jointly. -/
theorem inv_nbJointFisherInfo [DecidableEq ι] [DecidableEq κ] (θ : ℝ) (X : Matrix ι κ ℝ) (o : ι → ℝ)
    (β : κ → ℝ) (hA : IsUnit (Xᵀ * diagonal (fun i => nbFisherWeight θ ((X *ᵥ β) i + o i)) * X))
    (hD : ∑ i, nbShapeFisherInfo θ ((X *ᵥ β) i + o i) ≠ 0) :
    (nbJointFisherInfo θ X o β)⁻¹ =
      fromBlocks (Xᵀ * diagonal (fun i => nbFisherWeight θ ((X *ᵥ β) i + o i)) * X)⁻¹ 0 0
        (of fun _ _ => (∑ i, nbShapeFisherInfo θ ((X *ᵥ β) i + o i))⁻¹) := by
  rw [nbJointFisherInfo_eq_fromBlocks]
  refine inv_eq_right_inv ?_
  rw [fromBlocks_multiply, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hA)]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← fromBlocks_one]
  congr 1
  ext
  simp [mul_apply, hD]

/-- **The `β`-block of the inverse joint Fisher information** is the inverse fixed-shape Fisher
information (`inv_nbJointFisherInfo`). -/
theorem toBlocks₁₁_inv_nbJointFisherInfo [DecidableEq ι] [DecidableEq κ] (θ : ℝ) (X : Matrix ι κ ℝ)
    (o : ι → ℝ) (β : κ → ℝ)
    (hA : IsUnit (Xᵀ * diagonal (fun i => nbFisherWeight θ ((X *ᵥ β) i + o i)) * X))
    (hD : ∑ i, nbShapeFisherInfo θ ((X *ᵥ β) i + o i) ≠ 0) :
    (nbJointFisherInfo θ X o β)⁻¹.toBlocks₁₁ =
      (Xᵀ * diagonal (fun i => nbFisherWeight θ ((X *ᵥ β) i + o i)) * X)⁻¹ := by
  rw [inv_nbJointFisherInfo θ X o β hA hD, toBlocks_fromBlocks₁₁]

/-! ### Consistency with an estimated shape -/

/-- The averaged joint log-likelihood of the first `n` observations of a sample with covariate rows
`x i ω`, offsets `o i ω` and counts `y i ω`, at `p = (β, θ)`:
`n⁻¹ ∑_{i<n} nbLogPmf θ (y i ω) (x i ω ⬝ᵥ β + o i ω)`. It is `n⁻¹ • nbJointLogLik` of the
`n`-row design (`nbAvgLogLik_eq_nbJointLogLik`). -/
noncomputable def nbAvgLogLik {Ω : Type*} (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ)
    (n : ℕ) (ω : Ω) (p : (κ → ℝ) × ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ range n, nbLogPmf p.2 (y i ω) (x i ω ⬝ᵥ p.1 + o i ω)

omit [Fintype ι] in
/-- The averaged log-likelihood is the joint log-likelihood of the design with rows
`x 0 ω, …, x (n - 1) ω`, divided by `n`. -/
theorem nbAvgLogLik_eq_nbJointLogLik {Ω : Type*} (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ)
    (y : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) (p : (κ → ℝ) × ℝ) :
    nbAvgLogLik x o y n ω p = (n : ℝ)⁻¹ *
      nbJointLogLik (of fun i : Fin n => x i ω) (fun i => o i ω) (fun i => y i ω) p := by
  simp only [nbAvgLogLik, nbJointLogLik, mulVec, of_apply]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun i => nbLogPmf p.2 (y i ω) (x i ω ⬝ᵥ p.1 + o i ω)) n).symm

/-- A unique maximizer of a continuous function on a compact set is well separated. -/
private lemma exists_sub_le_of_isCompact {Θ : Type*} [PseudoMetricSpace Θ] {M : Θ → ℝ}
    {K : Set Θ} (hK : IsCompact K) (hM : ContinuousOn M K) {p₀ : Θ}
    (hident : ∀ p ∈ K, p ≠ p₀ → M p < M p₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ε ≤ dist p p₀ → M p ≤ M p₀ - δ := by
  set C := K ∩ {p | ε ≤ dist p p₀}
  rcases C.eq_empty_or_nonempty with hC | hC
  · refine ⟨1, one_pos, fun p hp hpε => ?_⟩
    exact absurd (show p ∈ C from ⟨hp, hpε⟩) (hC ▸ Set.notMem_empty p)
  have hCc : IsCompact C := hK.inter_right (isClosed_le continuous_const
    (continuous_id.dist continuous_const))
  obtain ⟨q, hq, hmax⟩ := hCc.exists_isMaxOn hC (hM.mono Set.inter_subset_left)
  have hq0 : q ≠ p₀ := by
    rintro rfl
    have := hq.2
    simp only [Set.mem_ofPred_eq, dist_self] at this
    linarith
  refine ⟨M p₀ - M q, sub_pos.2 (hident q hq.1 hq0), fun p hp hpε => ?_⟩
  have := isMaxOn_iff.1 hmax p ⟨hp, hpε⟩
  linarith

/-- **Consistency of the joint `(β, θ)` maximum likelihood estimator, under explicit hypotheses.**

Let `K` be a compact parameter set of pairs `(β, θ)` (the shape `θ` is estimated) and let `M` be a
population criterion (typically the expected log mass function) such that

* (continuity) `M` is continuous on `K`;
* (identifiability) `p₀ ∈ K` is the unique maximizer of `M` on `K`;
* (uniform law of large numbers) the averaged joint log-likelihood `nbAvgLogLik` converges to `M`
  uniformly on `K` in probability;
* (estimator) `p̂ n` lies in `K` and maximizes the averaged log-likelihood over `K` up to an
  arbitrary `δ > 0`, each with probability tending to one (an exact maximizer over `K` qualifies).

Then `p̂ n → p₀` in probability. None of the three conditions is derived from a sampling model
here; in particular the uniform LLN and the identification of `p₀` as the maximizer of the
expected log-likelihood are hypotheses. The probabilities of the possibly non-measurable events are
outer measures, so no measurability of `p̂` is needed. -/
theorem tendstoInMeasure_nbJointMLE {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ) {M : (κ → ℝ) × ℝ → ℝ}
    {K : Set ((κ → ℝ) × ℝ)} (hK : IsCompact K) (hM : ContinuousOn M K) {p₀ : (κ → ℝ) × ℝ}
    (hp₀ : p₀ ∈ K) (hident : ∀ p ∈ K, p ≠ p₀ → M p < M p₀)
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ =>
      P {ω | ∃ p ∈ K, ε ≤ |nbAvgLogLik x o y n ω p - M p|}) atTop (𝓝 0))
    {phat : ℕ → Ω → (κ → ℝ) × ℝ} (hphatK : Tendsto (fun n => P {ω | phat n ω ∉ K}) atTop (𝓝 0))
    (hmax : ∀ δ > 0, Tendsto (fun n => P {ω |
      nbAvgLogLik x o y n ω (phat n ω) < nbAvgLogLik x o y n ω p₀ - δ}) atTop (𝓝 0)) :
    TendstoInMeasure P phat atTop (fun _ => p₀) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨δ, hδ, hsep⟩ := exists_sub_le_of_isCompact hK hM hident hε
  have hsum := ((hphatK.add (hmax (δ / 3) (by positivity))).add
    (hunif (δ / 3) (by positivity)))
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans ((measure_union_le _ _).trans
      (add_le_add_left (measure_union_le _ _) _))
  simp only [Set.mem_ofPred_eq] at hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_exists, not_and, not_le] at hcon
  obtain ⟨⟨hK', hmx⟩, hu⟩ := hcon
  have h1 := hsep _ (not_not.1 hK') hω
  have h2 := (abs_lt.1 (hu _ (not_not.1 hK'))).2
  have h3 := (abs_lt.1 (hu _ hp₀)).1
  linarith

/-- A continuous image of an in-probability limit at a constant. -/
private lemma tendstoInMeasure_comp_const {Ω Θ E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [PseudoMetricSpace Θ] [PseudoMetricSpace E] {g : Θ → E} {p₀ : Θ} (hg : ContinuousAt g p₀)
    {phat : ℕ → Ω → Θ} (h : TendstoInMeasure P phat atTop (fun _ => p₀)) :
    TendstoInMeasure P (fun n ω => g (phat n ω)) atTop (fun _ => g p₀) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hg ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ) (fun _ => zero_le)
    fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hlt
  exact (hball (not_le.1 hlt)).not_ge hω

/-- **The estimated shape is consistent** whenever the joint estimator is
(`tendstoInMeasure_nbJointMLE`). -/
theorem tendstoInMeasure_snd_of_nbJointMLE {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {phat : ℕ → Ω → (κ → ℝ) × ℝ} {p₀ : (κ → ℝ) × ℝ}
    (h : TendstoInMeasure P phat atTop (fun _ => p₀)) :
    TendstoInMeasure P (fun n ω => (phat n ω).2) atTop (fun _ => p₀.2) :=
  tendstoInMeasure_comp_const continuous_snd.continuousAt h

/-- **Plug-in Fisher weights.** If `(β̂, θ̂) → (β₀, θ₀)` in probability with `θ₀ > 0`, then the
plug-in Fisher weights `nbFisherWeight θ̂ ((X β̂)ᵢ + oᵢ)` converge in probability to the weights at
`(β₀, θ₀)`; hence so does the plug-in `β`-block `Xᵀ diag(F) X` of the joint Fisher information,
which by `toBlocks₁₁_inv_nbJointFisherInfo` is the information for `β` whether or not the shape is
estimated. -/
theorem tendstoInMeasure_nbFisherWeight_plugIn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Matrix ι κ ℝ) (o : ι → ℝ) {phat : ℕ → Ω → (κ → ℝ) × ℝ} {p₀ : (κ → ℝ) × ℝ}
    (hθ : 0 < p₀.2) (h : TendstoInMeasure P phat atTop (fun _ => p₀)) :
    TendstoInMeasure P (fun n ω i => nbFisherWeight (phat n ω).2 ((X *ᵥ (phat n ω).1) i + o i))
      atTop (fun _ i => nbFisherWeight p₀.2 ((X *ᵥ p₀.1) i + o i)) := by
  refine tendstoInMeasure_comp_const (g := fun p : (κ → ℝ) × ℝ => fun i =>
    nbFisherWeight p.2 ((X *ᵥ p.1) i + o i)) ?_ h
  refine continuousAt_pi.2 fun i => ?_
  have hη : Continuous fun p : (κ → ℝ) × ℝ => (X *ᵥ p.1) i + o i := by
    simp only [mulVec, dotProduct]
    fun_prop
  unfold nbFisherWeight
  refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
  positivity

end MathlibExt.Probability.Statistics.GLM.NegativeBinomial
