/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.VectorInference
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Tactic.Module

/-!
# Longitudinal count GEE with a negative binomial working covariance

A cluster is observed at the finite set of occasions `T`: at occasion `t` it carries a covariate
vector `x t ∈ E` (a finite-dimensional real inner product space) and a count `y t ∈ ℝ`. The
marginal mean model has the log link, `μ_t(β) = exp ⟪x t, β⟫` (`countMean`), and the working
variance is the negative binomial (NB2) variance function `v(μ) = μ + α μ²` (`nbVariance`),
with dispersion `α ≥ 0`; `α = 0` is the Poisson variance. With a working correlation `R_w`, the
working covariance of Liang and Zeger is `V = A^{1/2} R_w A^{1/2}`, `A = diag v(μ_t)`, so
`V⁻¹ = A^{-1/2} Q A^{-1/2}` with `Q = R_w⁻¹`. The matrix `Q : Matrix T T ℝ` is the input here,
so no matrix inverse appears; it is an arbitrary fixed matrix. With `D = ∂μ/∂β`, whose row `s` is
`μ_s (x s)ᵀ`, the GEE score of one cluster is (`countGEEScore`)

`ψ(β; x, y) = Dᵀ V⁻¹ (y - μ) = ∑_s ∑_t Q_st w_s w_t μ_s (y_t - μ_t) x s`, `w_t = v(μ_t)^{-1/2}`,

and the model-based information `Dᵀ V⁻¹ D` is `countGEEInfo`. Clusters are i.i.d. with joint law
`μx ⊗ₘ κ`: covariates with law `μx`, counts with conditional law `κ x` given the covariates.

## Main results

* `integral_countGEEScore_eq_zero`: **unbiasedness.** If the conditional mean model is correct,
  `E[y_t | x] = μ_t(β₀)`, then `E ψ(β₀) = 0`, for every `α` and every `Q`; neither the NB
  variance nor the working correlation needs to be correct.
* `fderiv_countGEEScore`: the Jacobian of the score is a residual-weighted term minus the
  model-based information, `∂ψ/∂β = ∑ (y - μ) • (…) - Dᵀ V⁻¹ D`.
* `integral_fderiv_countGEEScore`: **the bread.** Under a correct mean model the residual term
  has mean zero, so `E ∂ψ(β₀)/∂β = -A` with `A = E[Dᵀ V⁻¹ D]`.
* `integral_inner_countGEEScore_sq` and `integral_inner_countGEEScore_sq_compProd`: **the meat
  under a correct working covariance.** If the conditional second moments about the model mean
  are `v(μ_s)^{1/2} v(μ_t)^{1/2} R_st` with `Q R = 1`, the meat equals the bread:
  `E ⟪ψ(β₀), u⟫² = ⟪A u, u⟫`.
* `tendstoInDistribution_sqrt_smul_sub_countGEE`: **sandwich asymptotic normality.**
  `√n (β̂ₙ - β₀) → A⁻¹ Y` with `⟪Y, t⟫ ~ N(0, E ⟪ψ(β₀), t⟫²)`, i.e. limiting covariance
  `A⁻¹ B A⁻ᵀ` with meat `B = E[ψ ψᵀ] = E[Dᵀ V⁻¹ Cov(y | x) (V⁻¹)ᵀ D]`; the transpose matters
  because `Q`, hence `V⁻¹`, need not be symmetric. This applies
  `VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation` (the i.i.d.
  Z-estimator theorem) to the count GEE score, discharging differentiability, measurability,
  the centering `E ψ(β₀) = 0` and the bread identification; it is not restated.
* `tendstoInDistribution_sqrt_smul_sub_countGEE_modelBased`: under a correct NB working
  covariance the meat is `A` and the limit `A⁻¹ Y` has `⟪Y, t⟫ ~ N(0, ⟪A t, t⟫)`, so the sandwich
  reduces to the model-based covariance `A⁻¹` (here `A` is symmetric: the second-moment hypothesis
  forces `R`, hence `Q = R⁻¹`, to be symmetric).

## Hypotheses that stay explicit, and what is not claimed

* As in `VectorInference`, existence of a root with probability tending to one and consistency
  of `β̂ₙ` are hypotheses, and `β₀` is interior (a ball of radius `δ`).
* The Lipschitz envelope `M` of the score Jacobian near `β₀`, its integrability, the second
  moment of the score, the strong measurability and integrability of the Jacobian at `β₀`, and
  the integrability of the model-based information are hypotheses; no explicit envelope for the
  exponential mean is derived.
* Nonsingularity of the bread `A` is a hypothesis (`IsUnit`).
* `Q` and `α` are fixed. Estimated working parameters (`α̂`, `R̂_w`) are treated by
  `Longitudinal.GEE.EstimatedWeights` for a generic score; that plug-in is not combined with the
  count score here.
* The cluster size `|T|` is fixed and common to all clusters, and the conditional law of the
  counts need not be negative binomial: only its conditional mean (and, for the model-based
  result, its conditional second moments) enter.

## References

* K.-Y. Liang and S. L. Zeger, "Longitudinal data analysis using generalized linear models",
  Biometrika 73 (1986) 13–22.
* S. L. Zeger and K.-Y. Liang, "Longitudinal data analysis for discrete and continuous
  outcomes", Biometrics 42 (1986) 121–130.
* A. C. Cameron and P. K. Trivedi, *Regression Analysis of Count Data*, 2nd ed. (2013), §9.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Longitudinal.GEE.CountGEE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : Type*}

/-! ### The count GEE score -/

/-- The negative binomial (NB2) variance function `v(m) = m + α m²`; `α = 0` is the Poisson
variance. -/
def nbVariance (α m : ℝ) : ℝ := m + α * m ^ 2

theorem nbVariance_pos {α m : ℝ} (hα : 0 ≤ α) (hm : 0 < m) : 0 < nbVariance α m := by
  unfold nbVariance; positivity

/-- The log-link mean `μ_t(β) = exp ⟪x t, β⟫` at occasion `t`. -/
noncomputable def countMean (β : E) (x : T → E) (t : T) : ℝ := Real.exp ⟪x t, β⟫

theorem countMean_pos (β : E) (x : T → E) (t : T) : 0 < countMean β x t := Real.exp_pos _

/-- The working weight `w_t = v(μ_t)^{-1/2}`, the diagonal entry of `A^{-1/2}`. -/
noncomputable def nbInvSqrtVar (α : ℝ) (β : E) (x : T → E) (t : T) : ℝ :=
  (√(nbVariance α (countMean β x t)))⁻¹

theorem sqrt_nbVariance_mul_nbInvSqrtVar {α : ℝ} (hα : 0 ≤ α) (β : E) (x : T → E) (t : T) :
    √(nbVariance α (countMean β x t)) * nbInvSqrtVar α β x t = 1 :=
  mul_inv_cancel₀ (Real.sqrt_pos.2 (nbVariance_pos hα (countMean_pos β x t))).ne'

/-- The scalar coefficient `Q_st w_s w_t μ_s` of `(y_t - μ_t) • x s` in the score. -/
noncomputable def countGEECoeff (Q : Matrix T T ℝ) (α : ℝ) (β : E) (x : T → E) (s t : T) : ℝ :=
  Q s t * nbInvSqrtVar α β x s * nbInvSqrtVar α β x t * countMean β x s

theorem hasFDerivAt_countMean (β : E) (x : T → E) (t : T) :
    HasFDerivAt (fun b => countMean b x t) (countMean β x t • innerSL ℝ (x t)) β := by
  have h := ((innerSL ℝ (x t)).hasFDerivAt (x := β)).exp
  unfold countMean
  simpa only [innerSL_apply_apply] using h

theorem differentiableAt_countGEECoeff {α : ℝ} (hα : 0 ≤ α) (Q : Matrix T T ℝ) (β : E)
    (x : T → E) (s t : T) : DifferentiableAt ℝ (fun b => countGEECoeff Q α b x s t) β := by
  have hm : ∀ r, DifferentiableAt ℝ (fun b => countMean b x r) β := fun r =>
    (hasFDerivAt_countMean β x r).differentiableAt
  have hw : ∀ r, DifferentiableAt ℝ (fun b => nbInvSqrtVar α b x r) β := fun r => by
    have hv : DifferentiableAt ℝ (fun b => nbVariance α (countMean b x r)) β := by
      unfold nbVariance
      exact (hm r).add (((hm r).pow 2).const_mul α)
    have hpos := nbVariance_pos hα (countMean_pos β x r)
    exact (hv.sqrt hpos.ne').inv (Real.sqrt_pos.2 hpos).ne'
  unfold countGEECoeff
  exact (((differentiableAt_const _).mul (hw s)).mul (hw t)).mul (hm s)

variable [Fintype T]

/-- The **count GEE score** of one cluster `z = (x, y)`,
`ψ(β; x, y) = Dᵀ V⁻¹ (y - μ) = ∑_s ∑_t Q_st w_s w_t μ_s (y_t - μ_t) x s`, for the log-link mean,
the NB2 working variance with dispersion `α`, and inverse working correlation `Q`. -/
noncomputable def countGEEScore (Q : Matrix T T ℝ) (α : ℝ) (β : E) (z : (T → E) × (T → ℝ)) :
    E :=
  ∑ s, ∑ t, (countGEECoeff Q α β z.1 s t * (z.2 t - countMean β z.1 t)) • z.1 s

/-- The **model-based information** `Dᵀ V⁻¹ D` of a cluster with covariates `x`,
`h ↦ ∑_s ∑_t Q_st w_s w_t μ_s μ_t ⟪x t, h⟫ x s`. -/
noncomputable def countGEEInfo (Q : Matrix T T ℝ) (α : ℝ) (β : E) (x : T → E) : E →L[ℝ] E :=
  ∑ s, ∑ t, (countGEECoeff Q α β x s t * countMean β x t) • (innerSL ℝ (x t)).smulRight (x s)

theorem countGEEInfo_apply (Q : Matrix T T ℝ) (α : ℝ) (β : E) (x : T → E) (h : E) :
    countGEEInfo Q α β x h =
      ∑ s, ∑ t, (countGEECoeff Q α β x s t * countMean β x t * ⟪x t, h⟫) • x s := by
  simp only [countGEEInfo, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]

/-- The score is a sum of residuals `y_t - μ_t` times covariate-only vectors. -/
theorem countGEEScore_eq_sum_residual (Q : Matrix T T ℝ) (α : ℝ) (β : E)
    (z : (T → E) × (T → ℝ)) :
    countGEEScore Q α β z =
      ∑ t, (z.2 t - countMean β z.1 t) • ∑ s, countGEECoeff Q α β z.1 s t • z.1 s := by
  unfold countGEEScore
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_smul, mul_comm]

theorem inner_countGEEScore_eq (Q : Matrix T T ℝ) (α : ℝ) (β : E) (z : (T → E) × (T → ℝ))
    (u : E) :
    ⟪countGEEScore Q α β z, u⟫ =
      ∑ t, (z.2 t - countMean β z.1 t) * ∑ s, countGEECoeff Q α β z.1 s t * ⟪z.1 s, u⟫ := by
  rw [countGEEScore_eq_sum_residual, sum_inner]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [real_inner_smul_left, sum_inner]
  congr 1
  exact Finset.sum_congr rfl fun s _ => real_inner_smul_left _ _ _

/-! ### The Jacobian of the score -/

theorem hasFDerivAt_countGEEScore {α : ℝ} (hα : 0 ≤ α) (Q : Matrix T T ℝ) (β : E)
    (z : (T → E) × (T → ℝ)) :
    HasFDerivAt (fun b => countGEEScore Q α b z)
      (∑ s, ∑ t, (countGEECoeff Q α β z.1 s t • -(countMean β z.1 t • innerSL ℝ (z.1 t)) +
        (z.2 t - countMean β z.1 t) • fderiv ℝ (fun b => countGEECoeff Q α b z.1 s t) β
          ).smulRight (z.1 s)) β := by
  unfold countGEEScore
  refine HasFDerivAt.fun_sum fun s _ => HasFDerivAt.fun_sum fun t _ => ?_
  refine HasFDerivAt.smul_const ?_ (z.1 s)
  exact (differentiableAt_countGEECoeff hα Q β z.1 s t).hasFDerivAt.fun_mul
    ((hasFDerivAt_countMean β z.1 t).const_sub (z.2 t))

/-- The Jacobian of the count GEE score: a residual-weighted term minus the model-based
information `Dᵀ V⁻¹ D`. -/
theorem fderiv_countGEEScore {α : ℝ} (hα : 0 ≤ α) (Q : Matrix T T ℝ) (β : E)
    (z : (T → E) × (T → ℝ)) :
    fderiv ℝ (fun b => countGEEScore Q α b z) β =
      ∑ s, ∑ t, (z.2 t - countMean β z.1 t) •
        (fderiv ℝ (fun b => countGEECoeff Q α b z.1 s t) β).smulRight (z.1 s) -
      countGEEInfo Q α β z.1 := by
  rw [(hasFDerivAt_countGEEScore hα Q β z).fderiv, countGEEInfo, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ext h
  simp only [ContinuousLinearMap.smulRight_apply, add_apply, sub_apply, smul_apply, neg_apply,
    innerSL_apply_apply, smul_eq_mul]
  module

/-! ### The meat under a correct working covariance -/

/-- The second moment of a linear combination of residuals is the quadratic form of their
second-moment matrix. -/
theorem integral_sum_sub_mul_sq {ν : Measure (T → ℝ)} [IsFiniteMeasure ν] {c ℓ : T → ℝ}
    (hL2 : ∀ t, MemLp (fun y : T → ℝ => y t) 2 ν) :
    ∫ y, (∑ t, (y t - c t) * ℓ t) ^ 2 ∂ν =
      ∑ t, ∑ t', ℓ t * ℓ t' * ∫ y, (y t - c t) * (y t' - c t') ∂ν := by
  have hr : ∀ t, MemLp (fun y : T → ℝ => y t - c t) 2 ν := fun t =>
    (hL2 t).sub (memLp_const _)
  have hprod : ∀ t t', Integrable (fun y : T → ℝ => (y t - c t) * (y t' - c t')) ν :=
    fun t t' => (hr t).integrable_mul (hr t')
  have hexp : ∀ y : T → ℝ, (∑ t, (y t - c t) * ℓ t) ^ 2 =
      ∑ t, ∑ t', ℓ t * ℓ t' * ((y t - c t) * (y t' - c t')) := by
    intro y
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ =>
    (hprod t t').const_mul _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_finsetSum _ fun t' _ => (hprod t t').const_mul _]
  exact Finset.sum_congr rfl fun t' _ => integral_const_mul _ _

/-- **Meat equals bread for a correct working covariance (one cluster).** Fix covariates `x`
and let `ν` be the conditional law of the counts. If the second moments of the counts about the
model mean are those of the NB working covariance,
`∫ (y_s - μ_s) (y_t - μ_t) dν = v(μ_s)^{1/2} v(μ_t)^{1/2} R_st`, and `Q R = 1` (so `V⁻¹` is the
inverse of this covariance), then `∫ ⟪ψ, u⟫² dν = ⟪Dᵀ V⁻¹ D u, u⟫`. -/
theorem integral_inner_countGEEScore_sq [DecidableEq T] {α : ℝ} (hα : 0 ≤ α)
    (Q R : Matrix T T ℝ) (hQR : Q * R = 1) (β : E) (x : T → E) {ν : Measure (T → ℝ)}
    [IsFiniteMeasure ν]
    (hL2 : ∀ t, MemLp (fun y : T → ℝ => y t) 2 ν)
    (hcov : ∀ s t, ∫ y, (y s - countMean β x s) * (y t - countMean β x t) ∂ν =
      √(nbVariance α (countMean β x s)) * √(nbVariance α (countMean β x t)) * R s t)
    (u : E) :
    ∫ y, ⟪countGEEScore Q α β (x, y), u⟫ ^ 2 ∂ν = ⟪countGEEInfo Q α β x u, u⟫ := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : T → ℝ, ℓ = fun t => ∑ s, countGEECoeff Q α β x s t * ⟪x s, u⟫ :=
    ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : T → ℝ,
      z = fun s => nbInvSqrtVar α β x s * countMean β x s * ⟪x s, u⟫ := ⟨_, rfl⟩
  have hin : ∀ y : T → ℝ,
      ⟪countGEEScore Q α β (x, y), u⟫ = ∑ t, (y t - countMean β x t) * ℓ t := by
    intro y
    rw [inner_countGEEScore_eq, hℓ]
  have hℓσ : ∀ t, ℓ t * √(nbVariance α (countMean β x t)) = (z ᵥ* Q) t := by
    intro t
    have h1 := sqrt_nbVariance_mul_nbInvSqrtVar hα β x t
    simp only [hℓ, hz, Matrix.vecMul, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold countGEECoeff
    linear_combination (Q s t * nbInvSqrtVar α β x s * countMean β x s * ⟪x s, u⟫) * h1
  have hinfo : ⟪countGEEInfo Q α β x u, u⟫ = z ⬝ᵥ (z ᵥ* Q) := by
    rw [countGEEInfo_apply]
    simp only [sum_inner, real_inner_smul_left, hz, Matrix.vecMul, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    unfold countGEECoeff
    ring
  simp_rw [hin]
  rw [integral_sum_sub_mul_sq hL2, hinfo]
  simp_rw [hcov]
  have h1 : ∑ t, ∑ t', ℓ t * ℓ t' * (√(nbVariance α (countMean β x t)) *
      √(nbVariance α (countMean β x t')) * R t t') = (z ᵥ* Q) ⬝ᵥ (R *ᵥ (z ᵥ* Q)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    rw [← hℓσ t, ← hℓσ t']
    ring
  rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hQR, Matrix.vecMul_one]

/-! ### Unbiasedness -/

variable [MeasurableSpace E] [FiniteDimensional ℝ E]

/-- A sum of conditionally centered residuals times covariate-only weights has mean zero under
`μx ⊗ₘ κ`: if `∫ y_t d(κ x) = m x t` for `μx`-almost every `x`, then
`∫ ∑_t (y_t - m x t) • G t x = 0`. No measurability of `G` is needed beyond the joint
integrability of the sum. -/
theorem integral_sum_residual_smul_compProd_eq_zero {X : Type*} [MeasurableSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {μx : Measure X}
    [SFinite μx]
    {κ : Kernel X (T → ℝ)} [IsMarkovKernel κ] {m : X → T → ℝ} {G : T → X → F}
    (hy : ∀ᵐ x ∂μx, ∀ t, Integrable (fun y : T → ℝ => y t) (κ x) ∧ ∫ y, y t ∂κ x = m x t)
    (hint : Integrable (fun z : X × (T → ℝ) => ∑ t, (z.2 t - m z.1 t) • G t z.1) (μx ⊗ₘ κ)) :
    ∫ z, ∑ t, (z.2 t - m z.1 t) • G t z.1 ∂(μx ⊗ₘ κ) = 0 := by
  rw [Measure.integral_compProd hint, show (0 : F) = ∫ _ : X, (0 : F) ∂μx by simp]
  refine integral_congr_ae ?_
  filter_upwards [hy] with x hx
  have hi : ∀ t ∈ Finset.univ, Integrable (fun y : T → ℝ => (y t - m x t) • G t x) (κ x) :=
    fun t _ => ((hx t).1.sub (integrable_const (m x t))).smul_const (G t x)
  rw [integral_finsetSum _ hi]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [integral_smul_const, integral_sub (hx t).1 (integrable_const _), (hx t).2, integral_const]
  simp

/-- **Unbiasedness of the count GEE.** If the log-link conditional mean is correct at `β₀`,
`E[y_t | x] = exp ⟪x t, β₀⟫`, then the count GEE score has mean zero at `β₀`, for every
dispersion `α` and every inverse working correlation `Q`. -/
theorem integral_countGEEScore_eq_zero {μx : Measure (T → E)} [SFinite μx]
    {κ : Kernel (T → E) (T → ℝ)} [IsMarkovKernel κ] (Q : Matrix T T ℝ) (α : ℝ) {β₀ : E}
    (hy : ∀ᵐ x ∂μx, ∀ t, Integrable (fun y : T → ℝ => y t) (κ x) ∧
      ∫ y, y t ∂κ x = countMean β₀ x t)
    (hint : Integrable (countGEEScore Q α β₀) (μx ⊗ₘ κ)) :
    ∫ z, countGEEScore Q α β₀ z ∂(μx ⊗ₘ κ) = 0 := by
  have h := integral_sum_residual_smul_compProd_eq_zero (m := fun x t => countMean β₀ x t)
    (G := fun t x => ∑ s, countGEECoeff Q α β₀ x s t • x s) hy
    (hint.congr (ae_of_all _ fun z => countGEEScore_eq_sum_residual Q α β₀ z))
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun z => countGEEScore_eq_sum_residual Q α β₀ z)

/-! ### The bread -/

/-- **The bread of the count GEE.** Under a correct log-link conditional mean, the expected
Jacobian of the score at `β₀` is minus the expected model-based information:
`E ∂ψ(β₀)/∂β = -E[Dᵀ V⁻¹ D]`. -/
theorem integral_fderiv_countGEEScore {α : ℝ} (hα : 0 ≤ α) {μx : Measure (T → E)} [SFinite μx]
    {κ : Kernel (T → E) (T → ℝ)} [IsMarkovKernel κ] (Q : Matrix T T ℝ) {β₀ : E}
    (hy : ∀ᵐ x ∂μx, ∀ t, Integrable (fun y : T → ℝ => y t) (κ x) ∧
      ∫ y, y t ∂κ x = countMean β₀ x t)
    (hint : Integrable (fun z => fderiv ℝ (fun b => countGEEScore Q α b z) β₀) (μx ⊗ₘ κ))
    (hinfo : Integrable (fun z : (T → E) × (T → ℝ) => countGEEInfo Q α β₀ z.1) (μx ⊗ₘ κ)) :
    ∫ z, fderiv ℝ (fun b => countGEEScore Q α b z) β₀ ∂(μx ⊗ₘ κ) =
      -∫ z, countGEEInfo Q α β₀ z.1 ∂(μx ⊗ₘ κ) := by
  set G : T → (T → E) → E →L[ℝ] E := fun t x =>
    ∑ s, (fderiv ℝ (fun b => countGEECoeff Q α b x s t) β₀).smulRight (x s) with hG
  have hdec : ∀ z : (T → E) × (T → ℝ), fderiv ℝ (fun b => countGEEScore Q α b z) β₀ =
      (∑ t, (z.2 t - countMean β₀ z.1 t) • G t z.1) - countGEEInfo Q α β₀ z.1 := by
    intro z
    rw [fderiv_countGEEScore hα, Finset.sum_comm]
    simp only [hG, Finset.smul_sum]
  have hR : Integrable (fun z : (T → E) × (T → ℝ) =>
      ∑ t, (z.2 t - countMean β₀ z.1 t) • G t z.1) (μx ⊗ₘ κ) :=
    (hint.add hinfo).congr (ae_of_all _ fun z => by
      simp only [Pi.add_apply]
      rw [hdec z, sub_add_cancel])
  have h0 := integral_sum_residual_smul_compProd_eq_zero (m := fun x t => countMean β₀ x t)
    (G := G) hy hR
  calc ∫ z, fderiv ℝ (fun b => countGEEScore Q α b z) β₀ ∂(μx ⊗ₘ κ)
      = ∫ z, ((∑ t, (z.2 t - countMean β₀ z.1 t) • G t z.1) - countGEEInfo Q α β₀ z.1)
          ∂(μx ⊗ₘ κ) := integral_congr_ae (ae_of_all _ hdec)
    _ = -∫ z, countGEEInfo Q α β₀ z.1 ∂(μx ⊗ₘ κ) := by
      rw [integral_sub hR hinfo, h0, zero_sub]


/-- **Meat equals bread for a correct working covariance.** Integrated over the covariates:
`E ⟪ψ(β₀), u⟫² = ⟪E[Dᵀ V⁻¹ D] u, u⟫` when the conditional second moments about the model mean
are those of the NB working covariance with correlation `R = Q⁻¹`. -/
theorem integral_inner_countGEEScore_sq_compProd [DecidableEq T] {α : ℝ} (hα : 0 ≤ α)
    (Q R : Matrix T T ℝ) (hQR : Q * R = 1) {β₀ : E} {μx : Measure (T → E)} [SFinite μx]
    {κ : Kernel (T → E) (T → ℝ)} [IsMarkovKernel κ]
    (hL2 : ∀ᵐ x ∂μx, ∀ t, MemLp (fun y : T → ℝ => y t) 2 (κ x))
    (hcov : ∀ᵐ x ∂μx, ∀ s t,
      ∫ y, (y s - countMean β₀ x s) * (y t - countMean β₀ x t) ∂κ x =
        √(nbVariance α (countMean β₀ x s)) * √(nbVariance α (countMean β₀ x t)) * R s t)
    (u : E) (hint : Integrable (fun z => ⟪countGEEScore Q α β₀ z, u⟫ ^ 2) (μx ⊗ₘ κ))
    (hinfo : Integrable (fun z : (T → E) × (T → ℝ) => countGEEInfo Q α β₀ z.1) (μx ⊗ₘ κ)) :
    ∫ z, ⟪countGEEScore Q α β₀ z, u⟫ ^ 2 ∂(μx ⊗ₘ κ) =
      ⟪(∫ z, countGEEInfo Q α β₀ z.1 ∂(μx ⊗ₘ κ)) u, u⟫ := by
  have hu : Integrable (fun z : (T → E) × (T → ℝ) => countGEEInfo Q α β₀ z.1 u) (μx ⊗ₘ κ) :=
    hinfo.apply_continuousLinearMap u
  calc ∫ z, ⟪countGEEScore Q α β₀ z, u⟫ ^ 2 ∂(μx ⊗ₘ κ)
      = ∫ z, ⟪countGEEInfo Q α β₀ z.1 u, u⟫ ∂(μx ⊗ₘ κ) := by
        rw [Measure.integral_compProd hint, Measure.integral_compProd (hu.inner_const u)]
        refine integral_congr_ae ?_
        filter_upwards [hL2, hcov] with x hx hc
        rw [integral_inner_countGEEScore_sq hα Q R hQR β₀ x hx hc u]
        simp
    _ = ⟪(∫ z, countGEEInfo Q α β₀ z.1 ∂(μx ⊗ₘ κ)) u, u⟫ := by
        rw [ContinuousLinearMap.integral_apply hinfo u, real_inner_comm u,
          ← integral_inner hu u]
        exact integral_congr_ae (ae_of_all _ fun z => real_inner_comm _ _)

/-! ### Sandwich asymptotic normality -/

theorem ringInverse_neg {R : Type*} [Ring R] (a : R) : Ring.inverse (-a) = -Ring.inverse a := by
  by_cases h : IsUnit a
  · have hn : IsUnit (-a) := h.neg
    calc Ring.inverse (-a) = Ring.inverse (-a) * (-a * -Ring.inverse a) := by
          rw [neg_mul_neg, Ring.mul_inverse_cancel a h, mul_one]
      _ = -Ring.inverse a := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hn, one_mul]
  · have hn : ¬IsUnit (-a) := fun hn => h (by simpa using hn.neg)
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ hn, neg_zero]

variable [BorelSpace E]

theorem measurable_countGEEScore (Q : Matrix T T ℝ) (α : ℝ) (β : E) :
    Measurable (countGEEScore Q α β) := by
  unfold countGEEScore countGEECoeff nbInvSqrtVar countMean nbVariance
  fun_prop

/-- **Asymptotic normality of the count GEE with the sandwich covariance.** Clusters
`X i = (x, y)` are i.i.d. with law `μx ⊗ₘ κ`, the log-link conditional mean is correct at
`β₀`, and the working covariance is the NB2 one with dispersion `α ≥ 0` and an arbitrary
inverse working correlation `Q` (it need not be correct). Let `A = E[Dᵀ V⁻¹ D]` be the bread,
assumed nonsingular, and let `β̂ₙ` be a consistent root of `∑_{i<n} ψ(β; X i) = 0` with
probability tending to one. Under the moment and envelope conditions of the i.i.d. Z-estimator
theorem, `√n (β̂ₙ - β₀) → A⁻¹ Y` in distribution, where `⟪Y, t⟫ ~ N(0, E ⟪ψ(β₀), t⟫²)`: the
limiting covariance is the sandwich `A⁻¹ B A⁻ᵀ`, `B = E[ψ(β₀) ψ(β₀)ᵀ]`.

This is `VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation` applied
to `countGEEScore`, with differentiability, measurability, centering and the bread
identification `E ∂ψ(β₀)/∂β = -A` proved here. -/
theorem tendstoInDistribution_sqrt_smul_sub_countGEE
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {μx : Measure (T → E)} [IsProbabilityMeasure μx] {κ : Kernel (T → E) (T → ℝ)}
    [IsMarkovKernel κ] {X : ℕ → Ω → (T → E) × (T → ℝ)}
    (hX_law : ∀ i, HasLaw (X i) (μx ⊗ₘ κ) P) (hX_indep : iIndepFun X P)
    {Q : Matrix T T ℝ} {α : ℝ} (hα : 0 ≤ α) {β₀ : E}
    (hy : ∀ᵐ x ∂μx, ∀ t, Integrable (fun y : T → ℝ => y t) (κ x) ∧
      ∫ y, y t ∂κ x = countMean β₀ x t)
    {δ : ℝ} (hδ : 0 < δ) {M : (T → E) × (T → ℝ) → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (μx ⊗ₘ κ))
    (hM : ∀ z, ∀ β ∈ Metric.ball β₀ δ,
      ‖fderiv ℝ (fun b => countGEEScore Q α b z) β -
        fderiv ℝ (fun b => countGEEScore Q α b z) β₀‖ ≤ M z * ‖β - β₀‖)
    (hψ_sq : Integrable (fun z => ‖countGEEScore Q α β₀ z‖ ^ 2) (μx ⊗ₘ κ))
    (hψ'_meas : StronglyMeasurable fun z => fderiv ℝ (fun b => countGEEScore Q α b z) β₀)
    (hψ'_int : Integrable (fun z => fderiv ℝ (fun b => countGEEScore Q α b z) β₀) (μx ⊗ₘ κ))
    (hinfo : Integrable (fun z : (T → E) × (T → ℝ) => countGEEInfo Q α β₀ z.1) (μx ⊗ₘ κ))
    (hA : IsUnit (∫ z, countGEEInfo Q α β₀ z.1 ∂(μx ⊗ₘ κ)))
    {βhat : ℕ → Ω → E} (hβ_meas : ∀ n, AEMeasurable (βhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, countGEEScore Q α (βhat n ω) (X i ω)
      ≠ 0}) atTop (𝓝 0))
    (hcons : TendstoInMeasure P βhat atTop (fun _ => β₀))
    {Y : Ω' → E} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ z, ⟪countGEEScore Q α β₀ z, t⟫ ^ 2 ∂(μx ⊗ₘ κ)).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (βhat n ω - β₀)) atTop
      (fun ω => Ring.inverse (∫ z, countGEEInfo Q α β₀ z.1 ∂(μx ⊗ₘ κ)) (Y ω))
      (fun _ => P) P' := by
  have hψ_meas := measurable_countGEEScore (T := T) Q α β₀
  have hψ_int : Integrable (countGEEScore Q α β₀) (μx ⊗ₘ κ) :=
    ((memLp_two_iff_integrable_sq_norm hψ_meas.aestronglyMeasurable).2 hψ_sq).integrable
      one_le_two
  have hbread := integral_fderiv_countGEEScore hα Q hy hψ'_int hinfo
  have h := VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation
    (ψ := countGEEScore Q α) hX_law hX_indep hδ
    (fun z β _ => (hasFDerivAt_countGEEScore hα Q β z).differentiableAt) hM_meas hM_int hM
    hψ_meas hψ_sq (integral_countGEEScore_eq_zero Q α hy hψ_int) hψ'_meas hψ'_int
    (by rw [hbread]; exact hA.neg) hβ_meas hroot hcons hY_meas hY
  rw [hbread, ringInverse_neg] at h
  simpa only [neg_apply, neg_neg] using h

/-- **Model-based limit under a correct NB working covariance.** If, in addition, the
conditional second moments of the counts about the model mean are those of the NB working
covariance, `v(μ_s)^{1/2} v(μ_t)^{1/2} R_st` with `Q R = 1`, then the meat equals the bread `A`
and `√n (β̂ₙ - β₀) → A⁻¹ Y` with `⟪Y, t⟫ ~ N(0, ⟪A t, t⟫)`: the sandwich `A⁻¹ A A⁻ᵀ` is the
model-based covariance `A⁻¹`, since the second-moment hypothesis forces `R`, hence `Q` and `A`,
to be symmetric. -/
theorem tendstoInDistribution_sqrt_smul_sub_countGEE_modelBased [DecidableEq T]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {μx : Measure (T → E)} [IsProbabilityMeasure μx] {κ : Kernel (T → E) (T → ℝ)}
    [IsMarkovKernel κ] {X : ℕ → Ω → (T → E) × (T → ℝ)}
    (hX_law : ∀ i, HasLaw (X i) (μx ⊗ₘ κ) P) (hX_indep : iIndepFun X P)
    {Q R : Matrix T T ℝ} (hQR : Q * R = 1) {α : ℝ} (hα : 0 ≤ α) {β₀ : E}
    (hy : ∀ᵐ x ∂μx, ∀ t, Integrable (fun y : T → ℝ => y t) (κ x) ∧
      ∫ y, y t ∂κ x = countMean β₀ x t)
    (hL2 : ∀ᵐ x ∂μx, ∀ t, MemLp (fun y : T → ℝ => y t) 2 (κ x))
    (hcov : ∀ᵐ x ∂μx, ∀ s t,
      ∫ y, (y s - countMean β₀ x s) * (y t - countMean β₀ x t) ∂κ x =
        √(nbVariance α (countMean β₀ x s)) * √(nbVariance α (countMean β₀ x t)) * R s t)
    {δ : ℝ} (hδ : 0 < δ) {M : (T → E) × (T → ℝ) → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (μx ⊗ₘ κ))
    (hM : ∀ z, ∀ β ∈ Metric.ball β₀ δ,
      ‖fderiv ℝ (fun b => countGEEScore Q α b z) β -
        fderiv ℝ (fun b => countGEEScore Q α b z) β₀‖ ≤ M z * ‖β - β₀‖)
    (hψ_sq : Integrable (fun z => ‖countGEEScore Q α β₀ z‖ ^ 2) (μx ⊗ₘ κ))
    (hψ'_meas : StronglyMeasurable fun z => fderiv ℝ (fun b => countGEEScore Q α b z) β₀)
    (hψ'_int : Integrable (fun z => fderiv ℝ (fun b => countGEEScore Q α b z) β₀) (μx ⊗ₘ κ))
    (hinfo : Integrable (fun z : (T → E) × (T → ℝ) => countGEEInfo Q α β₀ z.1) (μx ⊗ₘ κ))
    (hA : IsUnit (∫ z, countGEEInfo Q α β₀ z.1 ∂(μx ⊗ₘ κ)))
    {βhat : ℕ → Ω → E} (hβ_meas : ∀ n, AEMeasurable (βhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, countGEEScore Q α (βhat n ω) (X i ω)
      ≠ 0}) atTop (𝓝 0))
    (hcons : TendstoInMeasure P βhat atTop (fun _ => β₀))
    {Y : Ω' → E} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (⟪(∫ z, countGEEInfo Q α β₀ z.1 ∂(μx ⊗ₘ κ)) t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (βhat n ω - β₀)) atTop
      (fun ω => Ring.inverse (∫ z, countGEEInfo Q α β₀ z.1 ∂(μx ⊗ₘ κ)) (Y ω))
      (fun _ => P) P' := by
  have hψ_meas := measurable_countGEEScore (T := T) Q α β₀
  have hsq : ∀ t, Integrable (fun z => ⟪countGEEScore Q α β₀ z, t⟫ ^ 2) (μx ⊗ₘ κ) := by
    intro t
    refine (hψ_sq.mul_const (‖t‖ ^ 2)).mono'
      ((hψ_meas.inner measurable_const).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    calc ‖⟪countGEEScore Q α β₀ z, t⟫ ^ 2‖ = |⟪countGEEScore Q α β₀ z, t⟫| ^ 2 := by
          rw [Real.norm_eq_abs, abs_pow]
      _ ≤ (‖countGEEScore Q α β₀ z‖ * ‖t‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
      _ = ‖countGEEScore Q α β₀ z‖ ^ 2 * ‖t‖ ^ 2 := mul_pow _ _ _
  refine tendstoInDistribution_sqrt_smul_sub_countGEE hX_law hX_indep hα hy hδ hM_meas hM_int
    hM hψ_sq hψ'_meas hψ'_int hinfo hA hβ_meas hroot hcons hY_meas fun t => ?_
  rw [integral_inner_countGEEScore_sq_compProd hα Q R hQR hL2 hcov t (hsq t) hinfo]
  exact hY t

end MathlibExt.Probability.Statistics.Longitudinal.GEE.CountGEE
