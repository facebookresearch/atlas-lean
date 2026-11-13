/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.NegativeBinomialDispersion
public import MathlibExt.Probability.Statistics.EstimatedInformation
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Asymptotic normality of the joint negative binomial MLE

`NegativeBinomialDispersion` estimates the shape `θ` (the `k` of the NB2 variance `μ + μ² / k`)
jointly with the coefficients `β` of the log-link negative binomial regression, and proves
consistency of the joint estimator. This file proves its asymptotic normality and the Wald,
score and likelihood-ratio limits with the shape estimated, for i.i.d. observations
`(xᵢ, yᵢ)` (random design, no offset).

The model is a family of densities on `(κ → ℝ) × ℕ` indexed by the Euclidean parameter space
`NBParam κ = EuclideanSpace ℝ (κ ⊕ Unit)`: `nbRegDensity (β, θ) (x, y) = NB(y; θ, exp (x ⬝ᵥ β))`.
With respect to the reference measure `μX ⊗ count`, where `μX` is the law of the covariates,
`lawOf (μX.prod Measure.count) nbRegDensity p` (shape `θ > 0`) is the law of random-design
negative binomial regression: covariates of law `μX` and counts that are conditionally
`NB(θ, exp (x ⬝ᵥ β))`. The generic theorems of `VectorInference` and `EstimatedInformation` are
first instantiated for an arbitrary reference measure `ν`. Those are generic weighted-density
results: for other `ν` the law `lawOf ν nbRegDensity p` need not be negative binomial. Each
asymptotic result is then restated for negative binomial regression, `ν = μX ⊗ count` (the
`..._randomDesign` theorems).

## Proved model facts (no hypotheses beyond `θ > 0`)

* `score_nbRegDensity`, `hasGradientAt_log_nbRegDensity`: the score of the family is the closed
  form `nbRegScore`, built from `nbScore` and `nbShapeScore` of `hasFDerivAt_nbLogPmf`.
* `hasFDerivAt_score_nbRegDensity`: the derivative of the score is minus `nbRegObsInfo`, the
  operator of the merged `nbObsInfoRow`. So the differentiability conditions of `VectorInference`
  hold on any ball of radius `δ ≤ θ₀` and are not assumed.
* `observedInformation_nbRegDensity`, `nbRegAvgObsInfo_eq_nbJointObsInfo`: the generic observed
  information is `n⁻¹ • nbJointObsInfo` of the `n`-row design.
* `inner_nbRegFisherInfo_nbShapeVec_nbCoefIncl`: under the information identity, the cross
  information between `β` and `θ` vanishes (covariate average of
  `hasSum_nbCross_mul_negBinomialReal`); `inner_nbCoefBlock_nbRegFisherInfo`: the coefficient
  block is `E_x[F(θ₀, x ⬝ᵥ β₀) x xᵀ]`, the known-shape information.
* `inverse_apply_nbCoefIncl_of_cross`: with vanishing cross information, the coefficient block of
  `I⁻¹` is the inverse of the coefficient block of `I`.

## Asymptotic results

For negative binomial regression (reference measure `μX ⊗ count`):

* `tendstoInDistribution_sqrt_smul_sub_nbJointMLE_randomDesign`: `√n (p̂ - p₀) → N(0, I(p₀)⁻¹)`.
* `tendstoInDistribution_waldStatistic_nbJointMLE_randomDesign`, `..._obsInfo_randomDesign`:
  joint Wald statistic with an estimated information (any consistent one, or the observed
  information at `p̂`) `→ χ²_{|κ|+1}`; `tendstoInMeasure_nbRegAvgObsInfo_randomDesign`:
  consistency of that observed information.
* `tendstoInDistribution_scoreStatistic_nbJointMLE_randomDesign`: Rao's statistic
  `→ χ²_{|κ|+1}`.
* `tendstoInDistribution_two_mul_logLik_sub_nbJointMLE_randomDesign`: Wilks, simple null,
  `→ χ²_{|κ|+1}`.
* `tendstoInDistribution_coefWaldStatistic_nbJointMLE_randomDesign` and
  `tendstoInDistribution_coefWaldStatistic_nbJointMLE_obsInfo` (cross condition proved;
  observed-information block): the Wald statistic for `β` alone, with `θ` estimated as a nuisance
  parameter, `→ χ²_{|κ|}`.

The generic weighted-density versions, for an arbitrary reference measure `ν`, are the same names
without `_randomDesign`: `tendstoInDistribution_sqrt_smul_sub_nbJointMLE`,
`tendstoInDistribution_waldStatistic_nbJointMLE`, `..._obsInfo`,
`tendstoInMeasure_nbRegAvgObsInfo`, `tendstoInDistribution_scoreStatistic_nbJointMLE`,
`tendstoInDistribution_two_mul_logLik_sub_nbJointMLE`, and
`tendstoInDistribution_coefWaldStatistic_nbJointMLE`, which takes the vanishing cross information
as a hypothesis.

## Hypotheses and what is not proved

* As in `VectorInference`, the following are hypotheses: the Lipschitz envelope `M` on
  `nbRegObsInfo` near `p₀`, square integrability and centering of the score, integrability of the
  observed information and the information identity `E[nbRegObsInfo p₀] = I(p₀)`, positive
  definiteness of `I(p₀)`, and that `p̂` is consistent and solves the likelihood equation with
  probability tending to one. Consistency follows from `tendstoInMeasure_nbJointMLE` under its
  own explicit hypotheses. The Bartlett identities for the shape need differentiation under the
  negative binomial series and are not derived (the merged file defers them for the same reason).
* Only simple nulls are covered for the score and likelihood-ratio statistics. Composite score and
  likelihood-ratio tests for `β` with `θ` free need the restricted MLE and are not proved; for
  `β` alone only the Wald statistic is covered.
* Covariates are random and i.i.d.; fixed designs and offsets are not covered.
* Interior points only (`θ₀ > 0`); the boundary `θ = ∞` (Poisson) is not covered.

## References

* J. F. Lawless, "Negative binomial and mixed Poisson regression", Canad. J. Statist. 15 (1987)
  209–225, §2 (joint maximum likelihood for `(β, k)`; `β̂` and `k̂` are asymptotically
  independent).
* A. C. Cameron and P. K. Trivedi, *Regression Analysis of Count Data*, 2nd ed. (2013), §3.3
  (NB2 maximum likelihood and its asymptotic distribution).
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 5.41 and ch. 16.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM.NegativeBinomial

open Finset Real Matrix ProbabilityTheory MeasureTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.VectorInference
  (score fisherInformation)
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### The random-design model in `(β, θ)` -/

/-- The joint parameter `(β, θ)` of the negative binomial regression as a vector of the Euclidean
space indexed by `κ ⊕ Unit`: `Sum.inl j` is the coefficient `βⱼ`, `Sum.inr ()` is the shape `θ`
(the `k` of the NB2 variance `μ + μ² / k`). -/
abbrev NBParam (κ : Type*) := EuclideanSpace ℝ (κ ⊕ Unit)

/-- The coefficient block `β` of a joint parameter. -/
def nbParamCoef (p : NBParam κ) : κ → ℝ := fun j => p (Sum.inl j)

/-- The shape coordinate `θ` of a joint parameter. -/
def nbParamShape (p : NBParam κ) : ℝ := p (Sum.inr ())

/-- The density of one observation `z = (x, y)` (covariate row `x`, count `y`) of the log-link
negative binomial regression with joint parameter `p = (β, θ)`, with respect to
`(law of x) ⊗ (counting measure)`: the conditional mass `NB(y; θ, exp (x ⬝ᵥ β))`. -/
noncomputable def nbRegDensity (p : NBParam κ) (z : (κ → ℝ) × ℕ) : ℝ :=
  negBinomialReal (nbParamShape p) (exp (z.1 ⬝ᵥ nbParamCoef p)) z.2

/-- The joint score vector of one observation `z = (x, y)` in closed form: `nbScore θ y η • x` in
the coefficient block and `nbShapeScore θ y η` in the shape coordinate, `η = x ⬝ᵥ β`. -/
noncomputable def nbRegScore (p : NBParam κ) (z : (κ → ℝ) × ℕ) : NBParam κ :=
  WithLp.toLp 2 (Sum.elim
    (fun j => nbScore (nbParamShape p) z.2 (z.1 ⬝ᵥ nbParamCoef p) * z.1 j)
    (fun _ => nbShapeScore (nbParamShape p) z.2 (z.1 ⬝ᵥ nbParamCoef p)))

/-- The observed information operator of one observation `z = (x, y)`: the matrix
`nbObsInfoRow θ x y η` of `NegativeBinomialDispersion` acting on `NBParam κ`. -/
noncomputable def nbRegObsInfo (p : NBParam κ) (z : (κ → ℝ) × ℕ) : NBParam κ →L[ℝ] NBParam κ :=
  toEuclideanCLM (𝕜 := ℝ) (nbObsInfoRow (nbParamShape p) z.1 z.2 (z.1 ⬝ᵥ nbParamCoef p))

/-- The linear map `p ↦ (θ, x ⬝ᵥ β)` that feeds `nbLogPmf`. -/
noncomputable def nbPredictorCLM (x : κ → ℝ) : NBParam κ →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (Sum.inr ())).prod
    (∑ j, x j • EuclideanSpace.proj (𝕜 := ℝ) (Sum.inl j : κ ⊕ Unit))

omit [DecidableEq κ] in
theorem nbPredictorCLM_apply (x : κ → ℝ) (p : NBParam κ) :
    nbPredictorCLM x p = (nbParamShape p, x ⬝ᵥ nbParamCoef p) := by
  simp [nbPredictorCLM, nbParamShape, nbParamCoef, dotProduct]

omit [Fintype κ] [DecidableEq κ] in
theorem continuous_nbParamShape : Continuous (nbParamShape : NBParam κ → ℝ) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inr () : κ ⊕ Unit)).continuous

omit [DecidableEq κ] in
/-- Near a parameter with positive shape, the log density is `nbLogPmf` of the predictor. -/
theorem log_nbRegDensity_eventuallyEq {p : NBParam κ} (hp : 0 < nbParamShape p)
    (z : (κ → ℝ) × ℕ) :
    (fun t => Real.log (nbRegDensity t z)) =ᶠ[𝓝 p]
      fun t => nbLogPmf (nbPredictorCLM z.1 t).1 z.2 (nbPredictorCLM z.1 t).2 := by
  filter_upwards [continuous_nbParamShape.continuousAt.eventually (lt_mem_nhds hp)] with t ht
  rw [nbPredictorCLM_apply, nbRegDensity, log_negBinomialReal_exp_eq_nbLogPmf ht]

omit [DecidableEq κ] in
private theorem inner_nbRegScore (p : NBParam κ) (z : (κ → ℝ) × ℕ) (u : NBParam κ) :
    ⟪nbRegScore p z, u⟫ = nbShapeScore (nbParamShape p) z.2 (z.1 ⬝ᵥ nbParamCoef p) *
        nbParamShape u +
      nbScore (nbParamShape p) z.2 (z.1 ⬝ᵥ nbParamCoef p) * (z.1 ⬝ᵥ nbParamCoef u) := by
  simp only [nbRegScore, PiLp.inner_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_singleton, nbParamShape, nbParamCoef, dotProduct,
    RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq κ] in
/-- **The log density has gradient `nbRegScore`.** For a positive shape, `log nbRegDensity` is
differentiable in `p = (β, θ)` with gradient the closed-form score `nbRegScore p z`, assembled from
the joint score `(nbShapeScore, nbScore)` of `hasFDerivAt_nbLogPmf`. -/
theorem hasGradientAt_log_nbRegDensity {p : NBParam κ} (hp : 0 < nbParamShape p)
    (z : (κ → ℝ) × ℕ) :
    HasGradientAt (fun t => Real.log (nbRegDensity t z)) (nbRegScore p z) p := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h0 := hasFDerivAt_nbLogPmf hp z.2 (z.1 ⬝ᵥ nbParamCoef p)
  rw [show (nbParamShape p, z.1 ⬝ᵥ nbParamCoef p) = nbPredictorCLM z.1 p from
    (nbPredictorCLM_apply _ _).symm] at h0
  have h := h0.comp p (nbPredictorCLM z.1).hasFDerivAt
  refine (h.congr_of_eventuallyEq (log_nbRegDensity_eventuallyEq hp z)).congr_fderiv ?_
  ext1 u
  rw [InnerProductSpace.toDual_apply_apply, inner_nbRegScore]
  simp [nbPredictorCLM_apply]

omit [DecidableEq κ] in
/-- **The score of the model is `nbRegScore`.** -/
theorem score_nbRegDensity {p : NBParam κ} (hp : 0 < nbParamShape p) (z : (κ → ℝ) × ℕ) :
    score nbRegDensity p z = nbRegScore p z :=
  (hasGradientAt_log_nbRegDensity hp z).gradient

omit [DecidableEq κ] in
private theorem nbObsInfoRow_mulVec_inl (θ : ℝ) (x : κ → ℝ) (y : ℕ) (η : ℝ) (u : κ ⊕ Unit → ℝ)
    (j : κ) :
    (nbObsInfoRow θ x y η *ᵥ u) (Sum.inl j) =
      nbObsWeight θ y η * x j * (x ⬝ᵥ fun l => u (Sum.inl l)) -
        nbCross θ y η * x j * u (Sum.inr ()) := by
  simp only [nbObsInfoRow, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, of_apply,
    Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum]
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun l _ => by ring
  · ring

omit [DecidableEq κ] in
private theorem nbObsInfoRow_mulVec_inr (θ : ℝ) (x : κ → ℝ) (y : ℕ) (η : ℝ) (u : κ ⊕ Unit → ℝ) :
    (nbObsInfoRow θ x y η *ᵥ u) (Sum.inr ()) =
      -(nbCross θ y η * (x ⬝ᵥ fun l => u (Sum.inl l))) +
        nbShapeObsInfo θ y η * u (Sum.inr ()) := by
  simp only [nbObsInfoRow, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, of_apply, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **The derivative of the closed-form score is minus the observed information.** For a
positive shape, `t ↦ nbRegScore t z` has derivative `-nbRegObsInfo p z` at `p`; the entries come
from `hasFDerivAt_nbScore_prod` and `hasFDerivAt_nbShapeScore`. -/
theorem hasFDerivAt_nbRegScore {p : NBParam κ} (hp : 0 < nbParamShape p) (z : (κ → ℝ) × ℕ) :
    HasFDerivAt (fun t => nbRegScore t z) (-nbRegObsInfo p z) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  have hL : (nbParamShape p, z.1 ⬝ᵥ nbParamCoef p) = nbPredictorCLM z.1 p :=
    (nbPredictorCLM_apply _ _).symm
  rintro (j | _)
  · have h0 := hasFDerivAt_nbScore_prod hp (z.2 : ℝ) (z.1 ⬝ᵥ nbParamCoef p)
    rw [hL] at h0
    have h := (h0.comp p (nbPredictorCLM z.1).hasFDerivAt).mul_const (z.1 j)
    have e : (fun t => nbRegScore t z (Sum.inl j)) =
        fun t => ((fun q : ℝ × ℝ => nbScore q.1 z.2 q.2) ∘ nbPredictorCLM z.1) t * z.1 j := by
      funext t
      simp [nbRegScore, nbPredictorCLM_apply]
    rw [e]
    refine (h.congr_fderiv ?_).hasFDerivWithinAt
    ext1 u
    simp only [nbRegObsInfo, ContinuousLinearMap.comp_apply, _root_.neg_apply,
      PiLp.proj_apply, PiLp.neg_apply, ofLp_toEuclideanCLM]
    rw [nbObsInfoRow_mulVec_inl]
    simp [nbPredictorCLM_apply, nbParamShape]
    ring_nf
    rfl
  · have h0 := hasFDerivAt_nbShapeScore hp z.2 (z.1 ⬝ᵥ nbParamCoef p)
    rw [hL] at h0
    have h := h0.comp p (nbPredictorCLM z.1).hasFDerivAt
    have e : (fun t => nbRegScore t z (Sum.inr ())) =
        (fun q : ℝ × ℝ => nbShapeScore q.1 z.2 q.2) ∘ nbPredictorCLM z.1 := by
      funext t
      simp [nbRegScore, nbPredictorCLM_apply]
    rw [e]
    refine (h.congr_fderiv ?_).hasFDerivWithinAt
    ext1 u
    simp only [nbRegObsInfo, ContinuousLinearMap.comp_apply, _root_.neg_apply,
      PiLp.proj_apply, PiLp.neg_apply, ofLp_toEuclideanCLM]
    rw [nbObsInfoRow_mulVec_inr]
    simp [nbPredictorCLM_apply, nbParamShape]
    ring_nf
    exact Or.inl rfl

omit [DecidableEq κ] in
/-- Near a parameter with positive shape, the score of the model is the closed form. -/
theorem score_nbRegDensity_eventuallyEq {p : NBParam κ} (hp : 0 < nbParamShape p)
    (z : (κ → ℝ) × ℕ) :
    (fun t => score nbRegDensity t z) =ᶠ[𝓝 p] fun t => nbRegScore t z := by
  filter_upwards [continuous_nbParamShape.continuousAt.eventually (lt_mem_nhds hp)] with t ht
  exact score_nbRegDensity ht z

/-- **The derivative of the score is minus the observed information** `nbObsInfoRow` of
`NegativeBinomialDispersion`, at every parameter with positive shape. -/
theorem hasFDerivAt_score_nbRegDensity {p : NBParam κ} (hp : 0 < nbParamShape p)
    (z : (κ → ℝ) × ℕ) :
    HasFDerivAt (fun t => score nbRegDensity t z) (-nbRegObsInfo p z) p :=
  (hasFDerivAt_nbRegScore hp z).congr_of_eventuallyEq (score_nbRegDensity_eventuallyEq hp z)

/-! ### Measurability -/

omit [DecidableEq κ] in
theorem measurable_nbRegScore (p : NBParam κ) : Measurable (nbRegScore p) := by
  refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
  refine measurable_from_prod_countable_left fun y => ?_
  refine measurable_pi_iff.2 fun a => ?_
  rcases a with j | _
  · simp only [Sum.elim_inl, nbScore]
    fun_prop
  · simp only [Sum.elim_inr, nbShapeScore]
    fun_prop

theorem measurable_nbRegObsInfo (p : NBParam κ) : Measurable (nbRegObsInfo p) := by
  have hc : Continuous fun A : Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ =>
      toEuclideanCLM (n := κ ⊕ Unit) (𝕜 := ℝ) A := by
    let L : Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ →ₗ[ℝ] (NBParam κ →L[ℝ] NBParam κ) :=
      { toFun := fun A => toEuclideanCLM (n := κ ⊕ Unit) (𝕜 := ℝ) A
        map_add' := map_add _
        map_smul' := map_smul _ }
    exact L.continuous_of_finiteDimensional
  refine hc.measurable.comp ?_
  refine measurable_from_prod_countable_left fun y => ?_
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
  rcases a with j | _ <;> rcases b with l | _ <;>
    simp only [nbObsInfoRow, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, of_apply,
      nbObsWeight, nbCross, nbShapeObsInfo] <;>
    fun_prop

omit [DecidableEq κ] in
theorem measurable_uncurry_nbRegDensity :
    Measurable (Function.uncurry (nbRegDensity (κ := κ))) := by
  have h : Measurable fun q : (NBParam κ × (κ → ℝ)) × ℕ =>
      negBinomialReal (nbParamShape q.1.1) (exp (q.1.2 ⬝ᵥ nbParamCoef q.1.1)) q.2 := by
    refine measurable_from_prod_countable_left fun k => ?_
    have hθ : Measurable fun q : NBParam κ × (κ → ℝ) => nbParamShape q.1 :=
      continuous_nbParamShape.measurable.comp measurable_fst
    have hη : Measurable fun q : NBParam κ × (κ → ℝ) => q.2 ⬝ᵥ nbParamCoef q.1 := by
      simp only [dotProduct, nbParamCoef]
      fun_prop
    have hpoch : Measurable fun q : NBParam κ × (κ → ℝ) =>
        (ascPochhammer ℝ k).eval (nbParamShape q.1) :=
      (ascPochhammer ℝ k).continuous.measurable.comp hθ
    simp only [negBinomialReal]
    exact ((hpoch.div_const _).mul ((hθ.div (hθ.add hη.exp)).pow hθ)).mul
      ((hη.exp.div (hθ.add hη.exp)).pow_const k)
  exact h.comp MeasurableEquiv.prodAssoc.symm.measurable

/-! ### Translating the regularity conditions -/

omit [DecidableEq κ] in
/-- Parameters within `θ₀` of a parameter with shape `θ₀ > 0` have positive shape. -/
theorem nbParamShape_pos_of_mem_ball {p₀ p : NBParam κ} {δ : ℝ} (hδ : δ ≤ nbParamShape p₀)
    (hp : p ∈ Metric.ball p₀ δ) : 0 < nbParamShape p := by
  have h1 : |nbParamShape p - nbParamShape p₀| ≤ ‖p - p₀‖ := by
    simpa [nbParamShape, Real.norm_eq_abs] using PiLp.norm_apply_le (p - p₀) (Sum.inr ())
  rw [Metric.mem_ball, dist_eq_norm] at hp
  linarith [neg_abs_le (nbParamShape p - nbParamShape p₀)]

omit [DecidableEq κ] in
theorem score_nbRegDensity_eq {p : NBParam κ} (hp : 0 < nbParamShape p) :
    score nbRegDensity p = nbRegScore p :=
  funext (score_nbRegDensity hp)

theorem fderiv_score_nbRegDensity {p : NBParam κ} (hp : 0 < nbParamShape p) (z : (κ → ℝ) × ℕ) :
    fderiv ℝ (fun t => score nbRegDensity t z) p = -nbRegObsInfo p z :=
  (hasFDerivAt_score_nbRegDensity hp z).fderiv

/-! ### The observed information of a sample -/

/-- The averaged observed information of the first `n` observations `zs 0, …, zs (n - 1)` at `p`:
`n⁻¹ ∑_{i<n} nbRegObsInfo p (zs i)`. It is the operator of the merged matrix
`n⁻¹ • nbJointObsInfo` of the `n`-row design (`nbRegAvgObsInfo_eq_nbJointObsInfo`). -/
noncomputable def nbRegAvgObsInfo (n : ℕ) (zs : ℕ → (κ → ℝ) × ℕ) (p : NBParam κ) :
    NBParam κ →L[ℝ] NBParam κ :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, nbRegObsInfo p (zs i)

/-- The averaged observed information is the merged `nbJointObsInfo` of the design with rows
`(zs i).1` (no offset), scaled by `n⁻¹`. -/
theorem nbRegAvgObsInfo_eq_nbJointObsInfo (n : ℕ) (zs : ℕ → (κ → ℝ) × ℕ) (p : NBParam κ) :
    nbRegAvgObsInfo n zs p = toEuclideanCLM (𝕜 := ℝ) ((n : ℝ)⁻¹ •
      nbJointObsInfo (nbParamShape p) (of fun i : Fin n => (zs i).1) 0 (fun i => (zs i).2)
        (nbParamCoef p)) := by
  rw [map_smul, nbJointObsInfo, map_sum, nbRegAvgObsInfo,
    ← Fin.sum_univ_eq_sum_range (fun i => nbRegObsInfo p (zs i)) n]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp [nbRegObsInfo, mulVec, of_apply]; rfl

/-- For a parameter with positive shape, the generic observed information
`EstimatedInformation.observedInformation` of the model is `nbRegAvgObsInfo`. -/
theorem observedInformation_nbRegDensity {p : NBParam κ} (hp : 0 < nbParamShape p) (n : ℕ)
    (zs : ℕ → (κ → ℝ) × ℕ) :
    EstimatedInformation.observedInformation nbRegDensity n zs p = nbRegAvgObsInfo n zs p := by
  simp only [EstimatedInformation.observedInformation, fderiv_score_nbRegDensity hp,
    Finset.sum_neg_distrib, smul_neg, neg_neg, nbRegAvgObsInfo]

theorem measurable_uncurry_nbRegObsInfo :
    Measurable fun q : NBParam κ × ((κ → ℝ) × ℕ) => nbRegObsInfo q.1 q.2 := by
  have hc : Continuous fun A : Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ =>
      toEuclideanCLM (n := κ ⊕ Unit) (𝕜 := ℝ) A := by
    let L : Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ →ₗ[ℝ] (NBParam κ →L[ℝ] NBParam κ) :=
      { toFun := fun A => toEuclideanCLM (n := κ ⊕ Unit) (𝕜 := ℝ) A
        map_add' := map_add _
        map_smul' := map_smul _ }
    exact L.continuous_of_finiteDimensional
  have hg : Measurable fun w : (ℝ × (κ → ℝ) × (κ → ℝ)) × ℕ =>
      nbObsInfoRow w.1.1 w.1.2.1 w.2 (w.1.2.1 ⬝ᵥ w.1.2.2) := by
    refine measurable_from_prod_countable_left fun y => ?_
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
    rcases a with j | _ <;> rcases b with l | _ <;>
      simp only [nbObsInfoRow, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, of_apply,
        nbObsWeight, nbCross, nbShapeObsInfo, dotProduct] <;>
      fun_prop
  have hφ : Measurable fun q : (NBParam κ × (κ → ℝ)) × ℕ =>
      ((nbParamShape q.1.1, q.1.2, nbParamCoef q.1.1), q.2) := by
    refine Measurable.prodMk (Measurable.prodMk
      (continuous_nbParamShape.measurable.comp (measurable_fst.comp measurable_fst))
      ((measurable_snd.comp measurable_fst).prodMk ?_)) measurable_snd
    refine measurable_pi_iff.2 fun j => ?_
    exact (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inl j : κ ⊕ Unit)).continuous.measurable.comp
      (measurable_fst.comp measurable_fst)
  have e : (fun q : NBParam κ × ((κ → ℝ) × ℕ) => nbRegObsInfo q.1 q.2) =
      ((fun A : Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ => toEuclideanCLM (n := κ ⊕ Unit) (𝕜 := ℝ) A) ∘
        ((fun w : (ℝ × (κ → ℝ) × (κ → ℝ)) × ℕ =>
          nbObsInfoRow w.1.1 w.1.2.1 w.2 (w.1.2.1 ⬝ᵥ w.1.2.2)) ∘
        fun q : (NBParam κ × (κ → ℝ)) × ℕ =>
          ((nbParamShape q.1.1, q.1.2, nbParamCoef q.1.1), q.2))) ∘
        (MeasurableEquiv.prodAssoc (α := NBParam κ) (β := κ → ℝ) (γ := ℕ)).symm := by
    funext q
    obtain ⟨p, x, y⟩ := q
    simp only [Function.comp_apply]
    rfl
  rw [e]
  exact (hc.measurable.comp (hg.comp hφ)).comp MeasurableEquiv.prodAssoc.symm.measurable

/-! ### The coefficient block

Projection onto the coefficient block, its adjoint inclusion, and the shape direction. When the
cross information between `β` and `θ` vanishes, the coefficient block of `I⁻¹` is the inverse of
the coefficient block of `I`; this is what makes inference for `β` insensitive to estimating
`θ`. -/

/-- Projection `(β, θ) ↦ β` onto the coefficient block. -/
noncomputable def nbCoefProj : NBParam κ →L[ℝ] EuclideanSpace ℝ κ :=
  (EuclideanSpace.equiv κ ℝ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun j => EuclideanSpace.proj (𝕜 := ℝ) (Sum.inl j : κ ⊕ Unit))

/-- Inclusion `β ↦ (β, 0)` of the coefficient block. -/
noncomputable def nbCoefIncl : EuclideanSpace ℝ κ →L[ℝ] NBParam κ :=
  (EuclideanSpace.equiv (κ ⊕ Unit) ℝ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun a => Sum.elim (fun j => EuclideanSpace.proj (𝕜 := ℝ) j)
      (fun _ => 0) a)

/-- The shape direction `(0, 1)`. -/
noncomputable def nbShapeVec : NBParam κ := EuclideanSpace.single (Sum.inr ()) 1

/-- The coefficient block `B = Πβ I ιβ` of an operator `I` on the joint parameter space. -/
noncomputable def nbCoefBlock (I : NBParam κ →L[ℝ] NBParam κ) :
    EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ :=
  nbCoefProj ∘L I ∘L nbCoefIncl

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem nbCoefProj_apply (v : NBParam κ) (j : κ) : nbCoefProj v j = v (Sum.inl j) := rfl

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem nbCoefIncl_apply_inl (t : EuclideanSpace ℝ κ) (j : κ) :
    nbCoefIncl t (Sum.inl j) = t j := rfl

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem nbCoefIncl_apply_inr (t : EuclideanSpace ℝ κ) (u : Unit) :
    nbCoefIncl t (Sum.inr u) = 0 := rfl

omit [DecidableEq κ] in
theorem inner_nbCoefProj (v : NBParam κ) (t : EuclideanSpace ℝ κ) :
    ⟪nbCoefProj v, t⟫ = ⟪v, nbCoefIncl t⟫ := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type]

omit [DecidableEq κ] in
theorem inner_nbCoefIncl (s t : EuclideanSpace ℝ κ) :
    ⟪nbCoefIncl s, nbCoefIncl t⟫ = ⟪s, t⟫ := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type]

omit [Fintype κ] [DecidableEq κ] in
theorem nbCoefProj_nbCoefIncl (t : EuclideanSpace ℝ κ) : nbCoefProj (nbCoefIncl t) = t := by
  ext j; simp

theorem inner_nbShapeVec (v : NBParam κ) : ⟪v, nbShapeVec⟫ = v (Sum.inr ()) := by
  simp [nbShapeVec, EuclideanSpace.inner_single_right]

omit [Fintype κ] in
/-- Every joint parameter splits into its coefficient part and its shape part. -/
theorem nbCoefIncl_nbCoefProj_add (v : NBParam κ) :
    nbCoefIncl (nbCoefProj v) + v (Sum.inr ()) • nbShapeVec = v := by
  ext (j | u)
  · simp [nbShapeVec]
  · cases u; simp [nbShapeVec]

/-- **Block-diagonal operators preserve the coefficient block.** If `I` is symmetric and the
cross term `⟪I (0, 1), (t, 0)⟫` vanishes for every `t`, then `I (u, 0) = (B u, 0)` with `B` the
coefficient block of `I`. -/
theorem apply_nbCoefIncl_of_cross {I : NBParam κ →L[ℝ] NBParam κ}
    (hI_symm : ∀ u v, ⟪I u, v⟫ = ⟪u, I v⟫)
    (hcross : ∀ t, ⟪I nbShapeVec, nbCoefIncl t⟫ = 0) (u : EuclideanSpace ℝ κ) :
    I (nbCoefIncl u) = nbCoefIncl (nbCoefBlock I u) := by
  have h0 : I (nbCoefIncl u) (Sum.inr ()) = 0 := by
    rw [← inner_nbShapeVec, hI_symm, real_inner_comm, hcross]
  conv_lhs => rw [← nbCoefIncl_nbCoefProj_add (I (nbCoefIncl u)), h0, zero_smul, add_zero]
  rfl

omit [Fintype κ] [DecidableEq κ] in
theorem nbCoefIncl_injective : Function.Injective (nbCoefIncl (κ := κ)) := fun s t h => by
  rw [← nbCoefProj_nbCoefIncl s, h, nbCoefProj_nbCoefIncl]

omit [DecidableEq κ] in
/-- The coefficient block of a positive definite operator is positive definite. -/
theorem inner_nbCoefBlock_self_pos {I : NBParam κ →L[ℝ] NBParam κ}
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪I u, u⟫) (u : EuclideanSpace ℝ κ) (hu : u ≠ 0) :
    0 < ⟪nbCoefBlock I u, u⟫ := by
  rw [nbCoefBlock, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    inner_nbCoefProj]
  exact hI_pos _ fun h => hu (nbCoefIncl_injective (by rw [h, map_zero]))

omit [DecidableEq κ] in
/-- The coefficient block of a symmetric operator is symmetric. -/
theorem inner_nbCoefBlock_comm {I : NBParam κ →L[ℝ] NBParam κ}
    (hI_symm : ∀ u v, ⟪I u, v⟫ = ⟪u, I v⟫) (u v : EuclideanSpace ℝ κ) :
    ⟪nbCoefBlock I u, v⟫ = ⟪u, nbCoefBlock I v⟫ := by
  simp only [nbCoefBlock, ContinuousLinearMap.comp_apply]
  rw [inner_nbCoefProj, hI_symm, real_inner_comm (nbCoefProj _) u, inner_nbCoefProj,
    real_inner_comm]

/-- **The coefficient block of the inverse is the inverse of the coefficient block** for a
symmetric positive definite operator with vanishing cross term:
`I⁻¹ (t, 0) = (B⁻¹ t, 0)`. -/
theorem inverse_apply_nbCoefIncl_of_cross {I : NBParam κ →L[ℝ] NBParam κ}
    (hI_symm : ∀ u v, ⟪I u, v⟫ = ⟪u, I v⟫) (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪I u, u⟫)
    (hcross : ∀ t, ⟪I nbShapeVec, nbCoefIncl t⟫ = 0) (t : EuclideanSpace ℝ κ) :
    Ring.inverse I (nbCoefIncl t) = nbCoefIncl (Ring.inverse (nbCoefBlock I) t) := by
  have hI : IsUnit I := VectorInference.isUnit_of_inner_self_pos hI_pos
  have hB : IsUnit (nbCoefBlock I) :=
    VectorInference.isUnit_of_inner_self_pos (inner_nbCoefBlock_self_pos hI_pos)
  conv_lhs => rw [← VectorInference.apply_inverse_apply hB t]
  rw [← apply_nbCoefIncl_of_cross hI_symm hcross, VectorInference.inverse_apply_apply hI]

section Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

omit [DecidableEq κ] [IsProbabilityMeasure P] in
/-- An estimator that is a root of the closed-form likelihood equation with probability tending to
one, and is consistent for a parameter with positive shape, is a root of the generic likelihood
equation `∑ score = 0` with probability tending to one. -/
theorem tendsto_measure_sum_score_ne_zero {p₀ : NBParam κ} (hp₀ : 0 < nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ} {phat : ℕ → Ω → NBParam κ}
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀)) :
    Tendsto (fun n => P {ω | ∑ i ∈ range n, score nbRegDensity (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist] at hcons
  have hsum := hroot.add (hcons (nbParamShape p₀) hp₀)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq] at hω
  by_cases hpos : 0 < nbParamShape (phat n ω)
  · left
    simp only [Set.mem_ofPred_eq]
    simpa [score_nbRegDensity_eq hpos] using hω
  · right
    simp only [Set.mem_ofPred_eq]
    by_contra hlt
    exact hpos (nbParamShape_pos_of_mem_ball le_rfl (by
      rw [Metric.mem_ball]; exact lt_of_not_ge hlt))

/-- The Fisher information operator `I(p₀) = E[s sᵀ]` of the joint model at `p₀`, with
`s = score nbRegDensity p₀` (`VectorInference.fisherInformation`). -/
noncomputable abbrev nbRegFisherInfo (ν : Measure ((κ → ℝ) × ℕ)) (p₀ : NBParam κ) :
    NBParam κ →L[ℝ] NBParam κ :=
  fisherInformation ν nbRegDensity p₀

/-- **Asymptotic normality of the joint `(β, θ)` MLE, generic weighted-density form.** Let
`(xᵢ, yᵢ)` be i.i.d. with law `lawOf ν nbRegDensity p₀`, the law with density `nbRegDensity p₀`
with respect to an arbitrary reference measure `ν`, with true shape `θ₀ > 0`. This is
random-design negative binomial regression only for `ν = μX ⊗ count`
(`tendstoInDistribution_sqrt_smul_sub_nbJointMLE_randomDesign`); for other `ν` the counts need
not be negative binomial. Assume on the ball of radius
`δ ∈ (0, θ₀]` about `p₀ = (β₀, θ₀)` the Lipschitz envelope
`‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z ‖p - p₀‖` (integrable `M`), a square-integrable
centered score `nbRegScore p₀`, an integrable observed information with mean the Fisher
information (information identity), and a nonsingular Fisher information. Let `p̂ n` be
consistent and a root of `∑_{i<n} nbRegScore p (xᵢ, yᵢ) = 0` with probability tending to one.
Then `√n (p̂ n - p₀) → Z` in distribution for any `Z` with `⟪Z, t⟫ ~ N(0, ⟪I(p₀)⁻¹ t, t⟫)`.

The score `nbRegScore` and the observed information `nbRegObsInfo` are the closed forms of
`NegativeBinomialDispersion` (`score_nbRegDensity`, `hasFDerivAt_score_nbRegDensity`); the
differentiability conditions of `VectorInference` are proved, not assumed. The moment identities,
the envelope, the root property and consistency are hypotheses (consistency is the conclusion of
`tendstoInMeasure_nbJointMLE` under its explicit hypotheses). -/
theorem tendstoInDistribution_sqrt_smul_sub_nbJointMLE
    {ν : Measure ((κ → ℝ) × ℕ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ} (hX_law : ∀ i, HasLaw (X i) (lawOf ν nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf ν nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2) (lawOf ν nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf ν nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf ν nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf ν nbRegDensity p₀) = nbRegFisherInfo ν p₀)
    (hI : IsUnit (nbRegFisherInfo ν p₀))
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    {Z : Ω' → NBParam κ} (hZ_meas : AEMeasurable Z P')
    (hZ : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0 (⟪Ring.inverse (nbRegFisherInfo ν p₀) t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (phat n ω - p₀)) atTop Z (fun _ => P) P' := by
  have hp₀ : 0 < nbParamShape p₀ := hδ.trans_le hδθ
  have hball : ∀ p ∈ Metric.ball p₀ δ, 0 < nbParamShape p :=
    fun p hp => nbParamShape_pos_of_mem_ball hδθ hp
  refine VectorInference.tendstoInDistribution_sqrt_smul_sub_of_likelihoodEquation hδ hX_law
    hX_indep (fun z p hp => (hasFDerivAt_score_nbRegDensity (hball p hp) z).differentiableAt)
    hM_meas hM_int (fun z p hp => ?_) ?_ ?_ ?_ ?_ ?_ ?_ hI hphat_meas
    (tendsto_measure_sum_score_ne_zero hp₀ hroot hcons) hcons hZ_meas hZ
  · rw [fderiv_score_nbRegDensity (hball p hp), fderiv_score_nbRegDensity hp₀, ← neg_sub',
      norm_neg]
    exact hM z p hp
  · rw [score_nbRegDensity_eq hp₀]; exact measurable_nbRegScore p₀
  · rwa [score_nbRegDensity_eq hp₀]
  · rwa [score_nbRegDensity_eq hp₀]
  · simp_rw [fderiv_score_nbRegDensity hp₀]
    exact (measurable_nbRegObsInfo p₀).neg.stronglyMeasurable
  · simp_rw [fderiv_score_nbRegDensity hp₀]
    exact hJ_int.neg
  · simp_rw [fderiv_score_nbRegDensity hp₀]
    rw [integral_neg, h_info]

omit [DecidableEq κ] in
/-- The joint parameter space has dimension `|κ| + 1` (coefficients and the shape). -/
theorem finrank_nbParam : Module.finrank ℝ (NBParam κ) = Fintype.card κ + 1 := by
  simp [finrank_euclideanSpace, Fintype.card_sum]

/-- **Wald's test for the joint `(β, θ)` with estimated information, generic weighted-density
form** (arbitrary reference measure `ν`; negative binomial regression is
`tendstoInDistribution_waldStatistic_nbJointMLE_randomDesign`). Under the hypotheses of
`tendstoInDistribution_sqrt_smul_sub_nbJointMLE`, with positive definite Fisher information, and
for any a.e.-measurable information estimators `Î n → I(p₀)` in probability (for example the
closed-form observed information at the estimator, `tendstoInMeasure_nbRegAvgObsInfo`), the Wald
statistic `n ⟪Î n (p̂ n - p₀), p̂ n - p₀⟫` converges in distribution to `χ²` with `|κ| + 1`
degrees of freedom: the shape is estimated jointly and counts as one more degree of freedom. -/
theorem tendstoInDistribution_waldStatistic_nbJointMLE
    {ν : Measure ((κ → ℝ) × ℕ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ} (hX_law : ∀ i, HasLaw (X i) (lawOf ν nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf ν nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2) (lawOf ν nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf ν nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf ν nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf ν nbRegDensity p₀) = nbRegFisherInfo ν p₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo ν p₀ u, u⟫)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    {Ihat : ℕ → Ω → NBParam κ →L[ℝ] NBParam κ} (hIhat_meas : ∀ n, AEMeasurable (Ihat n) P)
    (hIhat : TendstoInMeasure P Ihat atTop (fun _ => nbRegFisherInfo ν p₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ + 1)) P') :
    TendstoInDistribution (fun (n : ℕ) ω => n * ⟪Ihat n ω (phat n ω - p₀), phat n ω - p₀⟫)
      atTop Q (fun _ => P) P' := by
  have hp₀ : 0 < nbParamShape p₀ := hδ.trans_le hδθ
  have hball : ∀ p ∈ Metric.ball p₀ δ, 0 < nbParamShape p :=
    fun p hp => nbParamShape_pos_of_mem_ball hδθ hp
  refine EstimatedInformation.tendstoInDistribution_waldStatistic_of_estimator hδ hX_law
    hX_indep (fun z p hp => (hasFDerivAt_score_nbRegDensity (hball p hp) z).differentiableAt)
    hM_meas hM_int (fun z p hp => ?_) ?_ ?_ ?_ ?_ ?_ ?_ hI_pos (by rw [finrank_nbParam]; omega)
    hphat_meas (tendsto_measure_sum_score_ne_zero hp₀ hroot hcons) hcons hIhat_meas hIhat
    (by rwa [finrank_nbParam])
  · rw [fderiv_score_nbRegDensity (hball p hp), fderiv_score_nbRegDensity hp₀, ← neg_sub',
      norm_neg]
    exact hM z p hp
  · rw [score_nbRegDensity_eq hp₀]; exact measurable_nbRegScore p₀
  · rwa [score_nbRegDensity_eq hp₀]
  · rwa [score_nbRegDensity_eq hp₀]
  · simp_rw [fderiv_score_nbRegDensity hp₀]
    exact (measurable_nbRegObsInfo p₀).neg.stronglyMeasurable
  · simp_rw [fderiv_score_nbRegDensity hp₀]
    exact hJ_int.neg
  · simp_rw [fderiv_score_nbRegDensity hp₀]
    rw [integral_neg, h_info]

omit [DecidableEq κ] in
/-- **Rao's score test for the joint `(β, θ)` with estimated information, generic
weighted-density form** (arbitrary reference measure `ν`; negative binomial regression is
`tendstoInDistribution_scoreStatistic_nbJointMLE_randomDesign`). For i.i.d. observations with law
`lawOf ν nbRegDensity p₀` (shape `θ₀ > 0`), a square-integrable centered score and a
positive definite Fisher information, and any a.e.-measurable `Î n → I(p₀)` in probability, the
score statistic `⟪Î n⁻¹ Sₙ, Sₙ⟫` with `Sₙ = n^{-1/2} ∑_{i<n} nbRegScore p₀ (xᵢ, yᵢ)` converges
in distribution to `χ²` with `|κ| + 1` degrees of freedom. -/
theorem tendstoInDistribution_scoreStatistic_nbJointMLE
    {ν : Measure ((κ → ℝ) × ℕ)} {p₀ : NBParam κ} (hp₀ : 0 < nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ} (hX_law : ∀ i, HasLaw (X i) (lawOf ν nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2) (lawOf ν nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf ν nbRegDensity p₀) = 0)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo ν p₀ u, u⟫)
    {Ihat : ℕ → Ω → NBParam κ →L[ℝ] NBParam κ} (hIhat_meas : ∀ n, AEMeasurable (Ihat n) P)
    (hIhat : TendstoInMeasure P Ihat atTop (fun _ => nbRegFisherInfo ν p₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ + 1)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ⟪Ring.inverse (Ihat n ω) ((√n)⁻¹ • ∑ i ∈ range n, nbRegScore p₀ (X i ω)),
          (√n)⁻¹ • ∑ i ∈ range n, nbRegScore p₀ (X i ω)⟫)
      atTop Q (fun _ => P) P' := by
  have h := EstimatedInformation.tendstoInDistribution_scoreStatistic_of_estimator hX_law
    hX_indep (by rw [score_nbRegDensity_eq hp₀]; exact measurable_nbRegScore p₀)
    (by rwa [score_nbRegDensity_eq hp₀]) (by rwa [score_nbRegDensity_eq hp₀]) hI_pos
    (by rw [finrank_nbParam]; omega) hIhat_meas hIhat (by rwa [finrank_nbParam])
  simpa only [score_nbRegDensity_eq hp₀] using h

/-- **Wilks' theorem for the joint `(β, θ)`, simple null, generic weighted-density form**
(arbitrary reference measure `ν`; negative binomial regression is
`tendstoInDistribution_two_mul_logLik_sub_nbJointMLE_randomDesign`). Under the hypotheses of
`tendstoInDistribution_waldStatistic_nbJointMLE` (without `Î`), the likelihood-ratio statistic
`2 ∑_{i<n} (log NB(yᵢ; θ̂, e^{xᵢ ⬝ᵥ β̂}) - log NB(yᵢ; θ₀, e^{xᵢ ⬝ᵥ β₀}))`, evaluated at the
consistent root `p̂ n = (β̂, θ̂)`, converges in distribution to `χ²` with `|κ| + 1` degrees of
freedom. Composite nulls (testing `β` with `θ` free) are not covered here. -/
theorem tendstoInDistribution_two_mul_logLik_sub_nbJointMLE
    {ν : Measure ((κ → ℝ) × ℕ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ} (hX_law : ∀ i, HasLaw (X i) (lawOf ν nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf ν nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2) (lawOf ν nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf ν nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf ν nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf ν nbRegDensity p₀) = nbRegFisherInfo ν p₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo ν p₀ u, u⟫)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ + 1)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ range n,
        (Real.log (nbRegDensity (phat n ω) (X i ω)) - Real.log (nbRegDensity p₀ (X i ω))))
      atTop Q (fun _ => P) P' := by
  have hp₀ : 0 < nbParamShape p₀ := hδ.trans_le hδθ
  have hball : ∀ p ∈ Metric.ball p₀ δ, 0 < nbParamShape p :=
    fun p hp => nbParamShape_pos_of_mem_ball hδθ hp
  refine VectorInference.tendstoInDistribution_two_mul_logLikelihood_sub hδ
    measurable_uncurry_nbRegDensity hX_law hX_indep
    (fun z p hp => (hasGradientAt_log_nbRegDensity (hball p hp) z).differentiableAt)
    (fun z p hp => (hasFDerivAt_score_nbRegDensity (hball p hp) z).differentiableAt)
    hM_meas hM_int (fun z p hp => ?_) ?_ ?_ ?_ ?_ ?_ ?_ hI_pos (by rw [finrank_nbParam]; omega)
    hphat_meas (tendsto_measure_sum_score_ne_zero hp₀ hroot hcons) hcons
    (by rwa [finrank_nbParam])
  · rw [fderiv_score_nbRegDensity (hball p hp), fderiv_score_nbRegDensity hp₀, ← neg_sub',
      norm_neg]
    exact hM z p hp
  · rw [score_nbRegDensity_eq hp₀]; exact measurable_nbRegScore p₀
  · rwa [score_nbRegDensity_eq hp₀]
  · rwa [score_nbRegDensity_eq hp₀]
  · simp_rw [fderiv_score_nbRegDensity hp₀]
    exact (measurable_nbRegObsInfo p₀).neg.stronglyMeasurable
  · simp_rw [fderiv_score_nbRegDensity hp₀]
    exact hJ_int.neg
  · simp_rw [fderiv_score_nbRegDensity hp₀]
    rw [integral_neg, h_info]

/-- **Wald's test for the coefficients with an estimated shape, generic weighted-density form**
(arbitrary reference measure `ν`; negative binomial regression is
`tendstoInDistribution_coefWaldStatistic_nbJointMLE_randomDesign`). Under the hypotheses of
`tendstoInDistribution_waldStatistic_nbJointMLE`, assume the cross information between `β` and
`θ` vanishes, `⟪I(p₀) (0, 1), (t, 0)⟫ = 0` (proved for negative binomial regression,
`ν = μX ⊗ count`, in `inner_nbRegFisherInfo_nbShapeVec_nbCoefIncl`). Let `B̂ n` be any
a.e.-measurable estimators of the coefficient block `B = Πβ I(p₀) ιβ` (for example the
coefficient block of a consistent estimator of `I(p₀)`). Then, with `θ` estimated jointly and
treated as a nuisance parameter, the Wald statistic for `β` alone, `n ⟪B̂ n (β̂ - β₀), β̂ - β₀⟫`,
converges in distribution to `χ²` with `|κ|` degrees of freedom. The block `B` is the
information for `β` when `θ` is known, so estimating the shape costs no degree of freedom and
does not change the reference law. -/
theorem tendstoInDistribution_coefWaldStatistic_nbJointMLE
    {ν : Measure ((κ → ℝ) × ℕ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ} (hX_law : ∀ i, HasLaw (X i) (lawOf ν nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf ν nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2) (lawOf ν nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf ν nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf ν nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf ν nbRegDensity p₀) = nbRegFisherInfo ν p₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo ν p₀ u, u⟫)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    (hcross : ∀ t, ⟪nbRegFisherInfo ν p₀ nbShapeVec, nbCoefIncl t⟫ = 0)
    (hκ : 0 < Fintype.card κ)
    {Bhat : ℕ → Ω → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ}
    (hBhat_meas : ∀ n, AEMeasurable (Bhat n) P)
    (hBhat : TendstoInMeasure P Bhat atTop (fun _ => nbCoefBlock (nbRegFisherInfo ν p₀)))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        n * ⟪Bhat n ω (nbCoefProj (phat n ω - p₀)), nbCoefProj (phat n ω - p₀)⟫)
      atTop Q (fun _ => P) P' := by
  have hp₀ : 0 < nbParamShape p₀ := hδ.trans_le hδθ
  have hball : ∀ p ∈ Metric.ball p₀ δ, 0 < nbParamShape p :=
    fun p hp => nbParamShape_pos_of_mem_ball hδθ hp
  set I := nbRegFisherInfo ν p₀ with hI_def
  set B := nbCoefBlock I with hB_def
  have hI_symm : ∀ u v, ⟪I u, v⟫ = ⟪u, I v⟫ :=
    VectorInference.inner_fisherInformation_comm ν nbRegDensity p₀
  have hI : IsUnit I := VectorInference.isUnit_of_inner_self_pos hI_pos
  have hB_pos : ∀ u, u ≠ 0 → 0 < ⟪B u, u⟫ := inner_nbCoefBlock_self_pos hI_pos
  have hB : IsUnit B := VectorInference.isUnit_of_inner_self_pos hB_pos
  have hB_symm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫ := inner_nbCoefBlock_comm hI_symm
  -- the hypotheses of `VectorInference` in generic form
  have hs_meas' : Measurable (score nbRegDensity p₀) := by
    rw [score_nbRegDensity_eq hp₀]; exact measurable_nbRegScore p₀
  have hs_sq' : Integrable (fun z => ‖score nbRegDensity p₀ z‖ ^ 2)
      (lawOf ν nbRegDensity p₀) := by rwa [score_nbRegDensity_eq hp₀]
  have hs_mean' : ∫ z, score nbRegDensity p₀ z ∂(lawOf ν nbRegDensity p₀) = 0 := by
    rwa [score_nbRegDensity_eq hp₀]
  have hM' : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖fderiv ℝ (fun t => score nbRegDensity t z) p -
        fderiv ℝ (fun t => score nbRegDensity t z) p₀‖ ≤ M z * ‖p - p₀‖ := fun z p hp => by
    rw [fderiv_score_nbRegDensity (hball p hp), fderiv_score_nbRegDensity hp₀, ← neg_sub',
      norm_neg]
    exact hM z p hp
  have hDs : (fun z => fderiv ℝ (fun t => score nbRegDensity t z) p₀) =
      fun z => -nbRegObsInfo p₀ z := funext (fderiv_score_nbRegDensity hp₀)
  have hs : MemLp (score nbRegDensity p₀) 2 (lawOf ν nbRegDensity p₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas'.aestronglyMeasurable).2 hs_sq'
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal ((hX_law 0).memLp_comp hs)
  have hAI : ∀ t, HasLaw (fun z => ⟪A z, t⟫) (gaussianReal 0 (⟪I t, t⟫).toNNReal)
      (stdGaussian (NBParam κ)) := fun t => by
    have h := hA t
    rwa [show (fun ω => ⟪(score nbRegDensity p₀ ∘ X 0) ω, t⟫) =
        fun ω => ⟪score nbRegDensity p₀ (X 0 ω), t⟫ from rfl,
      VectorInference.variance_inner_score (hX_law 0) hs_meas' hs_sq' hs_mean' t] at h
  have hT := VectorInference.tendstoInDistribution_sqrt_smul_sub_inverse_of_likelihoodEquation
    hδ hX_law hX_indep
    (fun z p hp => (hasFDerivAt_score_nbRegDensity (hball p hp) z).differentiableAt)
    hM_meas hM_int hM' hs_meas' hs_sq' hs_mean'
    (by rw [hDs]; exact (measurable_nbRegObsInfo p₀).neg.stronglyMeasurable)
    (by rw [hDs]; exact hJ_int.neg) (by rw [hDs, integral_neg, h_info]) hI hphat_meas
    (tendsto_measure_sum_score_ne_zero hp₀ hroot hcons) hcons A.continuous.aemeasurable hAI
  have hg : Continuous fun q : NBParam κ × (EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) =>
      ⟪q.2 (nbCoefProj q.1), nbCoefProj q.1⟫ := by fun_prop
  have h2 := hT.continuous_comp_prodMk_of_tendstoInMeasure_const hg hBhat hBhat_meas
  -- the law of the coefficient block of the limit
  set V : NBParam κ → EuclideanSpace ℝ κ := fun z => nbCoefProj (Ring.inverse I (A z)) with hV_def
  have hV : ∀ t, HasLaw (fun z => ⟪V z, t⟫)
      (gaussianReal 0 (⟪Ring.inverse B t, t⟫).toNNReal) (stdGaussian (NBParam κ)) := fun t => by
    have e : (fun z => ⟪V z, t⟫) = fun z => ⟪A z, nbCoefIncl (Ring.inverse B t)⟫ :=
      funext fun z => by
        rw [hV_def, inner_nbCoefProj, VectorInference.inner_inverse_comm hI_symm hI,
          inverse_apply_nbCoefIncl_of_cross hI_symm hI_pos hcross]
    rw [e]
    have h := hAI (nbCoefIncl (Ring.inverse B t))
    rwa [apply_nbCoefIncl_of_cross hI_symm hcross, inner_nbCoefIncl,
      VectorInference.apply_inverse_apply hB, real_inner_comm] at h
  have hS_pos : ∀ u, u ≠ 0 → 0 < ⟪Ring.inverse B u, u⟫ := fun u hu => by
    have hw : Ring.inverse B u ≠ 0 := fun h => hu (by
      rw [← VectorInference.apply_inverse_apply hB u, h, map_zero])
    have := hB_pos _ hw
    rwa [VectorInference.apply_inverse_apply hB, real_inner_comm] at this
  have hchi := VectorInference.hasLaw_inner_inverse_chiSquare
    (VectorInference.inner_inverse_comm hB_symm hB) hS_pos
    (by rw [finrank_euclideanSpace]; exact hκ) (by fun_prop) hV
  rw [Ring.inverse_inverse hB, finrank_euclideanSpace] at hchi
  refine (h2.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun z => rfl)).of_map_eq
    hQ.aemeasurable ?_
  · simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  · rw [hQ.map_eq, ← hchi.map_eq]

/-- **Consistency of the closed-form observed information at the estimator, generic
weighted-density form** (arbitrary reference measure `ν`; negative binomial regression is
`tendstoInMeasure_nbRegAvgObsInfo_randomDesign`). Under the envelope and information hypotheses
of `tendstoInDistribution_sqrt_smul_sub_nbJointMLE`, for any consistent
a.e.-measurable `p̂ n`, the averaged observed information `nbRegAvgObsInfo n (x, y) (p̂ n)`
(the merged `n⁻¹ • nbJointObsInfo` at `(β̂, θ̂)`, `nbRegAvgObsInfo_eq_nbJointObsInfo`) converges in
probability to the Fisher information `I(p₀)`. -/
theorem tendstoInMeasure_nbRegAvgObsInfo
    {ν : Measure ((κ → ℝ) × ℕ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ} (hX_law : ∀ i, HasLaw (X i) (lawOf ν nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf ν nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf ν nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf ν nbRegDensity p₀) = nbRegFisherInfo ν p₀)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀)) :
    TendstoInMeasure P (fun n ω => nbRegAvgObsInfo n (fun i => X i ω) (phat n ω)) atTop
      (fun _ => nbRegFisherInfo ν p₀) := by
  have hp₀ : 0 < nbParamShape p₀ := hδ.trans_le hδθ
  have hball : ∀ p ∈ Metric.ball p₀ δ, 0 < nbParamShape p :=
    fun p hp => nbParamShape_pos_of_mem_ball hδθ hp
  have hDs : (fun z => fderiv ℝ (fun t => score nbRegDensity t z) p₀) =
      fun z => -nbRegObsInfo p₀ z := funext (fderiv_score_nbRegDensity hp₀)
  have hgen := EstimatedInformation.tendstoInMeasure_observedInformation_of_tendstoInMeasure hδ
    hX_law hX_indep hM_meas hM_int (fun z p hp => by
      rw [fderiv_score_nbRegDensity (hball p hp), fderiv_score_nbRegDensity hp₀, ← neg_sub',
        norm_neg]
      exact hM z p hp)
    (by rw [hDs]; exact (measurable_nbRegObsInfo p₀).neg.stronglyMeasurable)
    (by rw [hDs]; exact hJ_int.neg) (by rw [hDs, integral_neg, h_info]) hphat_meas hcons
  rw [tendstoInMeasure_iff_dist] at hgen hcons ⊢
  intro ε hε
  have hsum := (hgen ε hε).add (hcons (nbParamShape p₀) hp₀)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq] at hω
  by_cases hpos : 0 < nbParamShape (phat n ω)
  · left
    simp only [Set.mem_ofPred_eq]
    rwa [observedInformation_nbRegDensity hpos]
  · right
    simp only [Set.mem_ofPred_eq]
    by_contra hlt
    exact hpos (nbParamShape_pos_of_mem_ball le_rfl (by
      rw [Metric.mem_ball]; exact lt_of_not_ge hlt))

omit [IsProbabilityMeasure P] in
theorem aemeasurable_nbRegAvgObsInfo {X : ℕ → Ω → (κ → ℝ) × ℕ} (hX : ∀ i, AEMeasurable (X i) P)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P) (n : ℕ) :
    AEMeasurable (fun ω => nbRegAvgObsInfo n (fun i => X i ω) (phat n ω)) P := by
  have hi : ∀ i, AEMeasurable (fun ω => nbRegObsInfo (phat n ω) (X i ω)) P := fun i => by
    have h := measurable_uncurry_nbRegObsInfo.comp_aemeasurable ((hphat_meas n).prodMk (hX i))
    simpa only [Function.comp_def] using h
  have hs : AEMeasurable (fun ω => ∑ i ∈ range n, nbRegObsInfo (phat n ω) (X i ω)) P :=
    Finset.aemeasurable_fun_sum _ fun i _ => hi i
  simpa only [nbRegAvgObsInfo] using hs.fun_const_smul ((n : ℝ)⁻¹)

/-- **Wald's test for the joint `(β, θ)` with the observed information at the estimator,
generic weighted-density form** (arbitrary reference measure `ν`; negative binomial regression is
`tendstoInDistribution_waldStatistic_nbJointMLE_obsInfo_randomDesign`). The corollary of
`tendstoInDistribution_waldStatistic_nbJointMLE` with `Î n` the closed-form observed information
`nbRegAvgObsInfo n (x, y) (p̂ n)` (`tendstoInMeasure_nbRegAvgObsInfo`). -/
theorem tendstoInDistribution_waldStatistic_nbJointMLE_obsInfo
    {ν : Measure ((κ → ℝ) × ℕ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ} (hX_law : ∀ i, HasLaw (X i) (lawOf ν nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf ν nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2) (lawOf ν nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf ν nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf ν nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf ν nbRegDensity p₀) = nbRegFisherInfo ν p₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo ν p₀ u, u⟫)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ + 1)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        n * ⟪nbRegAvgObsInfo n (fun i => X i ω) (phat n ω) (phat n ω - p₀), phat n ω - p₀⟫)
      atTop Q (fun _ => P) P' :=
  tendstoInDistribution_waldStatistic_nbJointMLE hδ hδθ hX_law hX_indep hM_meas hM_int hM hs_sq
    hs_mean hJ_int h_info hI_pos hphat_meas hroot hcons
    (aemeasurable_nbRegAvgObsInfo (fun i => (hX_law i).aemeasurable) hphat_meas)
    (tendstoInMeasure_nbRegAvgObsInfo hδ hδθ hX_law hX_indep hM_meas hM_int hM hJ_int h_info
      hphat_meas hcons) hQ

end Asymptotics

/-! ### The Fisher information of the random-design model is block diagonal

With covariates of law `μX` and the reference measure `μX ⊗ count`, integrals under the model law
are covariate averages of negative binomial sums (`integral_lawOf_nbRegDensity`). The per-count
mean identities of `NegativeBinomialDispersion` then give the blocks of `I(p₀)`, through the
information identity `E[nbRegObsInfo] = I(p₀)`. -/

omit [DecidableEq κ] in
/-- **Integrals under the model law.** For covariates of law `μX` and reference measure
`μX ⊗ count`, `∫ g d(law) = ∫ ∑ₖ NB(k; θ₀, e^{x ⬝ᵥ β₀}) g (x, k) dμX(x)`. -/
theorem integral_lawOf_nbRegDensity {μX : Measure (κ → ℝ)} [SFinite μX] {p₀ : NBParam κ}
    (hp₀ : 0 < nbParamShape p₀) {g : (κ → ℝ) × ℕ → ℝ}
    (hg : Integrable g (lawOf (μX.prod Measure.count) nbRegDensity p₀)) :
    ∫ z, g z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      ∫ x, ∑' k, nbRegDensity p₀ (x, k) * g (x, k) ∂μX := by
  have hmeas : Measurable fun z => ENNReal.ofReal (nbRegDensity p₀ z) :=
    ENNReal.measurable_ofReal.comp
      (measurable_uncurry_nbRegDensity.comp (measurable_const.prodMk measurable_id))
  have hfin : ∀ᵐ z ∂(μX.prod Measure.count), ENNReal.ofReal (nbRegDensity p₀ z) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hnn : ∀ z, 0 ≤ nbRegDensity p₀ z := fun z =>
    negBinomialReal_nonneg hp₀ (exp_pos _).le _
  have hF : Integrable (fun z => nbRegDensity p₀ z * g z) (μX.prod Measure.count) := by
    have := (integrable_withDensity_iff_integrable_smul' hmeas hfin).1 hg
    simpa [ENNReal.toReal_ofReal (hnn _)] using this
  rw [lawOf, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
  simp_rw [ENNReal.toReal_ofReal (hnn _), smul_eq_mul]
  rw [integral_prod _ hF]
  refine integral_congr_ae ?_
  filter_upwards [hF.prod_right_ae] with x hx
  rw [integral_countable hx]
  simp

theorem inner_nbCoefIncl_nbRegObsInfo_nbShapeVec (p : NBParam κ) (z : (κ → ℝ) × ℕ)
    (t : EuclideanSpace ℝ κ) :
    ⟪nbCoefIncl t, nbRegObsInfo p z nbShapeVec⟫ =
      -(nbCross (nbParamShape p) z.2 (z.1 ⬝ᵥ nbParamCoef p) * (z.1 ⬝ᵥ WithLp.ofLp t)) := by
  rw [nbRegObsInfo, inner_toEuclideanCLM]
  simp only [dotProduct, Fintype.sum_sum_type, nbObsInfoRow_mulVec_inl]
  simp only [nbShapeVec]
  simp only [nbCoefIncl_apply_inl, ne_eq, reduceCtorEq, not_false_eq_true, PiLp.single_eq_of_ne,
    mul_zero, sum_const_zero, PiLp.single_eq_same, mul_one, zero_sub, mul_neg, sum_neg_distrib,
    univ_unique, PUnit.default_eq_unit, nbCoefIncl_apply_inr, PiLp.ofLp_single, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, one_smul, zero_mul, add_zero, neg_inj,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The shape is orthogonal to the coefficients in the random-design model.** For covariates
of law `μX` (reference measure `μX ⊗ count`), a true shape `θ₀ > 0`, an integrable observed
information and the information identity `E[nbRegObsInfo p₀] = I(p₀)`, the cross information
vanishes: `⟪I(p₀) (0, 1), (t, 0)⟫ = 0` for every `t`. The proof averages the mean-zero identity
`hasSum_nbCross_mul_negBinomialReal` of `NegativeBinomialDispersion` over the covariates. -/
theorem inner_nbRegFisherInfo_nbShapeVec_nbCoefIncl {μX : Measure (κ → ℝ)} [SFinite μX]
    {p₀ : NBParam κ} (hp₀ : 0 < nbParamShape p₀)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      nbRegFisherInfo (μX.prod Measure.count) p₀)
    (t : EuclideanSpace ℝ κ) :
    ⟪nbRegFisherInfo (μX.prod Measure.count) p₀ nbShapeVec, nbCoefIncl t⟫ = 0 := by
  have hint := (hJ_int.apply_continuousLinearMap nbShapeVec).const_inner (𝕜 := ℝ) (nbCoefIncl t)
  rw [← h_info, real_inner_comm, ContinuousLinearMap.integral_apply hJ_int,
    ← integral_inner (𝕜 := ℝ) (hJ_int.apply_continuousLinearMap nbShapeVec),
    integral_lawOf_nbRegDensity hp₀ hint]
  refine (integral_congr_ae (ae_of_all _ fun x => ?_)).trans (integral_zero _ _)
  simp only [inner_nbCoefIncl_nbRegObsInfo_nbShapeVec]
  have h := ((hasSum_nbCross_mul_negBinomialReal hp₀ (x ⬝ᵥ nbParamCoef p₀)).mul_right
    (-(x ⬝ᵥ WithLp.ofLp t))).tsum_eq
  rw [zero_mul] at h
  rw [← h]
  refine tsum_congr fun k => ?_
  simp only [nbRegDensity]
  ring

theorem inner_nbCoefIncl_nbRegObsInfo_nbCoefIncl (p : NBParam κ) (z : (κ → ℝ) × ℕ)
    (u t : EuclideanSpace ℝ κ) :
    ⟪nbCoefIncl t, nbRegObsInfo p z (nbCoefIncl u)⟫ =
      nbObsWeight (nbParamShape p) z.2 (z.1 ⬝ᵥ nbParamCoef p) * (z.1 ⬝ᵥ WithLp.ofLp u) *
        (z.1 ⬝ᵥ WithLp.ofLp t) := by
  rw [nbRegObsInfo, inner_toEuclideanCLM]
  simp only [dotProduct, Fintype.sum_sum_type, nbObsInfoRow_mulVec_inl, nbCoefIncl_apply_inl,
    nbCoefIncl_apply_inr, mul_zero, sub_zero, zero_mul, Finset.univ_unique, Finset.sum_singleton,
    add_zero, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The coefficient block of the Fisher information is the known-shape information.** In the
random-design model (covariates of law `μX`, true shape `θ₀ > 0`), under the information identity
`E[nbRegObsInfo p₀] = I(p₀)`, the coefficient block of `I(p₀)` is
`E_x[F(θ₀, x ⬝ᵥ β₀) x xᵀ]` with `F = nbFisherWeight`: the information for `β` when `θ` is known
(the random-design form of `toBlocks₁₁_inv_nbJointFisherInfo`). The proof averages
`hasSum_nbObsWeight_mul_negBinomialReal` over the covariates. -/
theorem inner_nbCoefBlock_nbRegFisherInfo {μX : Measure (κ → ℝ)} [SFinite μX]
    {p₀ : NBParam κ} (hp₀ : 0 < nbParamShape p₀)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      nbRegFisherInfo (μX.prod Measure.count) p₀)
    (u t : EuclideanSpace ℝ κ) :
    ⟪nbCoefBlock (nbRegFisherInfo (μX.prod Measure.count) p₀) u, t⟫ =
      ∫ x, nbFisherWeight (nbParamShape p₀) (x ⬝ᵥ nbParamCoef p₀) * (x ⬝ᵥ WithLp.ofLp u) *
        (x ⬝ᵥ WithLp.ofLp t) ∂μX := by
  have hint := (hJ_int.apply_continuousLinearMap (nbCoefIncl u)).const_inner (𝕜 := ℝ)
    (nbCoefIncl t)
  rw [nbCoefBlock, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    inner_nbCoefProj, ← h_info, real_inner_comm, ContinuousLinearMap.integral_apply hJ_int,
    ← integral_inner (𝕜 := ℝ) (hJ_int.apply_continuousLinearMap (nbCoefIncl u)),
    integral_lawOf_nbRegDensity hp₀ hint]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [inner_nbCoefIncl_nbRegObsInfo_nbCoefIncl]
  have h := ((hasSum_nbObsWeight_mul_negBinomialReal hp₀ (x ⬝ᵥ nbParamCoef p₀)).mul_right
    ((x ⬝ᵥ WithLp.ofLp u) * (x ⬝ᵥ WithLp.ofLp t))).tsum_eq
  rw [← mul_assoc] at h
  rw [← h]
  refine tsum_congr fun k => ?_
  simp only [nbRegDensity]
  ring

section RandomDesign

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-! ### Random-design negative binomial regression

With covariates of law `μX`, the reference measure `μX ⊗ count` and a true shape `θ₀ > 0`, the
observations `(xᵢ, yᵢ)` with law `lawOf (μX.prod Measure.count) nbRegDensity p₀` are
random-design negative binomial regression data: covariates of law `μX` and counts that are
conditionally `NB(θ₀, exp (xᵢ ⬝ᵥ β₀))`. The theorems below restate every asymptotic result of
the file for this reference measure. -/

/-- **Asymptotic normality of the joint `(β, θ)` negative binomial MLE, random design.** For
i.i.d. `(xᵢ, yᵢ)` with covariates of law `μX` and counts conditionally `NB(θ₀, exp (xᵢ ⬝ᵥ β₀))`
(reference measure `μX ⊗ count`), under the hypotheses of
`tendstoInDistribution_sqrt_smul_sub_nbJointMLE`, `√n (p̂ n - p₀) → Z` in distribution for any
`Z` with `⟪Z, t⟫ ~ N(0, ⟪I(p₀)⁻¹ t, t⟫)`. -/
theorem tendstoInDistribution_sqrt_smul_sub_nbJointMLE_randomDesign
    {μX : Measure (κ → ℝ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i) (lawOf (μX.prod Measure.count) nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      nbRegFisherInfo (μX.prod Measure.count) p₀)
    (hI : IsUnit (nbRegFisherInfo (μX.prod Measure.count) p₀))
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    {Z : Ω' → NBParam κ} (hZ_meas : AEMeasurable Z P')
    (hZ : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0
        (⟪Ring.inverse (nbRegFisherInfo (μX.prod Measure.count) p₀) t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (phat n ω - p₀)) atTop Z (fun _ => P) P' :=
  tendstoInDistribution_sqrt_smul_sub_nbJointMLE hδ hδθ hX_law hX_indep hM_meas hM_int hM hs_sq
    hs_mean hJ_int h_info hI hphat_meas hroot hcons hZ_meas hZ

/-- **Wald's test for the joint `(β, θ)` with estimated information, random design.** The
negative binomial regression form (reference measure `μX ⊗ count`) of
`tendstoInDistribution_waldStatistic_nbJointMLE`: `n ⟪Î n (p̂ n - p₀), p̂ n - p₀⟫ → χ²` with
`|κ| + 1` degrees of freedom. -/
theorem tendstoInDistribution_waldStatistic_nbJointMLE_randomDesign
    {μX : Measure (κ → ℝ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i) (lawOf (μX.prod Measure.count) nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      nbRegFisherInfo (μX.prod Measure.count) p₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo (μX.prod Measure.count) p₀ u, u⟫)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    {Ihat : ℕ → Ω → NBParam κ →L[ℝ] NBParam κ} (hIhat_meas : ∀ n, AEMeasurable (Ihat n) P)
    (hIhat : TendstoInMeasure P Ihat atTop
      (fun _ => nbRegFisherInfo (μX.prod Measure.count) p₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ + 1)) P') :
    TendstoInDistribution (fun (n : ℕ) ω => n * ⟪Ihat n ω (phat n ω - p₀), phat n ω - p₀⟫)
      atTop Q (fun _ => P) P' :=
  tendstoInDistribution_waldStatistic_nbJointMLE hδ hδθ hX_law hX_indep hM_meas hM_int hM hs_sq
    hs_mean hJ_int h_info hI_pos hphat_meas hroot hcons hIhat_meas hIhat hQ

/-- **Consistency of the closed-form observed information at the estimator, random design.**
The negative binomial regression form (reference measure `μX ⊗ count`) of
`tendstoInMeasure_nbRegAvgObsInfo`: `nbRegAvgObsInfo n (x, y) (p̂ n) → I(p₀)` in probability. -/
theorem tendstoInMeasure_nbRegAvgObsInfo_randomDesign
    {μX : Measure (κ → ℝ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i) (lawOf (μX.prod Measure.count) nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      nbRegFisherInfo (μX.prod Measure.count) p₀)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀)) :
    TendstoInMeasure P (fun n ω => nbRegAvgObsInfo n (fun i => X i ω) (phat n ω)) atTop
      (fun _ => nbRegFisherInfo (μX.prod Measure.count) p₀) :=
  tendstoInMeasure_nbRegAvgObsInfo hδ hδθ hX_law hX_indep hM_meas hM_int hM hJ_int h_info
    hphat_meas hcons

/-- **Wald's test for the joint `(β, θ)` with the observed information at the estimator, random
design.** The negative binomial regression form (reference measure `μX ⊗ count`) of
`tendstoInDistribution_waldStatistic_nbJointMLE_obsInfo`:
`n ⟪nbRegAvgObsInfo n (x, y) (p̂ n) (p̂ n - p₀), p̂ n - p₀⟫ → χ²` with `|κ| + 1` degrees of
freedom. -/
theorem tendstoInDistribution_waldStatistic_nbJointMLE_obsInfo_randomDesign
    {μX : Measure (κ → ℝ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i) (lawOf (μX.prod Measure.count) nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      nbRegFisherInfo (μX.prod Measure.count) p₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo (μX.prod Measure.count) p₀ u, u⟫)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ + 1)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        n * ⟪nbRegAvgObsInfo n (fun i => X i ω) (phat n ω) (phat n ω - p₀), phat n ω - p₀⟫)
      atTop Q (fun _ => P) P' :=
  tendstoInDistribution_waldStatistic_nbJointMLE_obsInfo hδ hδθ hX_law hX_indep hM_meas hM_int
    hM hs_sq hs_mean hJ_int h_info hI_pos hphat_meas hroot hcons hQ

omit [DecidableEq κ] in
/-- **Rao's score test for the joint `(β, θ)` with estimated information, random design.** The
negative binomial regression form (reference measure `μX ⊗ count`) of
`tendstoInDistribution_scoreStatistic_nbJointMLE`: the score statistic `⟪Î n⁻¹ Sₙ, Sₙ⟫`,
`Sₙ = n^{-1/2} ∑_{i<n} nbRegScore p₀ (xᵢ, yᵢ)`, converges in distribution to `χ²` with `|κ| + 1`
degrees of freedom. -/
theorem tendstoInDistribution_scoreStatistic_nbJointMLE_randomDesign
    {μX : Measure (κ → ℝ)} {p₀ : NBParam κ} (hp₀ : 0 < nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i) (lawOf (μX.prod Measure.count) nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) = 0)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo (μX.prod Measure.count) p₀ u, u⟫)
    {Ihat : ℕ → Ω → NBParam κ →L[ℝ] NBParam κ} (hIhat_meas : ∀ n, AEMeasurable (Ihat n) P)
    (hIhat : TendstoInMeasure P Ihat atTop
      (fun _ => nbRegFisherInfo (μX.prod Measure.count) p₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ + 1)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ⟪Ring.inverse (Ihat n ω) ((√n)⁻¹ • ∑ i ∈ range n, nbRegScore p₀ (X i ω)),
          (√n)⁻¹ • ∑ i ∈ range n, nbRegScore p₀ (X i ω)⟫)
      atTop Q (fun _ => P) P' :=
  tendstoInDistribution_scoreStatistic_nbJointMLE hp₀ hX_law hX_indep hs_sq hs_mean hI_pos
    hIhat_meas hIhat hQ

/-- **Wilks' theorem for the joint `(β, θ)`, simple null, random design.** The negative binomial
regression form (reference measure `μX ⊗ count`) of
`tendstoInDistribution_two_mul_logLik_sub_nbJointMLE`: the likelihood-ratio statistic at the
consistent root `p̂ n` converges in distribution to `χ²` with `|κ| + 1` degrees of freedom. -/
theorem tendstoInDistribution_two_mul_logLik_sub_nbJointMLE_randomDesign
    {μX : Measure (κ → ℝ)} {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i) (lawOf (μX.prod Measure.count) nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      nbRegFisherInfo (μX.prod Measure.count) p₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo (μX.prod Measure.count) p₀ u, u⟫)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ + 1)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ range n,
        (Real.log (nbRegDensity (phat n ω) (X i ω)) - Real.log (nbRegDensity p₀ (X i ω))))
      atTop Q (fun _ => P) P' :=
  tendstoInDistribution_two_mul_logLik_sub_nbJointMLE hδ hδθ hX_law hX_indep hM_meas hM_int hM
    hs_sq hs_mean hJ_int h_info hI_pos hphat_meas hroot hcons hQ

/-- **Wald's test for the coefficients with an estimated shape, random design.** For i.i.d.
`(xᵢ, yᵢ)` with covariates of law `μX` and counts conditionally `NB(θ₀, exp (xᵢ ⬝ᵥ β₀))`
(reference measure `μX ⊗ count`), the cross-information hypothesis of
`tendstoInDistribution_coefWaldStatistic_nbJointMLE` holds
(`inner_nbRegFisherInfo_nbShapeVec_nbCoefIncl`), so `n ⟪B̂ n (β̂ - β₀), β̂ - β₀⟫ → χ²_{|κ|}` for any
consistent estimator `B̂ n` of the coefficient block, which is `E_x[F(θ₀, x ⬝ᵥ β₀) x xᵀ]`
(`inner_nbCoefBlock_nbRegFisherInfo`). -/
theorem tendstoInDistribution_coefWaldStatistic_nbJointMLE_randomDesign
    {μX : Measure (κ → ℝ)} [SFinite μX] {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i) (lawOf (μX.prod Measure.count) nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      nbRegFisherInfo (μX.prod Measure.count) p₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo (μX.prod Measure.count) p₀ u, u⟫)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    (hκ : 0 < Fintype.card κ)
    {Bhat : ℕ → Ω → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ}
    (hBhat_meas : ∀ n, AEMeasurable (Bhat n) P)
    (hBhat : TendstoInMeasure P Bhat atTop
      (fun _ => nbCoefBlock (nbRegFisherInfo (μX.prod Measure.count) p₀)))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        n * ⟪Bhat n ω (nbCoefProj (phat n ω - p₀)), nbCoefProj (phat n ω - p₀)⟫)
      atTop Q (fun _ => P) P' :=
  tendstoInDistribution_coefWaldStatistic_nbJointMLE hδ hδθ hX_law hX_indep hM_meas hM_int hM
    hs_sq hs_mean hJ_int h_info hI_pos hphat_meas hroot hcons
    (inner_nbRegFisherInfo_nbShapeVec_nbCoefIncl (hδ.trans_le hδθ) hJ_int h_info) hκ
    hBhat_meas hBhat hQ

/-- **Wald's test for the coefficients with an estimated shape and the observed information,
random design.** The fully computable form: `B̂ n` is the coefficient block of the closed-form
observed information at `p̂ n = (β̂, θ̂)` (the merged `n⁻¹ • nbJointObsInfo`), and
`n ⟪B̂ n (β̂ - β₀), β̂ - β₀⟫ → χ²_{|κ|}`. -/
theorem tendstoInDistribution_coefWaldStatistic_nbJointMLE_obsInfo
    {μX : Measure (κ → ℝ)} [SFinite μX] {p₀ : NBParam κ} {δ : ℝ} (hδ : 0 < δ)
    (hδθ : δ ≤ nbParamShape p₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i) (lawOf (μX.prod Measure.count) nbRegDensity p₀) P)
    (hX_indep : iIndepFun X P)
    {M : (κ → ℝ) × ℕ → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hM : ∀ z, ∀ p ∈ Metric.ball p₀ δ,
      ‖nbRegObsInfo p z - nbRegObsInfo p₀ z‖ ≤ M z * ‖p - p₀‖)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) = 0)
    (hJ_int : Integrable (nbRegObsInfo p₀) (lawOf (μX.prod Measure.count) nbRegDensity p₀))
    (h_info : ∫ z, nbRegObsInfo p₀ z ∂(lawOf (μX.prod Measure.count) nbRegDensity p₀) =
      nbRegFisherInfo (μX.prod Measure.count) p₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪nbRegFisherInfo (μX.prod Measure.count) p₀ u, u⟫)
    {phat : ℕ → Ω → NBParam κ} (hphat_meas : ∀ n, AEMeasurable (phat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ range n, nbRegScore (phat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P phat atTop (fun _ => p₀))
    (hκ : 0 < Fintype.card κ)
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        n * ⟪nbCoefBlock (nbRegAvgObsInfo n (fun i => X i ω) (phat n ω))
            (nbCoefProj (phat n ω - p₀)), nbCoefProj (phat n ω - p₀)⟫)
      atTop Q (fun _ => P) P' := by
  have hB : Continuous (nbCoefBlock (κ := κ)) := by unfold nbCoefBlock; fun_prop
  exact tendstoInDistribution_coefWaldStatistic_nbJointMLE_randomDesign hδ hδθ hX_law hX_indep
    hM_meas hM_int hM hs_sq hs_mean hJ_int h_info hI_pos hphat_meas hroot hcons hκ
    (fun n => hB.measurable.comp_aemeasurable
      (aemeasurable_nbRegAvgObsInfo (fun i => (hX_law i).aemeasurable) hphat_meas n))
    ((tendstoInMeasure_nbRegAvgObsInfo hδ hδθ hX_law hX_indep hM_meas hM_int hM hJ_int h_info
      hphat_meas hcons).comp_const_of_continuousAt hB.continuousAt)
    hQ

end RandomDesign

end MathlibExt.Probability.Statistics.GLM.NegativeBinomial
