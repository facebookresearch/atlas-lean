/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.NegativeBinomialAN
public import MathlibExt.Probability.Statistics.GLM.NegativeBinomialRestrictedMLE

/-!
# Composite score and likelihood-ratio tests for `β` with the negative binomial shape free

`NegativeBinomialAN` proves the score and likelihood-ratio limits for the joint parameter
`p = (β, θ)` of random-design negative binomial regression under a **simple** null `p = p₀`.
`NegativeBinomialRestrictedMLE` proves composite score and likelihood-ratio limits for
`H₀ : β = β₀` with the shape `θ` (the `k` of the NB2 variance `μ + μ² / k`) left free, but takes
the facts it needs from the joint setup (the coefficient-score central limit theorem, the limit
information and its block structure) as explicit hypotheses, because `NegativeBinomialAN` was not
merged when it was written. This file states the composite null for the random-design model of
`NegativeBinomialAN` and discharges those hypotheses from that model.

## The composite null

* `nbCompositeNull β₀ = {p | nbParamCoef p = β₀ ∧ 0 < nbParamShape p}`: `β = β₀`, shape free.
  `nbNullParam β₀ θ` is its point with shape `θ`; `mem_nbCompositeNull_iff` and
  `eq_nbNullParam_of_mem_nbCompositeNull` show the null is exactly the half-line
  `{nbNullParam β₀ θ | θ > 0}`.

## The statistics

* `nbRegCoefScore β₀ θ n zs = n^{-1/2} Πβ ∑_{i<n} nbRegScore (β₀, θ) zᵢ`, the scaled
  coefficient score at the null with shape `θ`. `nbCoefProj_sum_nbRegScore_nbNullParam` identifies
  it with `nbCoefScoreSum` of `NegativeBinomialRestrictedMLE` (covariates `xᵢ`, offset `0`).
* `nbRegCompositeLRStat n zs p̂ β₀ θ̃ = 2 ∑_{i<n} (log f(p̂; zᵢ) - log f((β₀, θ̃); zᵢ))`, the
  composite likelihood-ratio statistic of the density `nbRegDensity`.
  `nbRegCompositeLRStat_eq_sub`: it is the simple-null statistic of `NegativeBinomialAN` at `p̂`
  minus the same statistic at `(β₀, θ̃)`; with `θ̃ = θ₀` the second term vanishes and the composite
  statistic is the simple-joint-null statistic, whose limit at a consistent root `p̂` is `χ²` with
  `|κ| + 1` degrees of freedom (`tendstoInDistribution_two_mul_logLik_sub_nbJointMLE_randomDesign`),
  not the composite `χ²_{|κ|}`.

## Asymptotic null distributions (random design, under `H₀`, true parameter `(β₀, θ₀)`)

* `tendstoInDistribution_nbRegCoefScore`: `nbRegCoefScore β₀ θ₀ n →ᵈ Πβ Y` with
  `Y ~ N(0, I(p₀))`, so the limit is `N(0, B)` with `B` the coefficient block of `I(p₀)`.
  Proved from the joint score central limit theorem (`VectorInference.tendstoInDistribution_score`).
* `tendstoInDistribution_nbRegCompositeScoreStatistic` (**composite score test**): with `θ̃` the
  restricted estimate of the shape and `B̂ → B` in probability,
  `⟪B̂⁻¹ T̃ₙ, T̃ₙ⟫ → χ²_{|κ|}`, `T̃ₙ = nbRegCoefScore β₀ θ̃ n`.
* `inner_inverse_eq_of_cross` (deterministic): with vanishing cross information,
  `⟪I⁻¹ s, s⟫ = ⟪B⁻¹ Πβ s, Πβ s⟫ + s_θ² / D`, `D = ⟪I e_θ, e_θ⟫`.
* `tendstoInDistribution_nbRegCompositeLRStat` (**composite likelihood-ratio test**):
  `2 (ℓₙ(p̂) - ℓₙ(β₀, θ̃)) → χ²_{|κ|}`.

## What is discharged and what is still a hypothesis

Discharged from `NegativeBinomialAN`: the coefficient-score central limit theorem (`hT` of
`NegativeBinomialRestrictedMLE`), the limit information `B` and its symmetry and positive
definiteness (from those of `I(p₀)`), the existence of the Gaussian limit, and, for the
likelihood-ratio test, the vanishing cross information
(`inner_nbRegFisherInfo_nbShapeVec_nbCoefIncl`), which gives the block-diagonal structure.

Still hypotheses:

* the moment conditions of `NegativeBinomialAN` (square-integrable centered score, integrable
  observed information with the information identity, positive definite `I(p₀)`);
* for the restricted estimate `θ̃`: consistency, `√n (θ̃ - θ₀)` bounded in probability, and the
  uniform law of large numbers for the cross average (as in `NegativeBinomialRestrictedMLE`);
* the two Wilks expansions of the likelihood-ratio test,
  `2 (ℓₙ(p̂) - ℓₙ(p₀)) - ⟪I⁻¹ Sₙ, Sₙ⟫ → 0` and `2 (ℓₙ(β₀, θ̃) - ℓₙ(p₀)) - (Sₙ)_θ² / D → 0`.
  `EstimatedInformation.tendstoInMeasure_two_mul_logLikelihood_sub_sub` exports the joint
  expansion only in Wald form, `n ⟪I (p̂ - p₀), p̂ - p₀⟫`. Converting it to score form needs the
  asymptotic linearity `√n (p̂ - p₀) - I⁻¹ Sₙ → 0`, which `VectorInference` proves only inside its
  estimating-equation proof and does not export; the restricted fit needs the same for `θ̃`.
  Deriving it would duplicate that proof, so both expansions stay hypotheses;
* a.e.-measurability of the two statistics.

Fixed shape: when `θ` is known there is no nuisance parameter. For the score test, taking
`θ̃ = θ₀` makes the composite score statistic the known-shape coefficient score statistic, and
the consistency and `√n`-tightness hypotheses on `θ̃` hold trivially (see the tests). This does
not extend to the likelihood-ratio test: with `θ̃ = θ₀` the numerator still uses the unrestricted
`p̂`, the statistic is the simple-joint-null statistic above, and the hypothesis `hres` of
`tendstoInDistribution_nbRegCompositeLRStat` becomes `-(Sₙ)_θ² / D → 0`, which fails when the
shape score is nondegenerate. Nothing composite is claimed for a known shape.

## References

* J. F. Lawless, "Negative binomial and mixed Poisson regression", Canad. J. Statist. 15 (1987)
  209–225, §2–3.
* A. C. Cameron and P. K. Trivedi, *Regression Analysis of Count Data*, 2nd ed. (2013), §3.3
  and §5.6.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), §16.1 and §25.4.

## Source receipt (API-00)

Reused from `NegativeBinomialAN`: `NBParam`, `nbParamCoef`, `nbParamShape`, `nbRegDensity`,
`nbRegScore`, `nbRegFisherInfo`, `score_nbRegDensity_eq`, `measurable_nbRegScore`, `nbCoefProj`,
`nbCoefIncl`, `nbShapeVec`, `nbCoefBlock` and its lemmas, `inverse_apply_nbCoefIncl_of_cross`,
`inner_nbRegFisherInfo_nbShapeVec_nbCoefIncl`. Reused from `NegativeBinomialRestrictedMLE`:
`nbCoefScoreSum`, `nbCrossAvg`, `tendstoInDistribution_nbCompositeScoreStatistic`. Reused from
`VectorInference`: `tendstoInDistribution_score`, `variance_inner_score`,
`inner_fisherInformation_comm`, `hasLaw_inner_inverse_chiSquare`, `isUnit_of_inner_self_pos`,
`inverse_apply_apply`. Reused from `MultivariateCLT`: `exists_hasLaw_inner_gaussianReal`.
Proved here: the composite null, the statistics and their identities, the inverse-information
split, and the random-design composite limits.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM.NegativeBinomial

open Finset Real Matrix ProbabilityTheory MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
open MathlibExt.Probability.Statistics.VectorInference (score fisherInformation)
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)

variable {κ : Type*} [Fintype κ]

/-! ### The composite null -/

/-- The point `(β₀, θ)` of the joint parameter space. -/
def nbNullParam (β₀ : κ → ℝ) (θ : ℝ) : NBParam κ := WithLp.toLp 2 (Sum.elim β₀ fun _ => θ)

omit [Fintype κ] in
@[simp] theorem nbParamCoef_nbNullParam (β₀ : κ → ℝ) (θ : ℝ) :
    nbParamCoef (nbNullParam β₀ θ) = β₀ := rfl

omit [Fintype κ] in
@[simp] theorem nbParamShape_nbNullParam (β₀ : κ → ℝ) (θ : ℝ) :
    nbParamShape (nbNullParam β₀ θ) = θ := rfl

/-- **The composite null `H₀ : β = β₀`** with the shape free: the parameters with coefficient
block `β₀` and any positive shape. -/
def nbCompositeNull (β₀ : κ → ℝ) : Set (NBParam κ) :=
  {p | nbParamCoef p = β₀ ∧ 0 < nbParamShape p}

omit [Fintype κ] in
theorem mem_nbCompositeNull_iff (β₀ : κ → ℝ) (θ : ℝ) :
    nbNullParam β₀ θ ∈ nbCompositeNull β₀ ↔ 0 < θ := by
  simp [nbCompositeNull]

omit [Fintype κ] in
/-- Every point of the composite null is `(β₀, θ)` for its shape `θ`. -/
theorem eq_nbNullParam_of_mem_nbCompositeNull {β₀ : κ → ℝ} {p : NBParam κ}
    (hp : p ∈ nbCompositeNull β₀) : p = nbNullParam β₀ (nbParamShape p) := by
  obtain ⟨hβ, -⟩ := hp
  ext (j | u)
  · exact congrFun hβ j
  · cases u; rfl

/-! ### The statistics -/

/-- The scaled coefficient score at the null point with shape `θ`:
`n^{-1/2} Πβ ∑_{i<n} nbRegScore (β₀, θ) zᵢ`. -/
noncomputable def nbRegCoefScore (β₀ : κ → ℝ) (θ : ℝ) (n : ℕ) (zs : ℕ → (κ → ℝ) × ℕ) :
    EuclideanSpace ℝ κ :=
  (√(n : ℝ))⁻¹ • nbCoefProj (∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ) (zs i))

/-- The composite likelihood-ratio statistic `2 ∑_{i<n} (log f(p̂; zᵢ) - log f((β₀, θ̃); zᵢ))`. -/
noncomputable def nbRegCompositeLRStat (n : ℕ) (zs : ℕ → (κ → ℝ) × ℕ) (phat : NBParam κ)
    (β₀ : κ → ℝ) (θtil : ℝ) : ℝ :=
  2 * ∑ i ∈ range n,
    (Real.log (nbRegDensity phat (zs i)) - Real.log (nbRegDensity (nbNullParam β₀ θtil) (zs i)))

/-- The projected joint score is the coefficient score `nbCoefScoreSum` of
`NegativeBinomialRestrictedMLE` with covariates `xᵢ`, counts `yᵢ` and offset `0`. -/
theorem nbCoefProj_sum_nbRegScore_nbNullParam {Ω : Type*} (X : ℕ → Ω → (κ → ℝ) × ℕ)
    (β₀ : κ → ℝ) (θ : ℝ) (n : ℕ) (ω : Ω) :
    nbCoefProj (∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ) (X i ω)) =
      nbCoefScoreSum (fun i ω => (X i ω).1) (fun _ _ => 0) (fun i ω => (X i ω).2) β₀ n ω θ := by
  ext j
  simp [nbCoefScoreSum, nbRegScore, map_sum]

/-- The composite statistic is the simple-null statistic at `p̂` minus the simple-null
statistic at `(β₀, θ̃)`, both relative to any `p₀`. -/
theorem nbRegCompositeLRStat_eq_sub (n : ℕ) (zs : ℕ → (κ → ℝ) × ℕ) (phat p₀ : NBParam κ)
    (β₀ : κ → ℝ) (θtil : ℝ) :
    nbRegCompositeLRStat n zs phat β₀ θtil =
      2 * ∑ i ∈ range n, (Real.log (nbRegDensity phat (zs i)) -
        Real.log (nbRegDensity p₀ (zs i))) -
      2 * ∑ i ∈ range n, (Real.log (nbRegDensity (nbNullParam β₀ θtil) (zs i)) -
        Real.log (nbRegDensity p₀ (zs i))) := by
  rw [nbRegCompositeLRStat, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### The inverse information splits into coefficient and shape parts -/

/-- If the cross term vanishes, the shape direction is an eigenvector: `I e_θ = D e_θ`. -/
theorem apply_nbShapeVec_of_cross [DecidableEq κ] {I : NBParam κ →L[ℝ] NBParam κ}
    (hcross : ∀ t, ⟪I nbShapeVec, nbCoefIncl t⟫ = 0) :
    I nbShapeVec = ⟪I nbShapeVec, nbShapeVec⟫ • nbShapeVec := by
  have h0 : nbCoefProj (I nbShapeVec) = 0 :=
    ext_inner_right ℝ fun t => by rw [inner_nbCoefProj, hcross, inner_zero_left]
  conv_lhs => rw [← nbCoefIncl_nbCoefProj_add (I nbShapeVec), h0, map_zero, zero_add]
  rw [inner_nbShapeVec]

theorem inner_nbCoefIncl_nbShapeVec [DecidableEq κ] (t : EuclideanSpace ℝ κ) :
    ⟪nbCoefIncl t, nbShapeVec⟫ = 0 := by
  rw [inner_nbShapeVec, nbCoefIncl_apply_inr]

theorem inner_nbShapeVec_self [DecidableEq κ] : ⟪(nbShapeVec : NBParam κ), nbShapeVec⟫ = 1 := by
  rw [inner_nbShapeVec]; simp [nbShapeVec]

/-- **The inverse-information quadratic form splits.** For a symmetric positive definite `I`
with vanishing cross term, `⟪I⁻¹ s, s⟫ = ⟪B⁻¹ Πβ s, Πβ s⟫ + s_θ² / D` with `B` the coefficient
block and `D = ⟪I e_θ, e_θ⟫`. -/
theorem inner_inverse_eq_of_cross [DecidableEq κ] {I : NBParam κ →L[ℝ] NBParam κ}
    (hI_symm : ∀ u v, ⟪I u, v⟫ = ⟪u, I v⟫) (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪I u, u⟫)
    (hcross : ∀ t, ⟪I nbShapeVec, nbCoefIncl t⟫ = 0) (s : NBParam κ) :
    ⟪Ring.inverse I s, s⟫ =
      ⟪Ring.inverse (nbCoefBlock I) (nbCoefProj s), nbCoefProj s⟫ +
        s (Sum.inr ()) ^ 2 / ⟪I nbShapeVec, nbShapeVec⟫ := by
  have hI : IsUnit I := VectorInference.isUnit_of_inner_self_pos hI_pos
  set D := ⟪I nbShapeVec, nbShapeVec⟫ with hDdef
  have hD : 0 < D := hI_pos _ fun h => by
    have := congrArg (fun v : NBParam κ => v (Sum.inr ())) h
    simp [nbShapeVec] at this
  have hIe : Ring.inverse I nbShapeVec = D⁻¹ • nbShapeVec := by
    have h := VectorInference.inverse_apply_apply hI nbShapeVec
    rw [apply_nbShapeVec_of_cross hcross, map_smul] at h
    rw [eq_inv_smul_iff₀ hD.ne']
    exact h
  set t := nbCoefProj s
  set a := s (Sum.inr ())
  have hs : s = nbCoefIncl t + a • nbShapeVec := (nbCoefIncl_nbCoefProj_add s).symm
  conv_lhs => rw [hs]
  rw [map_add, map_smul, inverse_apply_nbCoefIncl_of_cross hI_symm hI_pos hcross, hIe]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_nbCoefIncl, inner_nbCoefIncl_nbShapeVec, inner_nbShapeVec_self]
  rw [real_inner_comm (nbCoefIncl t) nbShapeVec, inner_nbCoefIncl_nbShapeVec]
  field_simp
  ring

/-! ### Asymptotic null distributions, random design -/

section RandomDesign

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- A Gaussian vector with covariance the Fisher information of the joint model, on
`stdGaussian`: the limit object of the score central limit theorem. -/
theorem exists_hasLaw_inner_nbRegFisherInfo {ν : Measure ((κ → ℝ) × ℕ)} {p₀ : NBParam κ}
    (hp₀ : 0 < nbParamShape p₀) {X₀ : Ω → (κ → ℝ) × ℕ}
    (hX_law : HasLaw X₀ (lawOf ν nbRegDensity p₀) P)
    (hs_sq : Integrable (fun z => ‖nbRegScore p₀ z‖ ^ 2) (lawOf ν nbRegDensity p₀))
    (hs_mean : ∫ z, nbRegScore p₀ z ∂(lawOf ν nbRegDensity p₀) = 0) :
    ∃ Y : NBParam κ →L[ℝ] NBParam κ, ∀ t, HasLaw (fun z => ⟪Y z, t⟫)
      (gaussianReal 0 (⟪nbRegFisherInfo ν p₀ t, t⟫).toNNReal) (stdGaussian (NBParam κ)) := by
  have hs_meas : Measurable (score nbRegDensity p₀) := by
    rw [score_nbRegDensity_eq hp₀]; exact measurable_nbRegScore p₀
  have hs_sq' : Integrable (fun z => ‖score nbRegDensity p₀ z‖ ^ 2)
      (lawOf ν nbRegDensity p₀) := by
    rwa [score_nbRegDensity_eq hp₀]
  have hs_mean' : ∫ z, score nbRegDensity p₀ z ∂(lawOf ν nbRegDensity p₀) = 0 := by
    rwa [score_nbRegDensity_eq hp₀]
  have : IsProbabilityMeasure (lawOf ν nbRegDensity p₀) :=
    hX_law.isProbabilityMeasure_iff.1 inferInstance
  have hs : MemLp (score nbRegDensity p₀) 2 (lawOf ν nbRegDensity p₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq'
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal (hX_law.memLp_comp hs)
  refine ⟨A, fun t => ?_⟩
  have h := hA t
  rwa [show (fun ω => ⟪(score nbRegDensity p₀ ∘ X₀) ω, t⟫) =
      fun ω => ⟪score nbRegDensity p₀ (X₀ ω), t⟫ from rfl,
    VectorInference.variance_inner_score hX_law hs_meas hs_sq' hs_mean' t] at h

/-- The projection `Πβ Y` of a Gaussian vector `Y ~ N(0, I)` is `N(0, B)`, `B` the coefficient
block of `I`. -/
theorem hasLaw_inner_nbCoefProj {Ω'' : Type*} [MeasurableSpace Ω''] {P'' : Measure Ω''}
    {I : NBParam κ →L[ℝ] NBParam κ} {Y : Ω'' → NBParam κ}
    (hY : ∀ t, HasLaw (fun z => ⟪Y z, t⟫) (gaussianReal 0 (⟪I t, t⟫).toNNReal) P'')
    (t : EuclideanSpace ℝ κ) :
    HasLaw (fun z => ⟪nbCoefProj (Y z), t⟫) (gaussianReal 0 (⟪nbCoefBlock I t, t⟫).toNNReal)
      P'' := by
  simp_rw [inner_nbCoefProj]
  rw [nbCoefBlock, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    inner_nbCoefProj]
  exact hY (nbCoefIncl t)

/-- **Central limit theorem for the coefficient score under `H₀`, random design.** For i.i.d.
`(xᵢ, yᵢ)` of random-design negative binomial regression with true parameter `(β₀, θ₀)`,
`θ₀ > 0`, and a square-integrable centered score, the scaled coefficient score at the truth
converges in distribution to `Πβ Y` for every `Y` with `⟪Y, t⟫ ~ N(0, ⟪I(p₀) t, t⟫)`; that is,
to `N(0, B)` with `B` the coefficient block of `I(p₀)`. This is the hypothesis `hT` of
`NegativeBinomialRestrictedMLE`, discharged. -/
theorem tendstoInDistribution_nbRegCoefScore {μX : Measure (κ → ℝ)} {β₀ : κ → ℝ} {θ₀ : ℝ}
    (hθ₀ : 0 < θ₀) {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) P)
    (hX_indep : iIndepFun X P)
    (hs_sq : Integrable (fun z => ‖nbRegScore (nbNullParam β₀ θ₀) z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)))
    (hs_mean : ∫ z, nbRegScore (nbNullParam β₀ θ₀) z
      ∂(lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) = 0)
    {Y : Ω' → NBParam κ} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫) (gaussianReal 0
      (⟪nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀) t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => nbRegCoefScore β₀ θ₀ n fun i => X i ω) atTop
      (fun ω => nbCoefProj (Y ω)) (fun _ => P) P' := by
  have hp₀ : 0 < nbParamShape (nbNullParam β₀ θ₀) := hθ₀
  have h := VectorInference.tendstoInDistribution_score hX_law hX_indep
    (by rw [score_nbRegDensity_eq hp₀]; exact measurable_nbRegScore _)
    (by rwa [score_nbRegDensity_eq hp₀]) (by rwa [score_nbRegDensity_eq hp₀]) hY_meas hY
  simp only [score_nbRegDensity_eq hp₀] at h
  have h2 := h.continuous_comp nbCoefProj.continuous
  have heq : (fun (n : ℕ) ω => nbRegCoefScore β₀ θ₀ n fun i => X i ω) = fun (n : ℕ) =>
      nbCoefProj ∘ fun ω =>
        (√(n : ℝ))⁻¹ • ∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ₀) (X i ω) := by
    funext n ω
    simp [nbRegCoefScore, map_smul]
  rw [heq]
  exact h2

/-- **Composite score test for `H₀ : β = β₀` with the shape free, random design.** Let
`(xᵢ, yᵢ)` be i.i.d. random-design negative binomial regression data with true parameter
`(β₀, θ₀)`, under the moment conditions of `NegativeBinomialAN` (square-integrable centered
score, positive definite information `I(p₀)`). Let `θ̃ n` be a restricted estimate of the shape
under `H₀` that is consistent with `√n (θ̃ n - θ₀)` bounded in probability, and assume the
uniform law of large numbers for the cross average on `|θ - θ₀| ≤ δ < θ₀` (the
restricted-estimate hypotheses of `NegativeBinomialRestrictedMLE`). Let `B̂ n` be a.e.-measurable
and consistent for the coefficient block `B` of `I(p₀)`. Then the Rao statistic
`⟪B̂⁻¹ T̃ₙ, T̃ₙ⟫`, `T̃ₙ = n^{-1/2} Πβ ∑_{i<n} nbRegScore (β₀, θ̃ n) zᵢ`, converges in distribution
to `χ²_{|κ|}`. The score central limit theorem and the limit information are those of the model,
not hypotheses. -/
theorem tendstoInDistribution_nbRegCompositeScoreStatistic [Nonempty κ]
    {μX : Measure (κ → ℝ)} {β₀ : κ → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ) (hδθ : δ < θ₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) P)
    (hX_indep : iIndepFun X P)
    (hs_sq : Integrable (fun z => ‖nbRegScore (nbNullParam β₀ θ₀) z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)))
    (hs_mean : ∫ z, nbRegScore (nbNullParam β₀ θ₀) z
      ∂(lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) = 0)
    (hI_pos : ∀ u, u ≠ 0 →
      0 < ⟪nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀) u, u⟫)
    {θtil : ℕ → Ω → ℝ} (hcons : TendstoInMeasure P θtil atTop (fun _ => θ₀))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, P {ω | C < √(n : ℝ) * |θtil n ω - θ₀|} ≤ ε)
    (hcross : ∀ ε > 0, Tendsto (fun n : ℕ => P {ω | ∃ c ∈ Metric.closedBall θ₀ δ,
      ε ≤ ‖nbCrossAvg (fun i ω => (X i ω).1) (fun _ _ => 0) (fun i ω => (X i ω).2) β₀ n ω c‖})
      atTop (𝓝 0))
    (hTtil_meas : ∀ n : ℕ,
      AEMeasurable (fun ω => nbRegCoefScore β₀ (θtil n ω) n fun i => X i ω) P)
    {Bhat : ℕ → Ω → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ}
    (hBhat_meas : ∀ n, AEMeasurable (Bhat n) P)
    (hBhat : TendstoInMeasure P Bhat atTop
      (fun _ => nbCoefBlock (nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀))))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ)) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        ⟪Ring.inverse (Bhat n ω) (nbRegCoefScore β₀ (θtil n ω) n fun i => X i ω),
          nbRegCoefScore β₀ (θtil n ω) n fun i => X i ω⟫)
      atTop Q (fun _ => P) P' := by
  have hθ₀ : 0 < θ₀ := hδ.trans hδθ
  obtain ⟨Y, hY⟩ := exists_hasLaw_inner_nbRegFisherInfo (p₀ := nbNullParam β₀ θ₀) hθ₀ (hX_law 0)
    hs_sq hs_mean
  have hT := tendstoInDistribution_nbRegCoefScore hθ₀ hX_law hX_indep hs_sq hs_mean
    Y.continuous.measurable.aemeasurable hY
  have hscore : ∀ (θ : ℝ) (n : ℕ) (ω : Ω), (nbRegCoefScore β₀ θ n fun i => X i ω) =
      (√(n : ℝ))⁻¹ • nbCoefScoreSum (fun i ω => (X i ω).1) (fun _ _ => 0)
        (fun i ω => (X i ω).2) β₀ n ω θ := fun θ n ω => by
    rw [nbRegCoefScore, nbCoefProj_sum_nbRegScore_nbNullParam]
  simp only [hscore] at hT hTtil_meas ⊢
  exact tendstoInDistribution_nbCompositeScoreStatistic (fun i ω => (X i ω).1) (fun _ _ => 0)
    (fun i ω => (X i ω).2) β₀ hδ hδθ hcons htight hcross
    (inner_nbCoefBlock_comm fun u v => VectorInference.inner_fisherInformation_comm _ _ _ u v)
    (inner_nbCoefBlock_self_pos hI_pos)
    (nbCoefProj.continuous.comp Y.continuous).measurable.aemeasurable
    (hasLaw_inner_nbCoefProj hY) hT hTtil_meas hBhat_meas hBhat hQ

/-- **Composite likelihood-ratio test for `H₀ : β = β₀` with the shape free, random design.**
Let `(xᵢ, yᵢ)` be i.i.d. random-design negative binomial regression data (covariates of law
`μX`) with true parameter `p₀ = (β₀, θ₀)`, `θ₀ > 0`, under the moment conditions of
`NegativeBinomialAN` (square-integrable centered score, integrable observed information with the
information identity, positive definite `I = I(p₀)`). Let `Sₙ = n^{-1/2} ∑_{i<n} nbRegScore p₀ zᵢ`
and `D = ⟪I e_θ, e_θ⟫`. Assume the Wilks expansions

* `2 (ℓₙ(p̂ n) - ℓₙ(p₀)) - ⟪I⁻¹ Sₙ, Sₙ⟫ → 0` in probability (joint estimate `p̂ n`),
* `2 (ℓₙ(β₀, θ̃ n) - ℓₙ(p₀)) - (Sₙ)_θ² / D → 0` in probability (restricted estimate `θ̃ n`),

and that the statistic is a.e.-measurable. Then `2 (ℓₙ(p̂ n) - ℓₙ(β₀, θ̃ n)) → χ²_{|κ|}`. The
vanishing cross information, which makes the shape parts of the two expansions cancel, and the
coefficient-score central limit theorem are proved from the model. -/
theorem tendstoInDistribution_nbRegCompositeLRStat [DecidableEq κ] [Nonempty κ]
    {μX : Measure (κ → ℝ)} [SFinite μX] {β₀ : κ → ℝ} {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {X : ℕ → Ω → (κ → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) P)
    (hX_indep : iIndepFun X P)
    (hs_sq : Integrable (fun z => ‖nbRegScore (nbNullParam β₀ θ₀) z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)))
    (hs_mean : ∫ z, nbRegScore (nbNullParam β₀ θ₀) z
      ∂(lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) = 0)
    (hJ_int : Integrable (nbRegObsInfo (nbNullParam β₀ θ₀))
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)))
    (h_info : ∫ z, nbRegObsInfo (nbNullParam β₀ θ₀) z
        ∂(lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) =
      nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀))
    (hI_pos : ∀ u, u ≠ 0 →
      0 < ⟪nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀) u, u⟫)
    {phat : ℕ → Ω → NBParam κ} {θtil : ℕ → Ω → ℝ}
    (hfull : TendstoInMeasure P (fun (n : ℕ) ω =>
      2 * ∑ i ∈ range n, (Real.log (nbRegDensity (phat n ω) (X i ω)) -
        Real.log (nbRegDensity (nbNullParam β₀ θ₀) (X i ω))) -
      ⟪Ring.inverse (nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀))
          ((√(n : ℝ))⁻¹ • ∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ₀) (X i ω)),
        (√(n : ℝ))⁻¹ • ∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ₀) (X i ω)⟫) atTop 0)
    (hres : TendstoInMeasure P (fun (n : ℕ) ω =>
      2 * ∑ i ∈ range n, (Real.log (nbRegDensity (nbNullParam β₀ (θtil n ω)) (X i ω)) -
        Real.log (nbRegDensity (nbNullParam β₀ θ₀) (X i ω))) -
      ((√(n : ℝ))⁻¹ • ∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ₀) (X i ω)) (Sum.inr ()) ^ 2 /
        ⟪nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀) nbShapeVec, nbShapeVec⟫)
      atTop 0)
    (hLR_meas : ∀ n : ℕ, AEMeasurable
      (fun ω => nbRegCompositeLRStat n (fun i => X i ω) (phat n ω) β₀ (θtil n ω)) P)
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => nbRegCompositeLRStat n (fun i => X i ω) (phat n ω) β₀ (θtil n ω))
      atTop Q (fun _ => P) P' := by
  set I := nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀) with hIdef
  set B := nbCoefBlock I with hBdef
  have hI_symm : ∀ u v, ⟪I u, v⟫ = ⟪u, I v⟫ := fun u v =>
    VectorInference.inner_fisherInformation_comm _ _ _ u v
  have hcross : ∀ t, ⟪I nbShapeVec, nbCoefIncl t⟫ = 0 :=
    inner_nbRegFisherInfo_nbShapeVec_nbCoefIncl (p₀ := nbNullParam β₀ θ₀) hθ₀ hJ_int h_info
  obtain ⟨Y, hY⟩ := exists_hasLaw_inner_nbRegFisherInfo (p₀ := nbNullParam β₀ θ₀) hθ₀ (hX_law 0)
    hs_sq hs_mean
  have hT := tendstoInDistribution_nbRegCoefScore hθ₀ hX_law hX_indep hs_sq hs_mean
    Y.continuous.measurable.aemeasurable hY
  have hd : 0 < Module.finrank ℝ (EuclideanSpace ℝ κ) := by
    rw [finrank_euclideanSpace]; exact Fintype.card_pos
  rw [← finrank_euclideanSpace (𝕜 := ℝ) (ι := κ)] at hQ
  have hchi := VectorInference.hasLaw_inner_inverse_chiSquare (inner_nbCoefBlock_comm hI_symm)
    (inner_nbCoefBlock_self_pos hI_pos) hd
    (nbCoefProj.continuous.comp Y.continuous).measurable.aemeasurable (hasLaw_inner_nbCoefProj hY)
  have hQn := (hT.continuous_comp (g := fun v => ⟪Ring.inverse B v, v⟫)
    (by fun_prop)).of_map_eq hQ.aemeasurable (by rw [hQ.map_eq, ← hchi.map_eq]; rfl)
  have hneg : ∀ {V : ℕ → Ω → ℝ}, TendstoInMeasure P V atTop 0 →
      TendstoInMeasure P (fun n ω => -V n ω) atTop 0 := fun hV => by
    rw [tendstoInMeasure_iff_norm] at hV ⊢
    simpa only [Pi.zero_apply, sub_zero, norm_neg] using hV
  have hdiff := tendstoInMeasure_add_zero hfull (hneg hres)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Q hQn ?_ hLR_meas
  refine hdiff.congr_left fun n => ae_of_all _ fun ω => ?_
  simp only [Pi.sub_apply, Function.comp_apply]
  rw [nbRegCompositeLRStat_eq_sub _ _ _ (nbNullParam β₀ θ₀),
    inner_inverse_eq_of_cross hI_symm hI_pos hcross, nbRegCoefScore, map_smul]
  ring

end RandomDesign

end MathlibExt.Probability.Statistics.GLM.NegativeBinomial
