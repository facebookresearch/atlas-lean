/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.Sandwich
public import MathlibExt.Probability.Statistics.VectorInference
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.CentralLimitTheorem

/-!
# General estimating equations: cluster sandwich and asymptotic linearity

This file covers two gap targets that are deliberately **general** (IID units with a
finite-dimensional estimating equation), not GEE-specific.

## S16.1: cluster estimating equations with sandwich covariance

For IID independent **clusters** (the cluster is the IID unit; no independence is assumed
*within* a cluster since the estimating function consumes the whole cluster at once), a
consistent root of a finite-dimensional estimating equation with nonsingular limiting
Jacobian `A = E Dψ θ₀` and a finite-variance cluster score has asymptotic covariance
`A⁻¹ B A⁻ᵀ`, where `B = E ψ θ₀ ψ θ₀ᵀ` is the second-moment operator of the cluster score:
Mathlib's (uncentered) `covarianceOperator (μC.map (ψ θ₀))`, which is also the covariance
of the score because `E ψ θ₀ = 0`.

The asymptotic regime is `n → ∞` clusters drawn IID from one fixed cluster law `μC`.
Cluster sizes and within-cluster structure may vary at random, but only as variation drawn
from that fixed law; cluster sizes or laws that change with `n` or differ between clusters
are not covered. Independent, non-identically distributed clusters are treated in
`Longitudinal/GEE/Sandwich.lean` (vector parameter) and triangular arrays of clusters in
`Longitudinal/GEE/NonlinearTriangular.lean` (scalar parameter).

The proof reuses the vector Z-estimator theorem
`VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation` (applied with
the cluster as the IID unit), whose own proof runs through the multivariate CLT
(`tendstoInDistribution_inv_sqrt_smul_sum_sub`), a vector Taylor step with a Lipschitz
uniform remainder (`norm_sub_sub_fderiv_le`, `norm_avg_add_avg_apply_le`), and Slutsky's
theorem (`tendstoInDistribution_of_tendstoInMeasure_sub`). Its limit `-A⁻¹ Y` is then
identified with `N(0, A⁻¹ B A⁻ᵀ)` through the repository's sandwich operator
`ProbabilityTheory.GEE.sandwichCovariance A B` and its quadratic form
`ProbabilityTheory.GEE.inner_sandwichCovariance_apply`.

## S16.3: asymptotically linear estimators

For an asymptotically linear estimator with an integrable, square-integrable, mean-zero
influence function, `√n (θ̂ₙ - θ) = n^{-1/2} ∑ φ(Xᵢ) + oₚ(1)` with `E φ = 0`, `φ ∈ L²`, the
normal limit follows from the shared scalar/vector CLT plus Slutsky: the scalar case
(`tendstoInDistribution_of_asymptoticallyLinear`) via Mathlib's
`tendstoInDistribution_inv_sqrt_mul_sum_sub`, the vector case
(`tendstoInDistribution_of_asymptoticallyLinear_vector`) via
`tendstoInDistribution_inv_sqrt_smul_sum_comp`. The `oₚ(1)` remainder is an explicit
hypothesis (`hrem`); in particular the cross-fitted nuisance product-rate `oₚ(n^{-1/2})`
remainder bound is a separate obligation and is assumed here, not proved.

## Main statements

* `tendstoInDistribution_sqrt_smul_sub_of_clusterEstimatingEquation`: the cluster
  sandwich theorem, `√n (θ̂ₙ - θ₀) ⇒ Z` with `⟪Z, t⟫ ~ N(0, ⟪A⁻¹ B A⁻ᵀ t, t⟫)`, where
  `A⁻¹ B A⁻ᵀ = sandwichCovariance A B` and `B = covarianceOperator (μC.map (ψ θ₀))`.
* `covarianceOperator_map_eq_integral_rankOne`: that meat is the rank-one integral
  `∫ ψ θ₀ ψ θ₀ᵀ dμC`, the form of `VectorInference.fisherInformation`, and
  `sandwichCovariance_integral_rankOne`: the sandwich of a rank-one meat is the plain
  `A⁻¹ B A⁻ᵀ`, since that meat is self-adjoint.
* `hasLaw_inner_neg_inverse_apply_sandwich`: the limit `-A⁻¹ Y` of the vector Z-estimator
  theorem has projection laws `N(0, ⟪sandwichCovariance A B t, t⟫)`.
* `sandwich_score_eq_inverse_fisherInformation`: for a correctly specified score the
  sandwich collapses to the inverse information, `sandwichCovariance A B = I(θ₀)⁻¹`.
* `IsInfluenceFunction`: `φ` measurable, integrable and in `L²`, with mean zero.
* `tendstoInDistribution_of_asymptoticallyLinear` (scalar),
  `tendstoInDistribution_of_asymptoticallyLinear_vector` (vector): normal limits for
  asymptotically linear estimators.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.EstimatingEquations

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.VectorInference
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)

/-! ### The cluster sandwich theorem (S16.1) -/

/-- **Asymptotic normality of a consistent root of a cluster estimating equation**
(sandwich form). Let clusters `X 0, X 1, …` be IID with law `μC` (no independence is
assumed within a cluster: `ψ` consumes the whole cluster), and let
`ψ : E → 𝓒 → E` satisfy, for every cluster and every `θ` in the ball of radius
`δ > 0` about `θ₀`: `θ ↦ ψ θ x` is differentiable with derivative `Dψ θ x` obeying the
Lipschitz uniform remainder `‖Dψ θ x - Dψ θ₀ x‖ ≤ M x ‖θ - θ₀‖` for an integrable `M`.
Assume `E ψ θ₀ = 0` with finite second moment, `Dψ θ₀` strongly measurable and
integrable, and the limiting Jacobian `A = E Dψ θ₀` **nonsingular**. Let `θhat n` solve
`∑_{i<n} ψ θ (X i) = 0` with probability tending to one and converge to `θ₀` in
probability. Then `√n (θhat n - θ₀) ⇒ Z` in distribution, where
`⟪Z, t⟫ ~ N(0, ⟪A⁻¹ B A⁻ᵀ t, t⟫)`, with the sandwich `A⁻¹ B A⁻ᵀ = sandwichCovariance A B`
and `B = covarianceOperator (μC.map (ψ θ₀))` the second-moment operator of the cluster
score. All clusters share the law `μC`; cluster laws that vary between clusters or with `n`
are not covered. -/
theorem tendstoInDistribution_sqrt_smul_sub_of_clusterEstimatingEquation
    {𝓒 : Type*} [MeasurableSpace 𝓒]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P']
    {μC : Measure 𝓒} {X : ℕ → Ω → 𝓒}
    (hX_law : ∀ i, HasLaw (X i) μC P)
    (hX_indep : iIndepFun X P)
    {ψ : E → 𝓒 → E} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    (hψ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => ψ t x) θ)
    {M : 𝓒 → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable M μC)
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => ψ t x) θ -
        fderiv ℝ (fun t => ψ t x) θ₀‖ ≤ M x * ‖θ - θ₀‖)
    (hψ_meas : Measurable (ψ θ₀))
    (hψ_sq : Integrable (fun x => ‖ψ θ₀ x‖ ^ 2) μC)
    (hψ_mean : ∫ x, ψ θ₀ x ∂μC = 0)
    (hψ'_meas : StronglyMeasurable
      fun x => fderiv ℝ (fun t => ψ t x) θ₀)
    (hψ'_int : Integrable
      (fun x => fderiv ℝ (fun t => ψ t x) θ₀) μC)
    (hA : IsUnit (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC))
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n,
      ψ (θhat n ω) (X i ω) ≠ 0}) atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Z : Ω' → E} (hZ_meas : AEMeasurable Z P')
    (hZ : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0
        (⟪GEE.sandwichCovariance (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC)
          (covarianceOperator (μC.map (ψ θ₀))) t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (θhat n ω - θ₀))
      atTop Z (fun _ => P) P' := by
  have hProb : IsProbabilityMeasure μC :=
    (hX_law 0).isProbabilityMeasure_iff.1 inferInstance
  have hMemLp : MemLp (ψ θ₀) 2 μC :=
    (memLp_two_iff_integrable_sq_norm
      hψ_meas.aestronglyMeasurable).2 hψ_sq
  obtain ⟨G, hG⟩ :=
    exists_hasLaw_inner_gaussianReal ((hX_law 0).memLp_comp hMemLp)
  have hvar : ∀ t : E, Var[fun ω => ⟪(ψ θ₀ ∘ X 0) ω, t⟫; P] =
      ∫ x, ⟪ψ θ₀ x, t⟫ ^ 2 ∂μC := fun t => by
    have hinner : Measurable fun x : 𝓒 => ⟪ψ θ₀ x, t⟫ :=
      (continuous_id.inner continuous_const).measurable.comp hψ_meas
    have hL2 : MemLp (fun ω => ⟪(ψ θ₀ ∘ X 0) ω, t⟫) 2 P :=
      (hX_law 0).memLp_comp (hMemLp.inner_const t)
    have hmean : P[fun ω => ⟪(ψ θ₀ ∘ X 0) ω, t⟫] = 0 := by
      change ∫ ω, ((fun x => ⟪ψ θ₀ x, t⟫) ∘ X 0) ω ∂P = 0
      rw [(hX_law 0).integral_comp
        (f := fun x => ⟪ψ θ₀ x, t⟫) hinner.aestronglyMeasurable]
      simp_rw [real_inner_comm t]
      rw [integral_inner (hMemLp.integrable one_le_two), hψ_mean,
        inner_zero_right]
    change Var[fun ω => ⟪(ψ θ₀ ∘ X 0) ω, t⟫; P] = _
    rw [variance_of_integral_eq_zero hL2.aemeasurable hmean]
    change ∫ ω, ((fun x => ⟪ψ θ₀ x, t⟫ ^ 2) ∘ X 0) ω ∂P = _
    rw [(hX_law 0).integral_comp
      (f := fun x => ⟪ψ θ₀ x, t⟫ ^ 2)
      (hinner.pow_const 2).aestronglyMeasurable]
  have hG' : ∀ t : E, HasLaw (fun z => ⟪G z, t⟫)
      (gaussianReal 0
        (∫ x, ⟪ψ θ₀ x, t⟫ ^ 2 ∂μC).toNNReal)
      (stdGaussian E) := fun t => by
    have h := hG t
    rwa [hvar t] at h
  have hlim : TendstoInDistribution
      (fun (n : ℕ) ω => √n • (θhat n ω - θ₀)) atTop
      (fun z => -Ring.inverse
        (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC) (G z))
      (fun _ => P) (stdGaussian E) :=
    tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation
      hX_law hX_indep hδ hψ_diff hM_meas hM_int hM hψ_meas hψ_sq
      hψ_mean hψ'_meas hψ'_int hA hθ_meas hroot hcons
      G.continuous.aemeasurable hG'
  have hB : ∀ s : E, ⟪covarianceOperator (μC.map (ψ θ₀)) s, s⟫ =
      ∫ x, ⟪ψ θ₀ x, s⟫ ^ 2 ∂μC := fun s => by
    have hμ : MemLp id 2 (μC.map (ψ θ₀)) :=
      (memLp_map_measure_iff aestronglyMeasurable_id
        hψ_meas.aemeasurable).2 hMemLp
    have hcont : Continuous fun z : E => ⟪s, z⟫ * ⟪s, z⟫ :=
      (continuous_const.inner continuous_id).mul
        (continuous_const.inner continuous_id)
    rw [covarianceOperator_inner hμ s s,
      integral_map hψ_meas.aemeasurable hcont.aestronglyMeasurable]
    congr 1
    funext x
    rw [real_inner_comm (ψ θ₀ x) s, sq]
  have hGZ : ∀ t : E, HasLaw
      (fun ω => ⟪(-Ring.inverse
        (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC) (G ω)), t⟫)
      (gaussianReal 0
        (⟪GEE.sandwichCovariance (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC)
          (covarianceOperator (μC.map (ψ θ₀))) t, t⟫).toNNReal)
      (stdGaussian E) := fun t => by
    have e : (fun ω => ⟪(-Ring.inverse
        (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC) (G ω)), t⟫) =
        -(fun ω => ⟪G ω, ContinuousLinearMap.adjoint
          (Ring.inverse (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC)) t⟫) := by
      funext ω
      simp only [Pi.neg_apply]
      rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_right]
    rw [e, GEE.inner_sandwichCovariance_apply, hB]
    simpa using gaussianReal_neg (hG' _)
  refine hlim.of_map_eq hZ_meas (map_eq_of_forall_map_inner ?_ hZ_meas
    fun t => ?_)
  · exact ((-Ring.inverse
      (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC)).continuous.measurable.comp_aemeasurable
      G.continuous.aemeasurable)
  · show (stdGaussian E).map
        (fun ω => ⟪(-Ring.inverse
          (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC) (G ω)), t⟫) =
        P'.map (fun ω => ⟪Z ω, t⟫)
    rw [(hGZ t).map_eq, (hZ t).map_eq]

/-! ### Rank-one meat, sandwich projection laws and the Fisher collapse -/

/-- **The cluster meat is the rank-one integral.** For a measurable, square-integrable `ψ₀`,
the second-moment operator `covarianceOperator (μX.map ψ₀)` of
`tendstoInDistribution_sqrt_smul_sub_of_clusterEstimatingEquation` is the Bochner integral
`∫ ψ₀ ψ₀ᵀ dμX` of the rank-one operators `InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x)`, the form
of `VectorInference.fisherInformation`. -/
theorem covarianceOperator_map_eq_integral_rankOne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {𝓧 : Type*} [MeasurableSpace 𝓧]
    {μX : Measure 𝓧} {ψ₀ : 𝓧 → E} (hψ_meas : Measurable ψ₀)
    (hψ_sq : Integrable (fun x => ‖ψ₀ x‖ ^ 2) μX) :
    covarianceOperator (μX.map ψ₀) = ∫ x, InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x) ∂μX := by
  have hs : MemLp ψ₀ 2 μX :=
    (memLp_two_iff_integrable_sq_norm hψ_meas.aestronglyMeasurable).2 hψ_sq
  have hμ : MemLp id 2 (μX.map ψ₀) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hψ_meas.aemeasurable).2 hs
  have hrank : Continuous fun s : E => InnerProductSpace.rankOne ℝ s s := by
    have e : (fun s : E => InnerProductSpace.rankOne ℝ s s) =
        fun s => ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ s) s := by
      funext s; ext v; simp
    rw [e]
    exact (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp
      ((innerSL ℝ).continuous.prodMk continuous_id)
  have hV : Integrable (fun x => InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x)) μX := by
    refine Integrable.mono' hψ_sq (hrank.comp_aestronglyMeasurable hs.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [InnerProductSpace.norm_rankOne, sq]
  have hcont : ∀ u : E, Continuous fun y : E => ⟪u, y⟫ • y :=
    fun u => (continuous_const.inner continuous_id).smul continuous_id
  refine ContinuousLinearMap.ext fun u => ?_
  rw [covarianceOperator_apply hμ, integral_map hψ_meas.aemeasurable
    (hcont u).aestronglyMeasurable, ContinuousLinearMap.integral_apply hV]
  congr 1
  funext x
  rw [InnerProductSpace.rankOne_apply, real_inner_comm]

/-- **The canonical sandwich of a rank-one meat.** The rank-one integral
`V = ∫ ψ₀ ψ₀ᵀ dμX` is self-adjoint (its bilinear form `∫ ⟪ψ₀, u⟫ ⟪ψ₀, v⟫ dμX` is symmetric, and
a non-integrable `x ↦ ψ₀ x ψ₀ xᵀ` gives the junk value `0`), so the repository's symmetrized
sandwich `GEE.sandwichCovariance D V` is the plain `D⁻¹ V (D⁻¹)*`, with `D⁻¹ = Ring.inverse D`
and `(D⁻¹)*` its adjoint. No integrability or invertibility is assumed. -/
theorem sandwichCovariance_integral_rankOne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {𝓧 : Type*} [MeasurableSpace 𝓧] (μX : Measure 𝓧) (ψ₀ : 𝓧 → E) (D : E →L[ℝ] E) :
    GEE.sandwichCovariance D (∫ x, InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x) ∂μX) =
      Ring.inverse D ∘L (∫ x, InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x) ∂μX) ∘L
        ContinuousLinearMap.adjoint (Ring.inverse D) := by
  have hV : IsSelfAdjoint (∫ x, InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x) ∂μX) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    simp only [ContinuousLinearMap.coe_coe]
    by_cases h : Integrable (fun x => InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x)) μX
    · rw [ContinuousLinearMap.integral_apply h, ContinuousLinearMap.integral_apply h,
        real_inner_comm v, ← integral_inner (h.apply_continuousLinearMap u),
        ← integral_inner (h.apply_continuousLinearMap v)]
      congr 1
      funext x
      simp only [InnerProductSpace.rankOne_apply, real_inner_smul_right]
      rw [real_inner_comm (ψ₀ x) v, real_inner_comm (ψ₀ x) u, mul_comm]
    · simp [integral_undef h]
  rw [GEE.sandwichCovariance_eq_of_isSelfAdjoint hV, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

/-- **Projection laws of the Z-estimator limit: the sandwich covariance.** If every projection
`⟪Y, t⟫` is `N(0, E ⟪ψ₀, t⟫²)` (the limit law in
`VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation`), then every
projection of `-D⁻¹ Y` is `N(0, ⟪GEE.sandwichCovariance D V t, t⟫)` with `V = E ψ₀ ψ₀ᵀ` the
Bochner integral of the rank-one operators (`sandwichCovariance_integral_rankOne` writes this
sandwich as `D⁻¹ V (D⁻¹)*`). `D` need not be symmetric. No invertibility is assumed: for
singular `D`, `Ring.inverse D = 0` and both sides degenerate to `N(0, 0)`. -/
theorem hasLaw_inner_neg_inverse_apply_sandwich
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {𝓧 : Type*} [MeasurableSpace 𝓧]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {μX : Measure 𝓧} {ψ₀ : 𝓧 → E} (hψ_meas : Measurable ψ₀)
    (hψ_sq : Integrable (fun x => ‖ψ₀ x‖ ^ 2) μX) (D : E →L[ℝ] E)
    {Y : Ω' → E}
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ x, ⟪ψ₀ x, t⟫ ^ 2 ∂μX).toNNReal) P') (t : E) :
    HasLaw (fun ω => ⟪-Ring.inverse D (Y ω), t⟫)
      (gaussianReal 0 (⟪GEE.sandwichCovariance D
        (∫ x, InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x) ∂μX) t, t⟫).toNNReal) P' := by
  have hs : MemLp ψ₀ 2 μX :=
    (memLp_two_iff_integrable_sq_norm hψ_meas.aestronglyMeasurable).2 hψ_sq
  have hμ : MemLp id 2 (μX.map ψ₀) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hψ_meas.aemeasurable).2 hs
  have hB : ∀ s : E, ⟪covarianceOperator (μX.map ψ₀) s, s⟫ = ∫ x, ⟪ψ₀ x, s⟫ ^ 2 ∂μX :=
    fun s => by
      have hcont : Continuous fun z : E => ⟪s, z⟫ * ⟪s, z⟫ :=
        (continuous_const.inner continuous_id).mul (continuous_const.inner continuous_id)
      rw [covarianceOperator_inner hμ s s,
        integral_map hψ_meas.aemeasurable hcont.aestronglyMeasurable]
      congr 1
      funext x
      rw [real_inner_comm (ψ₀ x) s, sq]
  have efun : (fun ω => ⟪-Ring.inverse D (Y ω), t⟫) =
      fun ω => ⟪Y ω, -ContinuousLinearMap.adjoint (Ring.inverse D) t⟫ := by
    funext ω
    rw [inner_neg_left, ← ContinuousLinearMap.adjoint_inner_right, ← inner_neg_right]
  have evar : ⟪GEE.sandwichCovariance D
        (∫ x, InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x) ∂μX) t, t⟫ =
      ∫ x, ⟪ψ₀ x, -ContinuousLinearMap.adjoint (Ring.inverse D) t⟫ ^ 2 ∂μX := by
    rw [GEE.inner_sandwichCovariance_apply,
      ← covarianceOperator_map_eq_integral_rankOne hψ_meas hψ_sq, hB]
    congr 1
    funext x
    rw [inner_neg_right, neg_sq]
  rw [efun, evar]
  exact hY _

/-- **The sandwich collapses to the inverse information for a correctly specified score.** With
`ψ = score p`, data law `lawOf ν p θ₀`, the information identity `E Dscore θ₀ = -I(θ₀)` and
nonsingular `I(θ₀)`, the sandwich `GEE.sandwichCovariance D V` with `D = E Dscore θ₀` and
`V = E score scoreᵀ` equals `I(θ₀)⁻¹`: here `V` is `fisherInformation ν p θ₀` by definition,
`D = -I(θ₀)`, and `I(θ₀)⁻¹` is self-adjoint. -/
theorem sandwich_score_eq_inverse_fisherInformation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E}
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI : IsUnit (fisherInformation ν p θ₀)) :
    GEE.sandwichCovariance (∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀))
        (∫ x, InnerProductSpace.rankOne ℝ (score p θ₀ x) (score p θ₀ x) ∂(lawOf ν p θ₀)) =
      Ring.inverse (fisherInformation ν p θ₀) := by
  rw [sandwichCovariance_integral_rankOne, h_info]
  have hV : (∫ x, InnerProductSpace.rankOne ℝ (score p θ₀ x) (score p θ₀ x)
      ∂(lawOf ν p θ₀)) = fisherInformation ν p θ₀ := rfl
  rw [hV]
  set I : E →L[ℝ] E := fisherInformation ν p θ₀ with hI_def
  have hinv : Ring.inverse (-I) = -Ring.inverse I := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h := inverse_apply_apply hI.neg (Ring.inverse I v)
    rw [neg_apply, apply_inverse_apply hI, map_neg] at h
    rw [neg_apply, ← neg_neg (Ring.inverse (-I) v), h]
  have hadj : ContinuousLinearMap.adjoint (Ring.inverse I) = Ring.inverse I := by
    refine ContinuousLinearMap.ext fun v => ?_
    refine ext_inner_right ℝ fun w => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (inner_inverse_comm (inner_fisherInformation_comm ν p θ₀) hI v w).symm
  have hadj' : ContinuousLinearMap.adjoint (Ring.inverse (-I)) = -Ring.inverse I := by
    rw [hinv, map_neg, hadj]
  rw [hadj', hinv]
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg,
    apply_inverse_apply hI, neg_neg]

/-! ### Asymptotically linear estimators (S16.3) -/

/-- An **influence function**: measurable, square integrable and integrable, with mean
zero. Integrability is a separate condition because square integrability does not imply it
on an infinite measure, where the Bochner integral of a non-integrable function is the junk
value `0`. -/
def IsInfluenceFunction
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : 𝓧 → E) (μX : Measure 𝓧) : Prop :=
  Measurable φ ∧ MemLp φ 2 μX ∧ Integrable φ μX ∧ ∫ x, φ x ∂μX = 0

/-- **Normal limit of an asymptotically linear estimator (scalar).** If
`√n (θ̂ₙ - θ) = n^{-1/2} ∑ φ(Xᵢ) + oₚ(1)` with `φ` an influence function (integrable,
square integrable, mean zero), then `√n (θ̂ₙ - θ) ⇒ N(0, E φ²)`: the CLT
(`tendstoInDistribution_inv_sqrt_mul_sum_sub`) gives the limit for the linear part and
Slutsky (`tendstoInDistribution_of_tendstoInMeasure_sub`) removes the remainder. The
`oₚ(1)` remainder is an explicit hypothesis; a cross-fitted nuisance product-rate
`oₚ(n^{-1/2})` bound discharging it is a separate obligation, not proved here. -/
theorem tendstoInDistribution_of_asymptoticallyLinear
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P']
    {μX : Measure 𝓧} {X : ℕ → Ω → 𝓧}
    (hX_law : ∀ i, HasLaw (X i) μX P)
    (hX_indep : iIndepFun X P)
    {φ : 𝓧 → ℝ} (hφ : IsInfluenceFunction φ μX)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    {θ : ℝ}
    (hrem : TendstoInMeasure P
      (fun (n : ℕ) ω => √n * (θhat n ω - θ) -
        (√n)⁻¹ * ∑ i ∈ Finset.range n, φ (X i ω)) atTop 0)
    {Y : Ω' → ℝ}
    (hY : HasLaw Y
      (gaussianReal 0 (∫ x, φ x ^ 2 ∂μX).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √n * (θhat n ω - θ))
      atTop Y (fun _ => P) P' := by
  have hφ_meas : Measurable φ := hφ.1
  have hMemLp : MemLp φ 2 μX := hφ.2.1
  have hmean0 : ∫ x, φ x ∂μX = 0 := hφ.2.2.2
  set Z : ℕ → Ω → ℝ := fun i ω => φ (X i ω) with hZ_def
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i =>
    (⟨(hX_law i).aemeasurable, (hX_law 0).aemeasurable,
      (hX_law i).map_eq.trans (hX_law 0).map_eq.symm⟩ :
      IdentDistrib (X i) (X 0) P P).comp hφ_meas
  have hL2 : MemLp (Z 0) 2 P := (hX_law 0).memLp_comp hMemLp
  have hmean : P[Z 0] = 0 := by
    rw [← hmean0]
    exact (hX_law 0).integral_comp hφ_meas.aestronglyMeasurable
  have hsq : P[fun ω => Z 0 ω ^ 2] = ∫ x, φ x ^ 2 ∂μX :=
    (hX_law 0).integral_comp
      (f := fun x => φ x ^ 2) (hφ_meas.pow_const 2).aestronglyMeasurable
  have hvar : Var[Z 0; P] = ∫ x, φ x ^ 2 ∂μX := by
    rw [variance_of_integral_eq_zero hL2.aemeasurable hmean]
    exact hsq
  have hY' : HasLaw Y (gaussianReal 0 Var[Z 0; P].toNNReal) P' := by
    rw [← hvar] at hY
    exact hY
  have hCLT := tendstoInDistribution_inv_sqrt_mul_sum_sub (P := P) (X := Z)
    (Y := Y) hY' hL2
    (hX_indep.comp (fun _ => φ) (fun _ => hφ_meas)) hident
  have hmean' : ∫ ω, φ (X 0 ω) ∂P = 0 := by
    rw [← hmean0]
    exact (hX_law 0).integral_comp hφ_meas.aestronglyMeasurable
  have hCLT' : TendstoInDistribution
      (fun (n : ℕ) ω => (√n)⁻¹ * ∑ i ∈ Finset.range n, φ (X i ω))
      atTop Y (fun _ => P) P' := by
    simpa [hmean', hZ_def] using hCLT
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Y hCLT' hrem
    (fun n => ((hθ_meas n).sub_const _).const_mul _)

/-- **Normal limit of an asymptotically linear estimator (vector).** If
`√n (θ̂ₙ - θ) = n^{-1/2} ∑ φ(Xᵢ) + oₚ(1)` with `φ` an influence function (integrable,
square integrable, mean zero), then `√n (θ̂ₙ - θ) ⇒ Y` with `⟪Y, t⟫ ~ N(0, E ⟪φ, t⟫²)`: the
multivariate CLT (`tendstoInDistribution_inv_sqrt_smul_sum_comp`) plus Slutsky. As in
the scalar case, the `oₚ(1)` remainder (in particular any cross-fitted nuisance
product-rate bound) is an explicit hypothesis, not proved here. -/
theorem tendstoInDistribution_of_asymptoticallyLinear_vector
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P']
    {μX : Measure 𝓧} {X : ℕ → Ω → 𝓧}
    (hX_law : ∀ i, HasLaw (X i) μX P)
    (hX_indep : iIndepFun X P)
    {φ : 𝓧 → E} (hφ : IsInfluenceFunction φ μX)
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    {θ : E}
    (hrem : TendstoInMeasure P
      (fun (n : ℕ) ω => √n • (θhat n ω - θ) -
        (√n)⁻¹ • ∑ i ∈ Finset.range n, φ (X i ω)) atTop 0)
    {Y : Ω' → E} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ x, ⟪φ x, t⟫ ^ 2 ∂μX).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √n • (θhat n ω - θ))
      atTop Y (fun _ => P) P' := by
  have hφ_meas : Measurable φ := hφ.1
  have hMemLp : MemLp φ 2 μX := hφ.2.1
  have hφ_sq : Integrable (fun x => ‖φ x‖ ^ 2) μX :=
    hMemLp.integrable_norm_pow two_ne_zero
  have hCLT := tendstoInDistribution_inv_sqrt_smul_sum_comp
    hX_law hX_indep hφ_meas hφ_sq hφ.2.2.2 hY_meas hY
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Y hCLT hrem
    (fun n => ((hθ_meas n).sub_const _).const_smul _)

end MathlibExt.Probability.Statistics.EstimatingEquations
