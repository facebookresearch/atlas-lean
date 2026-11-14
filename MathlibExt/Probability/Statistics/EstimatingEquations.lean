/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.VectorInference
public import MathlibExt.Probability.Statistics.MultivariateCLT
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# General estimating equations: cluster sandwich and asymptotic linearity

This file covers two gap targets that are deliberately **general** (IID units with a
finite-dimensional estimating equation), not GEE-specific.

## S16.1: cluster estimating equations with sandwich covariance

For IID independent **clusters** (the cluster is the IID unit; no independence is assumed
*within* a cluster since the estimating function consumes the whole cluster at once), a
consistent root of a finite-dimensional estimating equation with nonsingular limiting
Jacobian `A = E Dψ θ₀` and a finite-variance cluster score has asymptotic covariance
`A⁻¹ B A⁻ᵀ`, where `B = E ψ θ₀ ψ θ₀ᵀ` is the cluster second moment
(`clusterSecondMoment`). The cluster asymptotic regime is `n → ∞` clusters; cluster sizes
may grow or be heterogeneous as long as each cluster contributes one IID summand.

The proof reuses the vector Z-estimator theorem
`VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation` (applied with
the cluster as the IID unit), whose own proof runs through the multivariate CLT
(`tendstoInDistribution_inv_sqrt_smul_sum_sub`), a vector Taylor step with a Lipschitz
uniform remainder (`norm_sub_sub_fderiv_le`, `norm_avg_add_avg_apply_le`), and Slutsky's
theorem (`tendstoInDistribution_of_tendstoInMeasure_sub`). The sandwich form `A⁻¹ B A⁻ᵀ`
(`clusterSandwich`, stated for `K = A⁻¹` as `K B Kᵀ`) is then read off the limit law by
`hasLaw_inner_clusterSandwich`. The statistics session owns the GEE sandwich slot in
`VectorInference`; nothing here duplicates that setup.

## S16.3: asymptotically linear estimators

For an asymptotically linear estimator with square-integrable mean-zero influence
function, `√n (θ̂ₙ - θ) = n^{-1/2} ∑ φ(Xᵢ) + oₚ(1)` with `E φ = 0`, `φ ∈ L²`, the normal
limit follows from the shared scalar/vector CLT plus Slutsky: the scalar case
(`tendstoInDistribution_of_asymptoticallyLinear`) via Mathlib's
`tendstoInDistribution_inv_sqrt_mul_sum_sub`, the vector case
(`tendstoInDistribution_of_asymptoticallyLinear_vector`) via
`tendstoInDistribution_inv_sqrt_smul_sum_comp`. The `oₚ(1)` remainder is an explicit
hypothesis (`hrem`); in particular the cross-fitted nuisance product-rate `oₚ(n^{-1/2})`
remainder bound is a separate obligation and is assumed here, not proved.

## Main statements

* `clusterSecondMoment`, `inner_clusterSecondMoment_apply`: the cluster second moment
  operator `B` and its quadratic form `⟪B u, v⟫ = E ⟪ψ, u⟫ ⟪ψ, v⟫`.
* `clusterSandwich`, `inner_clusterSandwich_self`: the sandwich operator `K B Kᵀ` and
  `⟪K B Kᵀ t, t⟫ = ⟪B (Kᵀ t), Kᵀ t⟫`.
* `hasLaw_inner_clusterSandwich`: the projection law of `-K Y` when `Y` has covariance
  `B`, i.e. `N(0, ⟪K B Kᵀ t, t⟫)`.
* `tendstoInDistribution_sqrt_smul_sub_of_clusterEstimatingEquation`: the cluster
  sandwich theorem, `√n (θ̂ₙ - θ₀) ⇒ Z` with `⟪Z, t⟫ ~ N(0, ⟪A⁻¹ B A⁻ᵀ t, t⟫)`.
* `IsInfluenceFunction`: `φ ∈ L²` with mean zero.
* `tendstoInDistribution_of_asymptoticallyLinear` (scalar),
  `tendstoInDistribution_of_asymptoticallyLinear_vector` (vector): normal limits for
  asymptotically linear estimators.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.EstimatingEquations

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.VectorInference

/-! ### The cluster second moment operator -/

/-- The **cluster second-moment operator** `B = E[ψ₀ ψ₀ᵀ]` of a cluster score
`ψ₀ : 𝓒 → E`: the Bochner integral of the rank-one operators
`InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x)`. If the score is not square integrable the
integral takes its junk value `0`. -/
noncomputable def clusterSecondMoment
    {𝓒 : Type*} [MeasurableSpace 𝓒]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ψ₀ : 𝓒 → E) (μC : Measure 𝓒) : E →L[ℝ] E :=
  ∫ x, InnerProductSpace.rankOne ℝ (ψ₀ x) (ψ₀ x) ∂μC

/-- Rank-one self-maps are continuous (mirrors the Fisher-information setup, for a general
cluster score rather than a log-density gradient). -/
private theorem continuous_rankOne_self_cluster
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Continuous fun s : E => InnerProductSpace.rankOne ℝ s s := by
  have e : (fun s : E => InnerProductSpace.rankOne ℝ s s) =
      fun s => ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ s) s := by
    funext s; ext v; simp
  rw [e]
  exact (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp
    ((innerSL ℝ).continuous.prodMk continuous_id)

/-- A square-integrable cluster score has an integrable rank-one second moment. -/
private theorem integrable_rankOne_cluster
    {𝓒 : Type*} [MeasurableSpace 𝓒]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure 𝓒} {s : 𝓒 → E} (hs : MemLp s 2 μ) :
    Integrable
      (fun x => InnerProductSpace.rankOne ℝ (s x) (s x)) μ := by
  refine Integrable.mono' (hs.integrable_norm_pow two_ne_zero)
    (continuous_rankOne_self_cluster.comp_aestronglyMeasurable
      hs.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [InnerProductSpace.norm_rankOne, sq]

/-- The bilinear form of a rank-one second moment is the expected product of projections. -/
private theorem inner_integral_rankOne_cluster
    {𝓒 : Type*} [MeasurableSpace 𝓒]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {μ : Measure 𝓒} {s : 𝓒 → E}
    (h : Integrable
      (fun x => InnerProductSpace.rankOne ℝ (s x) (s x)) μ)
    (u v : E) :
    ⟪(∫ x, InnerProductSpace.rankOne ℝ (s x) (s x) ∂μ) u, v⟫ =
      ∫ x, ⟪s x, u⟫ * ⟪s x, v⟫ ∂μ := by
  rw [ContinuousLinearMap.integral_apply h, real_inner_comm,
    ← integral_inner (h.apply_continuousLinearMap u)]
  congr 1; funext x
  rw [InnerProductSpace.rankOne_apply, real_inner_smul_right,
    real_inner_comm (s x) v]

/-- The quadratic form of the cluster second moment: for a square-integrable cluster
score, `⟪B u, v⟫ = E[⟪ψ₀, u⟫ ⟪ψ₀, v⟫]`. -/
theorem inner_clusterSecondMoment_apply
    {𝓒 : Type*} [MeasurableSpace 𝓒]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {ψ₀ : 𝓒 → E} {μC : Measure 𝓒}
    (hs : MemLp ψ₀ 2 μC) (u v : E) :
    ⟪clusterSecondMoment ψ₀ μC u, v⟫ =
      ∫ x, ⟪ψ₀ x, u⟫ * ⟪ψ₀ x, v⟫ ∂μC :=
  inner_integral_rankOne_cluster (integrable_rankOne_cluster hs) u v

/-! ### The sandwich operator -/

/-- The **sandwich covariance operator** `K B Kᵀ`: with `K = A⁻¹` (the inverse limiting
Jacobian) and `B` the cluster second moment, this is `A⁻¹ B A⁻ᵀ`. -/
noncomputable def clusterSandwich
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K B : E →L[ℝ] E) : E →L[ℝ] E :=
  K ∘L B ∘L ContinuousLinearMap.adjoint K

/-- The quadratic form of the sandwich: `⟪K B Kᵀ t, t⟫ = ⟪B (Kᵀ t), Kᵀ t⟫`. -/
theorem inner_clusterSandwich_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K B : E →L[ℝ] E) (t : E) :
    ⟪clusterSandwich K B t, t⟫ =
      ⟪B (ContinuousLinearMap.adjoint K t),
        ContinuousLinearMap.adjoint K t⟫ := by
  simp only [clusterSandwich, ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_right K _ _).symm

/-- **Projection law of the sandwich limit.** If every projection `⟪Y, s⟫` is
`N(0, ⟪B s, s⟫)`, then `⟪-K Y, t⟫` is `N(0, ⟪K B Kᵀ t, t⟫)`. -/
theorem hasLaw_inner_clusterSandwich
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Y : Ω → E} {B K : E →L[ℝ] E}
    (hY : ∀ s : E, HasLaw (fun ω => ⟪Y ω, s⟫)
      (gaussianReal 0 (⟪B s, s⟫).toNNReal) P)
    (t : E) :
    HasLaw (fun ω => ⟪-(K (Y ω)), t⟫)
      (gaussianReal 0 (⟪clusterSandwich K B t, t⟫).toNNReal) P := by
  have e : (fun ω => ⟪-(K (Y ω)), t⟫) =
      -((fun ω => ⟪Y ω, ContinuousLinearMap.adjoint K t⟫)) := by
    funext ω
    simp only [Pi.neg_apply]
    rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_right]
  rw [e, inner_clusterSandwich_self]
  have h := gaussianReal_neg (hY (ContinuousLinearMap.adjoint K t))
  simpa using h

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
`⟪Z, t⟫ ~ N(0, ⟪A⁻¹ B A⁻ᵀ t, t⟫)` with `B` the cluster second moment. -/
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
        (⟪clusterSandwich
          (Ring.inverse (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC))
          (clusterSecondMoment (ψ θ₀) μC) t, t⟫).toNNReal) P') :
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
  have hBt : ∀ s : E, ⟪clusterSecondMoment (ψ θ₀) μC s, s⟫ =
      ∫ x, ⟪ψ θ₀ x, s⟫ ^ 2 ∂μC := fun s => by
    rw [inner_clusterSecondMoment_apply hMemLp s s]
    congr 1
    funext x
    rw [sq]
  have hGZ : ∀ t : E, HasLaw
      (fun ω => ⟪(-Ring.inverse
        (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC) (G ω)), t⟫)
      (gaussianReal 0
        (⟪clusterSandwich
          (Ring.inverse (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μC))
          (clusterSecondMoment (ψ θ₀) μC) t, t⟫).toNNReal)
      (stdGaussian E) := fun t =>
    hasLaw_inner_clusterSandwich (fun s => by rw [hBt s]; exact hG' s) t
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

/-! ### Asymptotically linear estimators (S16.3) -/

/-- An **influence function**: measurable, square integrable, with mean zero. -/
def IsInfluenceFunction
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : 𝓧 → E) (μX : Measure 𝓧) : Prop :=
  Measurable φ ∧ MemLp φ 2 μX ∧ ∫ x, φ x ∂μX = 0

/-- **Normal limit of an asymptotically linear estimator (scalar).** If
`√n (θ̂ₙ - θ) = n^{-1/2} ∑ φ(Xᵢ) + oₚ(1)` with `φ` a square-integrable mean-zero
influence function, then `√n (θ̂ₙ - θ) ⇒ N(0, E φ²)`: the CLT
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
  have hmean0 : ∫ x, φ x ∂μX = 0 := hφ.2.2
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
`√n (θ̂ₙ - θ) = n^{-1/2} ∑ φ(Xᵢ) + oₚ(1)` with `φ` a square-integrable mean-zero
influence function, then `√n (θ̂ₙ - θ) ⇒ Y` with `⟪Y, t⟫ ~ N(0, E ⟪φ, t⟫²)`: the
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
    hX_law hX_indep hφ_meas hφ_sq hφ.2.2 hY_meas hY
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Y hCLT hrem
    (fun n => ((hθ_meas n).sub_const _).const_smul _)

end MathlibExt.Probability.Statistics.EstimatingEquations
