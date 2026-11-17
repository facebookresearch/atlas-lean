/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.EstimatingEquations
public import MathlibExtTest.Probability.Statistics.VectorInference
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Distributions.Gaussian.Real
import MathlibExt.Probability.Statistics.VectorInference
import Mathlib.Analysis.PSeries

/-!
# Tests for general estimating equations: cluster sandwich and asymptotic linearity

* Boundary (S16.1, nonsingular): on the IID product of `N(0, 1)` with the cluster
  estimating equation `ψ θ c = θ + c` (limiting Jacobian `A = id`, nonsingular), the
  cluster sandwich theorem gives `√n (-X̄ₙ) ⇒ N(0, 1)` with sandwich variance `t * t`.
* Boundary (S16.1, singular): the zero operator is not a unit, so the nonsingularity
  hypothesis — and hence the sandwich conclusion — is unavailable there.
* Positive (correctly specified recovery): under the hypotheses of the vector likelihood
  theorem, the cluster sandwich theorem, `covarianceOperator_map_eq_integral_rankOne` and
  `sandwich_score_eq_inverse_fisherInformation` give `√n (θhat n - θ₀) ⇒ N(0, I(θ₀)⁻¹)`.
* Non-vacuity (sandwich projection laws and collapse): on the Gaussian location family
  `N(θ, Id)` at `0` (`D = -Id`), `hasLaw_inner_neg_inverse_apply_sandwich` and
  `sandwich_score_eq_inverse_fisherInformation` give `⟪-D⁻¹ Z, u⟫ ~ N(0, ⟪I(0)⁻¹ u, u⟫)`.
* Boundary (singular `D`): at `D = 0` the projection law degenerates to `N(0, 0)`.
* Non-vacuity (misspecified working model): data `N(θ₀, 4)`, working model `N(θ, 1)`:
  `D = -1`, `V = 4 • 1`, and `sandwichCovariance_integral_rankOne` gives the sandwich `4 • 1`,
  not the model-based inverse information `1`.
* Boundary (S16.3, positive): with the explicit influence function `φ = id` on
  `N(0, 1)` and the sample mean (zero remainder), the scalar asymptotic-linearity
  theorem gives `√n X̄ₙ ⇒ N(0, 1)`.
* Boundary (S16.3, negative): the constant function `1` on `ℕ` with counting measure
  is not square integrable, so it is not an influence function and no normal limit is
  claimed.
* Boundary (S16.3, integrability): `φ n = 1 / (n + 1)` on `ℕ` with counting measure is
  square integrable and its Bochner integral is the junk value `0`, but it is not
  integrable, so it is not an influence function.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.EstimatingEquations

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace NNReal
open MathlibExt.Probability.Statistics.EstimatingEquations
open MathlibExt.Probability.Statistics.VectorInference
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)

/-- The IID sample space: coordinates of the infinite product of `N(0, 1)`. -/
noncomputable def sampleR : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ => gaussianReal 0 1

instance : IsProbabilityMeasure sampleR := by
  unfold sampleR
  infer_instance

/-- Each coordinate of the sample has law `N(0, 1)`. -/
theorem hasLaw_coordR (i : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω i) (gaussianReal 0 1) sampleR :=
  ⟨(measurable_pi_apply i).aemeasurable,
    Measure.infinitePi_map_eval _ i⟩

/-- The coordinates of the sample are independent. -/
theorem iIndepFun_coordR :
    iIndepFun (fun i (ω : ℕ → ℝ) => ω i) sampleR :=
  iIndepFun_infinitePi (P := fun _ => gaussianReal 0 1)
    (X := fun _ => id) (fun _ => measurable_id)

/-- The sample mean. -/
noncomputable def clusterMean (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ω i

/-- The sample mean is measurable. -/
theorem measurable_clusterMean (n : ℕ) :
    Measurable (clusterMean n) :=
  (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_mul _

/-- The sample mean is consistent (strong law). -/
theorem tendstoInMeasure_clusterMean :
    TendstoInMeasure sampleR clusterMean atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_clusterMean n).aestronglyMeasurable) ?_
  have hInt : Integrable (fun ω : ℕ → ℝ => ω 0) sampleR :=
    (hasLaw_coordR 0).integrable
      ((memLp_id_gaussianReal' 2 (by simp)).integrable one_le_two)
  have h := strong_law_ae (fun i (ω : ℕ → ℝ) => ω i) hInt
    (fun i j hij => iIndepFun_coordR.indepFun hij)
    (fun i => ⟨(measurable_pi_apply i).aemeasurable,
      (measurable_pi_apply 0).aemeasurable,
      ((hasLaw_coordR i).map_eq.trans
        (hasLaw_coordR 0).map_eq.symm)⟩)
  have h0 : ∫ ω, ω 0 ∂sampleR = 0 := by
    have hcomp := (hasLaw_coordR 0).integral_comp (f := id)
      aestronglyMeasurable_id
    simp only [Function.comp_def, id] at hcomp
    rw [hcomp, integral_id_gaussianReal]
  rw [h0] at h
  exact h

/-- Negation preserves convergence in probability to a constant. -/
theorem tendstoInMeasure_neg_clusterMean :
    TendstoInMeasure sampleR (fun n ω => -clusterMean n ω)
      atTop (fun _ => 0) := by
  have h := TendstoInMeasure.comp_const_of_continuousAt
    (continuous_neg.continuousAt) tendstoInMeasure_clusterMean
  simpa using h

/-! ### Cluster estimating equation `ψ θ c = θ + c` (nonsingular `A`) -/

/-- The cluster estimating function `ψ θ c = θ + c`: exact root `-X̄ₙ`, derivative
`id`, hence nonsingular limiting Jacobian. -/
noncomputable def clusterEE (θ c : ℝ) : ℝ := θ + c

/-- The derivative of the cluster estimating function is `id`. -/
theorem fderiv_clusterEE (x θ : ℝ) :
    fderiv ℝ (fun t : ℝ => clusterEE t x) θ =
      ContinuousLinearMap.id ℝ ℝ := by
  have h : (fun t : ℝ => clusterEE t x) = fun t => t + x := rfl
  rw [h]
  exact ((hasFDerivAt_id θ).add_const x).fderiv

/-- The limiting Jacobian is `id`. -/
theorem integral_fderiv_clusterEE :
    (∫ _ : ℝ, ContinuousLinearMap.id ℝ ℝ ∂(gaussianReal 0 1)) =
      ContinuousLinearMap.id ℝ ℝ := by
  simp

/-- The inverse Jacobian is `id`. -/
theorem inverse_id_clm :
    Ring.inverse (ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by
  rw [← ContinuousLinearMap.one_def, Ring.inverse_one]

/-- The adjoint of `id` is `id`. -/
theorem adjoint_id_clm :
    ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ :=
  ContinuousLinearMap.adjoint_id

/-- The second moment of `N(0, 1)` is `1`. -/
theorem integral_sq_gaussianReal_one :
    ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
  rw [variance_of_integral_eq_zero aemeasurable_id
    integral_id_gaussianReal] at h
  simpa using h

/-- The second-moment operator of the cluster score at `θ₀ = 0`:
`⟪B s, s⟫ = s * s`. -/
theorem inner_covarianceOperator_clusterEE (s : ℝ) :
    ⟪covarianceOperator ((gaussianReal 0 1).map (clusterEE 0)) s, s⟫ =
      s * s := by
  have h : (clusterEE 0 : ℝ → ℝ) = id := by
    funext x
    show (0 : ℝ) + x = x
    exact zero_add x
  rw [h, Measure.map_id,
    covarianceOperator_inner (memLp_id_gaussianReal' 2 (by simp)) s s]
  have e : (fun x : ℝ => ⟪s, x⟫ * ⟪s, x⟫) = fun x => (s * s) * x ^ 2 := by
    funext x
    rw [RCLike.inner_apply, conj_trivial]
    ring
  rw [e, integral_const_mul, integral_sq_gaussianReal_one, mul_one]

/-- The sandwich quadratic form at `θ₀ = 0`: `⟪A⁻¹ B A⁻ᵀ t, t⟫ = t * t`. -/
theorem inner_sandwichCovariance_clusterEE (t : ℝ) :
    ⟪GEE.sandwichCovariance
      (∫ x : ℝ, fderiv ℝ (fun t : ℝ => clusterEE t x) 0 ∂(gaussianReal 0 1))
      (covarianceOperator ((gaussianReal 0 1).map (clusterEE 0))) t, t⟫ =
      t * t := by
  have hK : Ring.inverse
      (∫ x : ℝ, fderiv ℝ (fun t : ℝ => clusterEE t x) 0
        ∂(gaussianReal 0 1)) =
      ContinuousLinearMap.id ℝ ℝ := by
    have e : (fun x : ℝ => fderiv ℝ (fun t : ℝ => clusterEE t x) 0) =
        fun _ => ContinuousLinearMap.id ℝ ℝ :=
      funext fun x => fderiv_clusterEE x 0
    rw [e, integral_fderiv_clusterEE]
    exact inverse_id_clm
  rw [GEE.inner_sandwichCovariance_apply, hK, adjoint_id_clm]
  simp only [ContinuousLinearMap.id_apply]
  exact inner_covarianceOperator_clusterEE t

/-- The negated sample mean solves the cluster equation for every `n`. -/
theorem sum_clusterEE_negMean (n : ℕ) (ω : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, clusterEE (-clusterMean n ω) (ω i) = 0 := by
  have e : (fun i : ℕ => clusterEE (-clusterMean n ω) (ω i)) =
      fun i => -clusterMean n ω + ω i := rfl
  rw [e]
  simp only [clusterMean, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [nsmul_eq_mul]
    field_simp
    ring

/-- The cluster-equation event fails with probability `0`. -/
theorem tendsto_root_negClusterMean :
    Tendsto (fun n => sampleR {ω | ∑ i ∈ Finset.range n,
      clusterEE (-clusterMean n ω) (ω i) ≠ 0}) atTop (𝓝 0) := by
  have h : ∀ n, {ω : ℕ → ℝ | ∑ i ∈ Finset.range n,
      clusterEE (-clusterMean n ω) (ω i) ≠ 0} = ∅ := fun n => by
    ext ω
    simp [sum_clusterEE_negMean n ω]
  simp [h]

/-- **Non-vacuity of the cluster sandwich theorem**: for `ψ θ c = θ + c` every
hypothesis holds, and `√n (-X̄ₙ) ⇒ N(0, 1)` with sandwich variance `t * t`. -/
theorem tendstoInDistribution_sqrt_mean_of_clusterEE :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → ℝ) => √(n : ℝ) • (-clusterMean n ω - 0))
      atTop id (fun _ => sampleR) (gaussianReal 0 1) := by
  have hdiff : ∀ x : ℝ, ∀ θ ∈ Metric.ball (0 : ℝ) 1,
      DifferentiableAt ℝ (fun t : ℝ => clusterEE t x) θ :=
    fun x θ _ => ((hasFDerivAt_id θ).add_const x).differentiableAt
  have hM : ∀ x : ℝ, ∀ θ ∈ Metric.ball (0 : ℝ) 1,
      ‖fderiv ℝ (fun t : ℝ => clusterEE t x) θ -
        fderiv ℝ (fun t : ℝ => clusterEE t x) 0‖ ≤
        0 * ‖θ - 0‖ := fun x θ _ => by
    rw [fderiv_clusterEE x θ, fderiv_clusterEE x 0, sub_self,
      norm_zero]
    exact mul_nonneg (le_refl 0) (norm_nonneg _)
  have hmeas : Measurable (clusterEE 0) := by
    have e : (clusterEE 0 : ℝ → ℝ) = fun c => 0 + c := rfl
    rw [e]
    simp only [zero_add]
    exact measurable_id
  have hsq : Integrable (fun x : ℝ => ‖clusterEE 0 x‖ ^ 2)
      (gaussianReal 0 1) := by
    have e : (fun x : ℝ => ‖clusterEE 0 x‖ ^ 2) =
        fun x => ‖(id : ℝ → ℝ) x‖ ^ 2 := by
      funext x
      show ‖(0 : ℝ) + x‖ ^ 2 = ‖x‖ ^ 2
      rw [zero_add]
    rw [e]
    exact (memLp_id_gaussianReal 2).integrable_norm_pow two_ne_zero
  have hmean : ∫ x : ℝ, clusterEE 0 x ∂(gaussianReal 0 1) = 0 := by
    have e : (fun x : ℝ => clusterEE 0 x) = fun x => 0 + x := rfl
    rw [e]
    simp only [zero_add]
    exact integral_id_gaussianReal
  have hDeq : (fun x : ℝ => fderiv ℝ (fun t : ℝ => clusterEE t x) 0) =
      fun _ => ContinuousLinearMap.id ℝ ℝ :=
    funext fun x => fderiv_clusterEE x 0
  have hDmeas : StronglyMeasurable fun x : ℝ =>
      fderiv ℝ (fun t : ℝ => clusterEE t x) 0 := by
    rw [hDeq]
    exact stronglyMeasurable_const
  have hDint : Integrable (fun x : ℝ =>
      fderiv ℝ (fun t : ℝ => clusterEE t x) 0)
      (gaussianReal 0 1) := by
    rw [hDeq]
    exact integrable_const _
  have hA : IsUnit (∫ x : ℝ, fderiv ℝ (fun t : ℝ => clusterEE t x) 0
      ∂(gaussianReal 0 1)) := by
    rw [hDeq, integral_fderiv_clusterEE,
      ← ContinuousLinearMap.one_def]
    exact isUnit_one
  have htheta : ∀ n, AEMeasurable
      ((fun n ω => -clusterMean n ω) n) sampleR := fun n =>
    (measurable_clusterMean n).neg.aemeasurable
  have hZ : ∀ t : ℝ, HasLaw (fun z : ℝ => ⟪id z, t⟫)
      (gaussianReal 0
        (⟪GEE.sandwichCovariance
          (∫ x : ℝ, fderiv ℝ (fun t : ℝ => clusterEE t x) 0 ∂(gaussianReal 0 1))
          (covarianceOperator ((gaussianReal 0 1).map (clusterEE 0))) t,
          t⟫).toNNReal) (gaussianReal 0 1) := by
    intro t
    rw [inner_sandwichCovariance_clusterEE t]
    have e : (fun z : ℝ => ⟪id z, t⟫) = fun z => z * t := by
      funext z
      show ⟪z, t⟫ = z * t
      rw [RCLike.inner_apply, conj_trivial]
      exact mul_comm t z
    have e2 : (fun z : ℝ => z * t) = fun ω => t * id ω := by
      funext z
      show z * t = t * z
      exact mul_comm z t
    rw [e, e2]
    have h : HasLaw (fun ω : ℝ => t * id ω)
        (gaussianReal (t * 0)
          ((NNReal.mk (t ^ 2) (sq_nonneg t)) * 1))
        (gaussianReal 0 1) :=
      gaussianReal_const_mul HasLaw.id t
    have hnn : ((NNReal.mk (t ^ 2) (sq_nonneg t)) * 1) =
        (t * t).toNNReal := by
      refine Subtype.ext ?_
      simp only [mul_one, pow_two]
      exact (Real.coe_toNNReal _ (mul_self_nonneg t)).symm
    rwa [mul_zero, hnn] at h
  exact tendstoInDistribution_sqrt_smul_sub_of_clusterEstimatingEquation
    (μC := gaussianReal 0 1) (X := fun i (ω : ℕ → ℝ) => ω i)
    (ψ := clusterEE) (θ₀ := 0) (δ := 1) (M := fun _ => 0)
    hasLaw_coordR iIndepFun_coordR one_pos hdiff measurable_const
    (integrable_const _) hM hmeas hsq hmean hDmeas hDint hA htheta
    tendsto_root_negClusterMean tendstoInMeasure_neg_clusterMean
    aemeasurable_id hZ

/-! ### Rank-one meat, sandwich projection laws and the Fisher collapse -/

/-- **Correctly specified recovery.** Under the hypotheses of
`VectorInference.tendstoInDistribution_sqrt_smul_sub_of_likelihoodEquation`, the cluster
sandwich theorem, the meat bridge `covarianceOperator_map_eq_integral_rankOne` and the collapse
`sandwich_score_eq_inverse_fisherInformation` give `√n (θhat n - θ₀) ⇒ N(0, I(θ₀)⁻¹)`. -/
theorem tendstoInDistribution_sqrt_smul_sub_of_score_sandwich
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {𝓧 : Type*} [MeasurableSpace 𝓧]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI : IsUnit (fisherInformation ν p θ₀))
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Z : Ω' → E} (hZ_meas : AEMeasurable Z P')
    (hZ : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0 (⟪Ring.inverse (fisherInformation ν p θ₀) t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (θhat n ω - θ₀)) atTop Z (fun _ => P) P' := by
  refine tendstoInDistribution_sqrt_smul_sub_of_clusterEstimatingEquation hX_law hX_indep hδ
    hs_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int
    (by rw [h_info]; exact hI.neg) hθ_meas hroot hcons hZ_meas (fun t => ?_)
  rw [covarianceOperator_map_eq_integral_rankOne hs_meas hs_sq,
    sandwich_score_eq_inverse_fisherInformation h_info hI]
  exact hZ t

open MathlibExtTest.Probability.Statistics.VectorInference in
/-- **Non-vacuity of `hasLaw_inner_neg_inverse_apply_sandwich` and
`sandwich_score_eq_inverse_fisherInformation`** on the Gaussian location family `N(θ, Id)` at `0`
(the density `pE` of the `VectorInference` tests): the score limit `Z = id ~ N(0, Id)` meets the
projection hypothesis, and with `D = E Dscore 0 = -Id` the two results give
`⟪-D⁻¹ Z, u⟫ ~ N(0, ⟪I(0)⁻¹ u, u⟫)`. -/
theorem hasLaw_inner_neg_inverse_apply_pE
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (u : E) :
    HasLaw (fun z : E => ⟪-Ring.inverse (∫ x, fderiv ℝ (fun t => score pE t x) 0
        ∂(lawOf (stdGaussian E) pE 0)) (id z), u⟫)
      (gaussianReal 0 (⟪Ring.inverse (fisherInformation (stdGaussian E) pE 0) u, u⟫).toNNReal)
      (stdGaussian E) := by
  have hD : (fun x : E => fderiv ℝ (fun t => score pE t x) 0) =
      fun _ => -ContinuousLinearMap.id ℝ E := funext fun x => fderiv_score_pE x 0
  have hlaw : IsProbabilityMeasure (lawOf (stdGaussian E) pE 0) := by
    rw [lawOf_pE]; infer_instance
  have h_info : ∫ x, fderiv ℝ (fun t => score pE t x) 0 ∂(lawOf (stdGaussian E) pE 0) =
      -fisherInformation (stdGaussian E) pE 0 := by
    rw [hD, fisherInformation_pE]; simp
  have hI : IsUnit (fisherInformation (stdGaussian E) pE 0) := by
    rw [fisherInformation_pE, ← ContinuousLinearMap.one_def]; exact isUnit_one
  rw [← sandwich_score_eq_inverse_fisherInformation h_info hI]
  refine hasLaw_inner_neg_inverse_apply_sandwich (by rw [score_pE_zero]; exact measurable_id)
    (memLp_score_pE.integrable_norm_pow two_ne_zero) _ (fun s => ?_) u
  have h := hasLaw_inner_id s
  rw [inverse_fisherInformation_pE, ← fisherInformation_pE,
    inner_fisherInformation_apply memLp_score_pE] at h
  simpa only [sq] using h

/-- **Boundary (singular `D`)**: with `D = 0`, `Ring.inverse 0 = 0`, so the projection law of
`hasLaw_inner_neg_inverse_apply_sandwich` degenerates to `N(0, 0)` whatever the meat. -/
theorem hasLaw_inner_neg_inverse_zero_apply_sandwich
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {𝓧 : Type*} [MeasurableSpace 𝓧]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {μX : Measure 𝓧} {ψ₀ : 𝓧 → E} (hψ_meas : Measurable ψ₀)
    (hψ_sq : Integrable (fun x => ‖ψ₀ x‖ ^ 2) μX) {Y : Ω' → E}
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ x, ⟪ψ₀ x, t⟫ ^ 2 ∂μX).toNNReal) P') (t : E) :
    HasLaw (fun ω => ⟪-Ring.inverse (0 : E →L[ℝ] E) (Y ω), t⟫) (gaussianReal 0 0) P' := by
  have h := hasLaw_inner_neg_inverse_apply_sandwich hψ_meas hψ_sq 0 hY t
  rwa [GEE.sandwichCovariance_zero_left, zero_apply, inner_zero_left,
    Real.toNNReal_zero] at h

/-- **Misspecified working model, bread**: data `N(θ₀, 4)`, working model `N(θ, 1)` with
score `ψ θ x = x - θ`; then `D = E Dψ θ₀ = -1` under any probability law. -/
theorem integral_fderiv_sub_misspecified (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ₀ : ℝ) :
    ∫ x, fderiv ℝ (fun t : ℝ => x - t) θ₀ ∂μ = -1 := by
  have hderiv : ∀ x, fderiv ℝ (fun t : ℝ => x - t) θ₀ = -1 := fun x => by
    have h1 : HasFDerivAt (fun t : ℝ => x - t) (-1 : ℝ →L[ℝ] ℝ) θ₀ := by
      have h := (hasFDerivAt_const (𝕜 := ℝ) x θ₀).sub (hasFDerivAt_id (𝕜 := ℝ) θ₀)
      have heq1 : ((fun _ => x) - id) = (fun t : ℝ => x - t) := rfl
      have heq2 : (0 : ℝ →L[ℝ] ℝ) - ContinuousLinearMap.id ℝ ℝ = -1 := by
        rw [show (1 : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.id ℝ ℝ from rfl, zero_sub]
      rwa [heq1, heq2] at h
    exact h1.fderiv
  simp_rw [hderiv]
  simp [integral_const]

/-- **Misspecified working model, meat**: `V = E (X - θ₀)² • 1 = 4 • 1` under the true law
`N(θ₀, 4)`. -/
theorem integral_rankOne_sub_misspecified (θ₀ : ℝ) :
    ∫ x, InnerProductSpace.rankOne ℝ (x - θ₀) (x - θ₀) ∂(gaussianReal θ₀ 4) =
      (4 : ℝ) • (1 : ℝ →L[ℝ] ℝ) := by
  have hrank : ∀ a : ℝ, InnerProductSpace.rankOne ℝ a a = (a * a) • (1 : ℝ →L[ℝ] ℝ) :=
    fun a => by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [InnerProductSpace.rankOne_apply, smul_apply, one_apply_eq_self, smul_eq_mul,
        RCLike.inner_apply, RCLike.conj_to_real]
      ring
  simp_rw [hrank]
  rw [integral_smul_const]
  congr 1
  have h := ProbabilityTheory.variance_fun_id_gaussianReal (μ := θ₀) (v := 4)
  rw [ProbabilityTheory.variance_eq_integral (X := fun x => x) aemeasurable_id] at h
  simp only [ProbabilityTheory.integral_id_gaussianReal] at h
  have h4 : ((4 : NNReal) : ℝ) = 4 := by simp
  simp_rw [← pow_two]
  rwa [h4] at h

/-- **Misspecified working model, sandwich**: the canonical sandwich of the misspecified score
is `4 • 1` (`sandwichCovariance_integral_rankOne` writes it as `D⁻¹ V (D⁻¹)*`), not the
model-based inverse information `-D⁻¹ = 1`: the sandwich correction is nonzero. -/
theorem sandwichCovariance_sub_misspecified (θ₀ : ℝ) :
    GEE.sandwichCovariance (∫ x, fderiv ℝ (fun t : ℝ => x - t) θ₀ ∂(gaussianReal θ₀ 4))
        (∫ x, InnerProductSpace.rankOne ℝ (x - θ₀) (x - θ₀) ∂(gaussianReal θ₀ 4)) =
      (4 : ℝ) • 1 ∧
      (4 : ℝ) • (1 : ℝ →L[ℝ] ℝ) ≠
        -Ring.inverse (∫ x, fderiv ℝ (fun t : ℝ => x - t) θ₀ ∂(gaussianReal θ₀ 4)) := by
  rw [sandwichCovariance_integral_rankOne, integral_fderiv_sub_misspecified,
    integral_rankOne_sub_misspecified]
  have hU : IsUnit (-1 : ℝ →L[ℝ] ℝ) := (isUnit_one (M := ℝ →L[ℝ] ℝ)).neg
  have h1 : Ring.inverse (-1 : ℝ →L[ℝ] ℝ) = -1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h := inverse_apply_apply hU v
    simp only [neg_apply, one_apply_eq_self, map_neg] at h
    rw [neg_apply, one_apply_eq_self]
    have h2 := congrArg Neg.neg h
    simpa using h2
  have hadj : ContinuousLinearMap.adjoint (-1 : ℝ →L[ℝ] ℝ) = -1 := by
    rw [map_neg, ContinuousLinearMap.adjoint_one]
  constructor
  · rw [h1, hadj]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, neg_apply, smul_apply, one_apply_eq_self,
      smul_eq_mul]
    ring
  · rw [h1, neg_neg]
    intro hcon
    have h2 := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1) hcon
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul, mul_one] at h2
    norm_num at h2

/-! ### Asymptotically linear estimator with `φ = id` (S16.3) -/

/-- The identity is an influence function on `N(0, 1)`. -/
theorem influenceFunction_id :
    IsInfluenceFunction (fun x : ℝ => x) (gaussianReal 0 1) := by
  refine ⟨measurable_id, memLp_id_gaussianReal' 2 (by simp), ?_, ?_⟩
  · exact (memLp_id_gaussianReal' 2 (by simp)).integrable one_le_two
  · exact integral_id_gaussianReal

/-- The sample mean has zero remainder: the linear expansion is exact. -/
theorem tendstoInMeasure_rem_clusterMean :
    TendstoInMeasure sampleR
      (fun (n : ℕ) (ω : ℕ → ℝ) => √(n : ℝ) * (clusterMean n ω - 0) -
        (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, id (ω i)) atTop 0 := by
  have hz : (fun (n : ℕ) (ω : ℕ → ℝ) => √(n : ℝ) * (clusterMean n ω - 0) -
      (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, id (ω i)) = fun _ _ => 0 := by
    funext n ω
    simp only [clusterMean, id, sub_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hr : (√(n : ℝ)) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have e2 : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n),
          mul_inv_cancel₀ hn']
      rw [← mul_assoc, e2, sub_self]
  rw [hz, tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [Pi.zero_apply, sub_zero, norm_zero, not_le_of_gt hε,
    Set.ofPred_false, measure_empty]
  exact tendsto_const_nhds

/-- **Non-vacuity of the scalar asymptotic-linearity theorem**: for `φ = id` on
`N(0, 1)` the sample mean satisfies the exact expansion, and `√n X̄ₙ ⇒ N(0, 1)`. -/
theorem tendstoInDistribution_sqrt_mean_of_asymptoticallyLinear :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → ℝ) => √(n : ℝ) * (clusterMean n ω - 0))
      atTop id (fun _ => sampleR) (gaussianReal 0 1) := by
  have hY : HasLaw (id : ℝ → ℝ)
      (gaussianReal 0 (∫ x : ℝ, id x ^ 2 ∂(gaussianReal 0 1)).toNNReal)
      (gaussianReal 0 1) := by
    have h1 : (∫ x : ℝ, id x ^ 2 ∂(gaussianReal 0 1)) = 1 := by
      simpa using integral_sq_gaussianReal_one
    rw [h1, Real.toNNReal_one]
    exact HasLaw.id
  exact tendstoInDistribution_of_asymptoticallyLinear
    (μX := gaussianReal 0 1) (X := fun i (ω : ℕ → ℝ) => ω i)
    (φ := id) (θhat := clusterMean) (θ := 0)
    hasLaw_coordR iIndepFun_coordR influenceFunction_id
    (fun n => (measurable_clusterMean n).aemeasurable)
    tendstoInMeasure_rem_clusterMean hY

/-! ### Boundary: singular Jacobian, non-integrable influence -/

/-- The zero operator is singular: the nonsingularity hypothesis of the sandwich
theorem cannot be discharged, so no sandwich conclusion is claimed there. -/
theorem not_isUnit_zero_clm :
    ¬ IsUnit (0 : ℝ →L[ℝ] ℝ) := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : ℝ)
  have h1 := apply_inverse_apply (E := ℝ) h x
  simp only [zero_apply] at h1
  exact hx h1.symm

/-- Counting measure on `ℕ` is not finite. -/
theorem not_isFiniteMeasure_count :
    ¬ IsFiniteMeasure (Measure.count : Measure ℕ) := by
  rw [not_isFiniteMeasure_iff]
  exact Measure.count_apply_infinite Set.infinite_univ

/-- The constant function `1` on `ℕ` is not square integrable, hence not an influence
function: no normal limit is claimed for it. -/
theorem not_isInfluenceFunction_const :
    ¬ IsInfluenceFunction (fun _ : ℕ => (1 : ℝ)) Measure.count := by
  rintro ⟨-, hLp, -, -⟩
  have hInt : Integrable (fun _ : ℕ => (1 : ℝ)) Measure.count := by
    have h := (memLp_two_iff_integrable_sq_norm
      aestronglyMeasurable_const).1 hLp
    simpa using h
  rw [integrable_const_iff] at hInt
  rcases hInt with h | h
  · exact one_ne_zero h
  · exact absurd h not_isFiniteMeasure_count

/-- The sequence `φ n = 1 / (n + 1)`: square summable but not summable. -/
noncomputable def harmonicTail (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- `φ n = 1 / (n + 1)` is square integrable for counting measure. -/
theorem memLp_two_harmonicTail : MemLp harmonicTail 2 Measure.count := by
  rw [memLp_two_iff_integrable_sq_norm
    (measurable_of_countable harmonicTail).aestronglyMeasurable, integrable_count_iff]
  have h : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine h.congr fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [harmonicTail, Nat.cast_add, Nat.cast_one, Real.norm_eq_abs, abs_pow,
    abs_div, abs_one, abs_of_pos hn, div_pow, one_pow]

/-- `φ n = 1 / (n + 1)` is not integrable for counting measure (harmonic series). -/
theorem not_integrable_harmonicTail : ¬ Integrable harmonicTail Measure.count := by
  rw [integrable_count_iff]
  intro h
  have h' : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    refine h.congr fun n => ?_
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [harmonicTail, Nat.cast_add, Nat.cast_one, Real.norm_eq_abs, abs_div,
      abs_one, abs_of_pos hn]
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 h')

/-- The Bochner integral of `φ n = 1 / (n + 1)` is the junk value `0`. -/
theorem integral_harmonicTail : ∫ n, harmonicTail n ∂Measure.count = 0 :=
  integral_undef not_integrable_harmonicTail

/-- Boundary (integrability): `φ n = 1 / (n + 1)` is measurable, square integrable and has
junk integral `0`, yet it is not an influence function, because it is not integrable. -/
theorem not_isInfluenceFunction_harmonicTail :
    ¬ IsInfluenceFunction harmonicTail Measure.count :=
  fun h => not_integrable_harmonicTail h.2.2.1

end MathlibExtTest.Probability.Statistics.EstimatingEquations
