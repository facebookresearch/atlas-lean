/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.EstimatingEquations
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Distributions.Gaussian.Real
import MathlibExt.Probability.Statistics.VectorInference

/-!
# Tests for general estimating equations: cluster sandwich and asymptotic linearity

* Boundary (S16.1, nonsingular): on the IID product of `N(0, 1)` with the cluster
  estimating equation `ψ θ c = θ + c` (limiting Jacobian `A = id`, nonsingular), the
  cluster sandwich theorem gives `√n (-X̄ₙ) ⇒ N(0, 1)` with sandwich variance `t * t`.
* Boundary (S16.1, singular): the zero operator is not a unit, so the nonsingularity
  hypothesis — and hence the sandwich conclusion — is unavailable there.
* Boundary (S16.3, positive): with the explicit influence function `φ = id` on
  `N(0, 1)` and the sample mean (zero remainder), the scalar asymptotic-linearity
  theorem gives `√n X̄ₙ ⇒ N(0, 1)`.
* Boundary (S16.3, negative): the constant function `1` on `ℕ` with counting measure
  is not square integrable, so it is not an influence function and no normal limit is
  claimed.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.EstimatingEquations

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace NNReal
open MathlibExt.Probability.Statistics.EstimatingEquations
open MathlibExt.Probability.Statistics.VectorInference

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

/-! ### Asymptotically linear estimator with `φ = id` (S16.3) -/

/-- The identity is an influence function on `N(0, 1)`. -/
theorem influenceFunction_id :
    IsInfluenceFunction (fun x : ℝ => x) (gaussianReal 0 1) := by
  refine ⟨measurable_id, memLp_id_gaussianReal' 2 (by simp), ?_⟩
  exact integral_id_gaussianReal

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
  rintro ⟨-, hLp, -⟩
  have hInt : Integrable (fun _ : ℕ => (1 : ℝ)) Measure.count := by
    have h := (memLp_two_iff_integrable_sq_norm
      aestronglyMeasurable_const).1 hLp
    simpa using h
  rw [integrable_const_iff] at hInt
  rcases hInt with h | h
  · exact one_ne_zero h
  · exact absurd h not_isFiniteMeasure_count

end MathlibExtTest.Probability.Statistics.EstimatingEquations
