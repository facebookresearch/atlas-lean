/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LikelihoodRatioLocalPower
public import MathlibExtTest.Probability.Statistics.LikelihoodRatioTests

/-!
# Tests for the local power of the likelihood-ratio test

* Non-vacuity: for the Gaussian location family `N(θ, 1)` at `θ₀ = 0` and the local
  alternatives `θₙ = h / √n`, the triangular array `X n i = Zᵢ + h / √n` built from one
  i.i.d. `N(0, 1)` sequence, with the row mean as the root of the likelihood equation, satisfies
  every hypothesis of `tendstoInDistribution_two_mul_logLikelihood_sub_local`; the theorem gives
  the noncentral limit `(Z + h)²`.
* The reweighting identity with the unit density: the first `n` coordinates of an infinite
  product measure have the finite product law.
* Boundary (junk value): row `0` has parameter `θ₀ + h / √0 = θ₀`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Statistics.FisherInformation
open MathlibExt.Probability.Statistics.MLEAsymptoticNormality
open MathlibExt.Probability.Statistics.LikelihoodRatioLocalPower
open MathlibExtTest.Probability.Statistics.MLEAsymptoticNormality
open MathlibExtTest.Probability.Statistics.LikelihoodRatioTests

namespace MathlibExtTest.Probability.Statistics.LikelihoodRatioLocalPower

/-- Boundary (junk value): with Lean's `h / 0 = 0`, row `0` of the local alternatives has the
null parameter. -/
example (θ₀ h : ℝ) : θ₀ + h / √((0 : ℕ) : ℝ) = θ₀ := by simp

/-- With the unit density, the reweighting identity says that the first `n` coordinates of the
infinite product `N(0, 1)^ℕ` have the law `N(0, 1)^n`. -/
example (n : ℕ) : ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).withDensity
    fun x => ∏ i ∈ Finset.range n, (fun _ : ℝ => (1 : ℝ≥0∞)) (x i)).map
      (fun x (i : Fin n) => x i) = Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
  have e : (gaussianReal 0 1).withDensity (fun _ => (1 : ℝ≥0∞)) = gaussianReal 0 1 :=
    withDensity_one
  have : IsProbabilityMeasure ((gaussianReal 0 1).withDensity fun _ => (1 : ℝ≥0∞)) := by
    rw [e]; infer_instance
  have h := map_withDensity_infinitePi_prod (μ := gaussianReal 0 1)
    (r := fun _ => (1 : ℝ≥0∞)) measurable_const n
  rwa [e] at h

/-- Row `n` of the local triangular array: `X n i = Zᵢ + h / √n`. -/
noncomputable def localSample (h : ℝ) (n i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i + h / √n

/-- The row mean of the local triangular array. -/
noncomputable def localMean (h : ℝ) (n : ℕ) (ω : ℕ → ℝ) : ℝ := sampleMean n ω + h / √n

/-- Row `n` is i.i.d. `N(h / √n, 1)`. -/
theorem hasLaw_localSample (h : ℝ) (n i : ℕ) :
    HasLaw (localSample h n i) (lawOf volume pG (0 + h / √n)) sampleG := by
  refine ⟨(by fun_prop : Measurable fun ω : ℕ → ℝ => ω i + h / √n).aemeasurable, ?_⟩
  have e : localSample h n i = (fun x => x + h / √n) ∘ fun ω : ℕ → ℝ => ω i := rfl
  rw [e, ← Measure.map_map (g := fun x : ℝ => x + h / √n) (f := fun ω : ℕ → ℝ => ω i)
    (by fun_prop) (measurable_pi_apply i), (hasLaw_coord i).map_eq,
    lawOf_pG, lawOf_pG, gaussianReal_map_add_const]

/-- The rows of the local triangular array are independent. -/
theorem iIndepFun_localSample (h : ℝ) (n : ℕ) : iIndepFun (localSample h n) sampleG :=
  iIndepFun_coord.comp (fun _ x => x + h / √n) (fun _ => by fun_prop)

/-- The row mean solves the likelihood equation on every sample. -/
theorem sum_score_localMean (h : ℝ) (n : ℕ) (ω : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, score pG (localMean h n ω) (localSample h n i ω) = 0 := by
  have := sum_score_sampleMean n ω
  simp only [score_pG] at this ⊢
  simpa only [localMean, localSample, add_sub_add_right_eq_sub] using this

/-- The row mean is consistent. -/
theorem tendstoInMeasure_localMean (h : ℝ) :
    TendstoInMeasure sampleG (localMean h) atTop (fun _ => 0) := by
  have hd : Tendsto (fun n : ℕ => h / √n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsm := tendstoInMeasure_sampleMean
  rw [tendstoInMeasure_iff_norm] at hsm ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hsm (ε / 2) (by positivity))
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hd.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε / 2))] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs, localMean] at hω ⊢
  rw [Real.dist_eq, sub_zero] at hn
  have := abs_add_le (sampleMean n ω) (h / √n)
  linarith

/-- **Non-vacuity of the local-power theorem**: for `N(θ, 1)` and `θₙ = h / √n`,
`2 (ℓₙ(X̄ₙ) - ℓₙ(0)) → (Z + h)²` in distribution, `Z ~ N(0, 1)`. -/
theorem tendstoInDistribution_logLikelihoodRatio_local_pG (h : ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
        (Real.log (pG (localMean h n ω) (localSample h n i ω)) -
          Real.log (pG 0 (localSample h n i ω))))
      atTop id (fun _ => sampleG) ((gaussianReal h 1).map fun x : ℝ => x ^ 2) := by
  have hd : Measurable fun x => deriv (fun t => score pG t x) 0 := by
    simp_rw [deriv_score_pG]; fun_prop
  have hdi : Integrable (fun x => deriv (fun t => score pG t x) 0) (lawOf volume pG 0) := by
    have : IsProbabilityMeasure (lawOf volume pG 0) := by rw [lawOf_pG]; infer_instance
    simp_rw [deriv_score_pG]; exact integrable_const (-1 : ℝ)
  have hZ : HasLaw id ((gaussianReal (h * √(fisherInformation volume pG 0)) 1).map
      fun x : ℝ => x ^ 2) ((gaussianReal h 1).map fun x : ℝ => x ^ 2) := by
    rw [fisherInformation_pG, Real.sqrt_one, mul_one]; exact HasLaw.id
  have hroot : ∀ n, {ω : ℕ → ℝ | ∑ i ∈ Finset.range n,
      score pG (localMean h n ω) (localSample h n i ω) ≠ 0} = ∅ :=
    fun n => Set.eq_empty_iff_forall_notMem.2 fun ω hω => hω (sum_score_localMean h n ω)
  have hroot' : Tendsto (fun n => sampleG {ω | ∑ i ∈ Finset.range n,
      score pG (localMean h n ω) (localSample h n i ω) ≠ 0}) atTop (𝓝 0) := by
    simp_rw [hroot, measure_empty]; exact tendsto_const_nhds
  exact tendstoInDistribution_two_mul_logLikelihood_sub_local (δ := 1) (M := fun _ => 0)
    (θhat := localMean h)
    one_pos pG_pos measurable_uncurry_pG (hasLaw_localSample h) (iIndepFun_localSample h)
    (fun x θ _ => differentiableAt_log_pG x θ) (fun x θ _ => by rw [score_pG_fun]; fun_prop)
    (fun x θ _ => by simp_rw [deriv_score_pG]; fun_prop) measurable_const
    (integrable_zero _ _ _) (fun x θ _ => by rw [deriv_deriv_score_pG, abs_zero])
    measurable_score_pG integrable_score_pG_sq integral_score_pG hd hdi integral_deriv_score_pG
    (by rw [fisherInformation_pG]; exact one_pos)
    (fun n => ((measurable_sampleMean n).add_const _).aemeasurable) hroot'
    (tendstoInMeasure_localMean h) hZ

#print axioms tendstoInDistribution_logLikelihoodRatio_local_pG

end MathlibExtTest.Probability.Statistics.LikelihoodRatioLocalPower
