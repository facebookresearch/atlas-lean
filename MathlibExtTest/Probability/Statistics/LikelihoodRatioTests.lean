/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LikelihoodRatioTests
public import MathlibExtTest.Probability.Statistics.MLEAsymptoticNormality

/-!
# Tests for the score, Wald and likelihood-ratio tests

* Non-vacuity: for the Gaussian location family `N(θ, 1)` at `θ₀ = 0` with the sample mean
  as the root of the likelihood equation (from the tests of `MLEAsymptoticNormality`), every
  hypothesis of the score, Wald and Wilks theorems and of the boundary theorem holds; the
  supremum form of Wilks' theorem applies because the sample mean maximizes the Gaussian
  log-likelihood. The Wald test is instantiated with the observed information.
* The law identities on concrete inputs, and the mixture `½ δ₀ + ½ χ²₁` is a probability
  measure with an atom of mass `½` at `0`.
* Boundary (junk value): an estimated information equal to `0` makes the score statistic `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Statistics.FisherInformation
open MathlibExt.Probability.Statistics.MLEAsymptoticNormality
open MathlibExt.Probability.Statistics.LikelihoodRatioTests
open MathlibExtTest.Probability.Statistics.MLEAsymptoticNormality

namespace MathlibExtTest.Probability.Statistics.LikelihoodRatioTests

/-- The chi-square law with one degree of freedom is a probability measure. -/
instance : IsProbabilityMeasure (chiSquareMeasure 1) :=
  isProbabilityMeasure_chiSquareMeasure one_pos

/-- The chi-bar-square mixture `½ δ₀ + ½ χ²₁`. -/
noncomputable def chiBarSq : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • chiSquareMeasure 1

/-- The mixture is a probability measure. -/
instance : IsProbabilityMeasure chiBarSq :=
  ⟨by simp [chiBarSq, ENNReal.inv_two_add_inv_two]⟩

/-- `χ²₁` has no atom at `0`: it is the image of `N(0, 1)`, which has no atoms. -/
theorem chiSquareMeasure_one_zero : chiSquareMeasure 1 {0} = 0 := by
  rw [← gaussianReal_map_sq, Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have : (fun x : ℝ => x ^ 2) ⁻¹' {0} = {0} := by ext x; simp
  rw [this]
  exact (gaussianReal_absolutelyContinuous 0 one_ne_zero) Real.volume_singleton

/-- The mixture `½ δ₀ + ½ χ²₁` has an atom of mass exactly `½` at `0`. -/
example : chiBarSq {0} = 2⁻¹ := by
  simp [chiBarSq, chiSquareMeasure_one_zero]

/-- The law identity for `N(0, 4)`: `Y² / 4 ~ χ²₁`. -/
example : (gaussianReal 0 4).map (fun x : ℝ => x ^ 2 / 4) = chiSquareMeasure 1 := by
  simpa using gaussianReal_map_sq_div (v := 4) (by norm_num)

/-! ### The Gaussian location family -/

/-- The score of `N(θ, 1)` at `0` is square integrable. -/
theorem integrable_score_pG_sq : Integrable (fun x => score pG 0 x ^ 2) (lawOf volume pG 0) := by
  simp only [score_pG, sub_zero, lawOf_pG]
  exact (memLp_id_gaussianReal 2).integrable_sq

/-- The score of `N(θ, 1)` at `0` has mean zero. -/
theorem integral_score_pG : ∫ x, score pG 0 x ∂lawOf volume pG 0 = 0 := by
  simp only [score_pG, sub_zero, lawOf_pG]; exact integral_id_gaussianReal

/-- The information identity for `N(θ, 1)` at `0`. -/
theorem integral_deriv_score_pG :
    ∫ x, deriv (fun t => score pG t x) 0 ∂lawOf volume pG 0 = -fisherInformation volume pG 0 := by
  have : IsProbabilityMeasure (lawOf volume pG 0) := by rw [lawOf_pG]; infer_instance
  simp [deriv_score_pG, fisherInformation_pG]

/-- The score at `0` is measurable. -/
theorem measurable_score_pG : Measurable (score pG 0) := by
  rw [show score pG 0 = fun x => x - 0 from funext fun x => score_pG 0 x]; fun_prop

/-- The density `(θ, x) ↦ pG θ x` is jointly measurable. -/
theorem measurable_uncurry_pG : Measurable (Function.uncurry pG) := by
  unfold pG gaussianPDFReal Function.uncurry
  fun_prop

/-- The sample mean is measurable. -/
theorem measurable_sampleMean (n : ℕ) : Measurable (sampleMean n) :=
  (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).div_const _

/-- The sample mean solves the likelihood equation on every sample. -/
theorem tendsto_root_sampleMean :
    Tendsto (fun n => sampleG {ω | ∑ i ∈ Finset.range n, score pG (sampleMean n ω) (ω i) ≠ 0})
      atTop (𝓝 0) := by
  have h : ∀ n, {ω : ℕ → ℝ | ∑ i ∈ Finset.range n, score pG (sampleMean n ω) (ω i) ≠ 0} = ∅ :=
    fun n => by ext ω; simp [sum_score_sampleMean]
  simp_rw [h, measure_empty]
  exact tendsto_const_nhds

/-- **Non-vacuity of Rao's score test**: `(n^{-1/2} ∑_{i<n} X i)² → χ²₁`. -/
theorem tendstoInDistribution_scoreStatistic_pG :
    TendstoInDistribution
      (fun (n : ℕ) ω => ((√n)⁻¹ * ∑ i ∈ Finset.range n, score pG 0 (ω i)) ^ 2 /
        fisherInformation volume pG 0) atTop id (fun _ => sampleG) (chiSquareMeasure 1) :=
  tendstoInDistribution_scoreStatistic (fun x => pG_pos 0 x) (measurable_gaussianPDFReal 0 1)
    (fun x => differentiableAt_pG x 0) hasLaw_coord iIndepFun_coord measurable_score_pG
    integrable_score_pG_sq integral_score_pG (by rw [fisherInformation_pG]; exact one_pos)
    HasLaw.id

/-- **Non-vacuity of Wald's test with the observed information**:
`n X̄ₙ² Îₙ → χ²₁`, `Îₙ = -(1/n) ∑_{i<n} ∂_θ score`. -/
theorem tendstoInDistribution_waldStatistic_pG :
    TendstoInDistribution
      (fun (n : ℕ) ω => (n : ℝ) * (sampleMean n ω - 0) ^ 2 *
        -((∑ i ∈ Finset.range n, deriv (fun t => score pG t (ω i)) 0) / n))
      atTop id (fun _ => sampleG) (chiSquareMeasure 1) := by
  have hd : Measurable fun x => deriv (fun t => score pG t x) 0 := by
    simp_rw [deriv_score_pG]; fun_prop
  have hdi : Integrable (fun x => deriv (fun t => score pG t x) 0) (lawOf volume pG 0) := by
    have : IsProbabilityMeasure (lawOf volume pG 0) := by rw [lawOf_pG]; infer_instance
    simp_rw [deriv_score_pG]; exact integrable_const (-1 : ℝ)
  refine tendstoInDistribution_waldStatistic_of_estimator (δ := 1) (M := fun _ => 0)
    one_pos pG_pos (measurable_gaussianPDFReal 0 1) hasLaw_coord iIndepFun_coord
    (fun x θ _ => differentiableAt_log_pG x θ) (fun x θ _ => by rw [score_pG_fun]; fun_prop)
    (fun x θ _ => by simp_rw [deriv_score_pG]; fun_prop) measurable_const
    (integrable_zero _ _ _) (fun x θ _ => by rw [deriv_deriv_score_pG, abs_zero])
    measurable_score_pG integrable_score_pG_sq integral_score_pG hd hdi integral_deriv_score_pG
    (by rw [fisherInformation_pG]; exact one_pos) (fun n => (measurable_sampleMean n).aemeasurable)
    tendsto_root_sampleMean tendstoInMeasure_sampleMean (fun n => ?_)
    (tendstoInMeasure_observedInformation hasLaw_coord iIndepFun_coord hd hdi
      integral_deriv_score_pG) HasLaw.id
  exact ((Finset.aemeasurable_fun_sum _ fun i _ =>
    hd.comp_aemeasurable (measurable_pi_apply i).aemeasurable).div_const _).neg

/-- **Non-vacuity of Wilks' theorem**: `2 (ℓₙ(X̄ₙ) - ℓₙ(0)) → χ²₁` for `N(θ, 1)`. -/
theorem tendstoInDistribution_logLikelihoodRatio_pG :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
        (Real.log (pG (sampleMean n ω) (ω i)) - Real.log (pG 0 (ω i))))
      atTop id (fun _ => sampleG) (chiSquareMeasure 1) := by
  have hd : Measurable fun x => deriv (fun t => score pG t x) 0 := by
    simp_rw [deriv_score_pG]; fun_prop
  have hdi : Integrable (fun x => deriv (fun t => score pG t x) 0) (lawOf volume pG 0) := by
    have : IsProbabilityMeasure (lawOf volume pG 0) := by rw [lawOf_pG]; infer_instance
    simp_rw [deriv_score_pG]; exact integrable_const (-1 : ℝ)
  exact tendstoInDistribution_two_mul_logLikelihood_sub (δ := 1) (M := fun _ => 0)
    one_pos pG_pos measurable_uncurry_pG hasLaw_coord iIndepFun_coord
    (fun x θ _ => differentiableAt_log_pG x θ) (fun x θ _ => by rw [score_pG_fun]; fun_prop)
    (fun x θ _ => by simp_rw [deriv_score_pG]; fun_prop) measurable_const
    (integrable_zero _ _ _) (fun x θ _ => by rw [deriv_deriv_score_pG, abs_zero])
    measurable_score_pG integrable_score_pG_sq integral_score_pG hd hdi integral_deriv_score_pG
    (by rw [fisherInformation_pG]; exact one_pos) (fun n => (measurable_sampleMean n).aemeasurable)
    tendsto_root_sampleMean tendstoInMeasure_sampleMean HasLaw.id

/-- **Non-vacuity of the boundary theorem**: for `N(θ, 1)` with `θ ∈ [0, ∞)` and `θ₀ = 0`,
`2 (ℓₙ(max X̄ₙ 0) - ℓₙ(0)) → ½ δ₀ + ½ χ²₁`. -/
theorem tendstoInDistribution_logLikelihoodRatio_max_zero_pG :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
        (Real.log (pG (max (sampleMean n ω) 0) (ω i)) - Real.log (pG 0 (ω i))))
      atTop id (fun _ => sampleG) chiBarSq := by
  have hd : Measurable fun x => deriv (fun t => score pG t x) 0 := by
    simp_rw [deriv_score_pG]; fun_prop
  have hdi : Integrable (fun x => deriv (fun t => score pG t x) 0) (lawOf volume pG 0) := by
    have : IsProbabilityMeasure (lawOf volume pG 0) := by rw [lawOf_pG]; infer_instance
    simp_rw [deriv_score_pG]; exact integrable_const (-1 : ℝ)
  exact tendstoInDistribution_two_mul_logLikelihood_max_zero_sub (δ := 1) (M := fun _ => 0)
    one_pos pG_pos measurable_uncurry_pG hasLaw_coord iIndepFun_coord
    (fun x θ _ => differentiableAt_log_pG x θ) (fun x θ _ => by rw [score_pG_fun]; fun_prop)
    (fun x θ _ => by simp_rw [deriv_score_pG]; fun_prop) measurable_const
    (integrable_zero _ _ _) (fun x θ _ => by rw [deriv_deriv_score_pG, abs_zero])
    measurable_score_pG integrable_score_pG_sq integral_score_pG hd hdi integral_deriv_score_pG
    (by rw [fisherInformation_pG]; exact one_pos) (fun n => (measurable_sampleMean n).aemeasurable)
    tendsto_root_sampleMean tendstoInMeasure_sampleMean HasLaw.id

/-- The sample mean maximizes the Gaussian log-likelihood: `∑ (x_i - θ)²` is minimal at the
mean. -/
theorem logLikelihood_le_sampleMean (n : ℕ) (ω : ℕ → ℝ) (θ : ℝ) :
    ∑ i ∈ Finset.range n, Real.log (pG θ (ω i)) ≤
      ∑ i ∈ Finset.range n, Real.log (pG (sampleMean n ω) (ω i)) := by
  simp only [log_pG]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- `∑ (x - θ)² = ∑ (x - m)² + n (m - θ)²` with `m` the sample mean
  have hsum : ∑ i ∈ Finset.range n, ω i = n * sampleMean n ω := by
    simp only [sampleMean]; field_simp
  have key : ∑ i ∈ Finset.range n, (ω i - θ) ^ 2 =
      ∑ i ∈ Finset.range n, (ω i - sampleMean n ω) ^ 2 + n * (sampleMean n ω - θ) ^ 2 := by
    have e : ∀ i, (ω i - θ) ^ 2 = (ω i - sampleMean n ω) ^ 2 +
        2 * (sampleMean n ω - θ) * ω i +
          ((sampleMean n ω - θ) ^ 2 - 2 * (sampleMean n ω - θ) * sampleMean n ω) := fun i => by
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, hsum]
    ring
  have hle : ∑ i ∈ Finset.range n, (ω i - sampleMean n ω) ^ 2 ≤
      ∑ i ∈ Finset.range n, (ω i - θ) ^ 2 := by
    rw [key]; nlinarith [sq_nonneg (sampleMean n ω - θ)]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
  linarith [div_le_div_of_nonneg_right hle (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Non-vacuity of the supremum form of Wilks' theorem** for `N(θ, 1)`. -/
theorem tendstoInDistribution_iSup_logLikelihood_pG :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ((⨆ θ, ∑ i ∈ Finset.range n, Real.log (pG θ (ω i))) -
        ∑ i ∈ Finset.range n, Real.log (pG 0 (ω i))))
      atTop id (fun _ => sampleG) (chiSquareMeasure 1) := by
  have hd : Measurable fun x => deriv (fun t => score pG t x) 0 := by
    simp_rw [deriv_score_pG]; fun_prop
  have hdi : Integrable (fun x => deriv (fun t => score pG t x) 0) (lawOf volume pG 0) := by
    have : IsProbabilityMeasure (lawOf volume pG 0) := by rw [lawOf_pG]; infer_instance
    simp_rw [deriv_score_pG]; exact integrable_const (-1 : ℝ)
  exact tendstoInDistribution_two_mul_iSup_logLikelihood_sub (δ := 1) (M := fun _ => 0)
    one_pos pG_pos measurable_uncurry_pG hasLaw_coord iIndepFun_coord
    (fun x θ _ => differentiableAt_log_pG x θ) (fun x θ _ => by rw [score_pG_fun]; fun_prop)
    (fun x θ _ => by simp_rw [deriv_score_pG]; fun_prop) measurable_const
    (integrable_zero _ _ _) (fun x θ _ => by rw [deriv_deriv_score_pG, abs_zero])
    measurable_score_pG integrable_score_pG_sq integral_score_pG hd hdi integral_deriv_score_pG
    (by rw [fisherInformation_pG]; exact one_pos) (fun n => (measurable_sampleMean n).aemeasurable)
    tendsto_root_sampleMean tendstoInMeasure_sampleMean
    (fun n ω θ => logLikelihood_le_sampleMean n ω θ) HasLaw.id

/-- Boundary (junk value): where the estimated information is `0`, the score statistic is `0`
(Lean's `x / 0 = 0`); the estimator version only needs this event to become negligible. -/
example (s : ℝ) : s ^ 2 / (0 : ℝ) = 0 := div_zero _

#print axioms tendstoInDistribution_logLikelihoodRatio_pG
#print axioms tendstoInDistribution_logLikelihoodRatio_max_zero_pG

end MathlibExtTest.Probability.Statistics.LikelihoodRatioTests
