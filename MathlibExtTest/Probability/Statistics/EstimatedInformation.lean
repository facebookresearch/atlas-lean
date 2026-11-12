/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.EstimatedInformation
public import MathlibExtTest.Probability.Statistics.VectorInference

/-!
# Tests for estimated information in regular likelihood inference

* Boundary: the observed information of the empty sample is `0`, computed from the definition,
  so `Ĵ₀ ≠ I(θ₀)` whenever `E` is nontrivial; and `Ring.inverse 0 = 0`, so the score statistic
  with a singular information estimate is `0`.
* The observed information of the Gaussian location family `N(θ, Id)` (reused from the
  `VectorInference` tests) is `Id` for every `n ≥ 1` and every `θ`, computed from the definition.
* Non-vacuity on the Gaussian location family with the sample mean as root: every hypothesis
  of the observed-information consistency theorems, of Wald's test with `Ĵₙ(X̄ₙ)`, of Rao's
  test with `Ĵₙ(0)`, and of the likelihood-ratio/estimated-Wald equivalence holds.
* `TendstoInMeasure.continuousAt_comp_const` on a deterministic sequence `1 / (n + 1) → 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)
open MathlibExt.Probability.Statistics.VectorInference
open MathlibExt.Probability.Statistics.EstimatedInformation
open MathlibExtTest.Probability.Statistics.VectorInference

namespace MathlibExtTest.Probability.Statistics.EstimatedInformation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Boundary values computed from the definitions -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Boundary `n = 0`: the observed information of the empty sample is `0`. -/
example (x : ℕ → E) (θ : E) : observedInformation pE 0 x θ = 0 := by
  simp [observedInformation]

omit [MeasurableSpace E] [BorelSpace E] in
/-- At `n = 0` the observed information differs from `I(0) = Id` on a nontrivial space, so the
consistency theorems are statements about the limit, not an identity at every `n`. -/
example [Nontrivial E] (x : ℕ → E) (θ : E) :
    observedInformation pE 0 x θ ≠ ContinuousLinearMap.id ℝ E := by
  rw [observedInformation_zero]
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  intro h
  have := congrArg (fun A : E →L[ℝ] E => A v) h
  simp only [zero_apply, ContinuousLinearMap.id_apply] at this
  exact hv this.symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Boundary of the `Ring.inverse` convention: the score statistic with the singular estimate
`Î = 0` is `0`. -/
example (S : E) : ⟪Ring.inverse (0 : E →L[ℝ] E) S, S⟫ = 0 := by
  simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Observed information of the Gaussian location family**: `Ĵₙ(θ) = Id` for `n ≥ 1`. -/
theorem observedInformation_pE {n : ℕ} (hn : 0 < n) (x : ℕ → E) (θ : E) :
    observedInformation pE n x θ = ContinuousLinearMap.id ℝ E := by
  simp only [observedInformation, fderiv_score_pE, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_range, smul_neg, neg_neg]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
    one_smul]

/-! ### Non-vacuity on the Gaussian location family -/

omit [MeasurableSpace E] [BorelSpace E] in
private theorem hD : (fun x : E => fderiv ℝ (fun t => score pE t x) 0) =
    fun _ => -ContinuousLinearMap.id ℝ E := funext fun x => fderiv_score_pE x 0

omit [BorelSpace E] in
private theorem hDs_meas :
    Measurable fun q : E × E => fderiv ℝ (fun t => score pE t q.2) q.1 := by
  have e : (fun q : E × E => fderiv ℝ (fun t => score pE t q.2) q.1) =
      fun _ => -ContinuousLinearMap.id ℝ E := funext fun q => fderiv_score_pE q.2 q.1
  rw [e]; exact measurable_const

private theorem hs_sq :
    Integrable (fun x => ‖score pE (0 : E) x‖ ^ 2) (lawOf (stdGaussian E) pE 0) :=
  memLp_score_pE.integrable_norm_pow two_ne_zero

private theorem hmean : ∫ x, score pE (0 : E) x ∂(lawOf (stdGaussian E) pE 0) = 0 := by
  simp only [score_pE, sub_zero, lawOf_pE]; exact integral_id_stdGaussian

private theorem hinfo : ∫ x, fderiv ℝ (fun t => score pE t x) 0 ∂(lawOf (stdGaussian E) pE 0) =
    -fisherInformation (stdGaussian E) pE 0 := by
  have : IsProbabilityMeasure (lawOf (stdGaussian E) pE 0) := by rw [lawOf_pE]; infer_instance
  rw [hD, fisherInformation_pE]; simp

/-- **Non-vacuity of `tendstoInMeasure_observedInformation_of_tendstoInMeasure`**: the observed
information at the sample mean converges to `I(0) = Id`. -/
theorem tendstoInMeasure_observedInformation_sampleMean :
    TendstoInMeasure sampleE
      (fun n (ω : ℕ → E) => observedInformation pE n (fun i => ω i) (sampleMean n ω)) atTop
      (fun _ => fisherInformation (stdGaussian E) pE 0) := by
  have : IsProbabilityMeasure (lawOf (stdGaussian E) pE 0) := by rw [lawOf_pE]; infer_instance
  exact tendstoInMeasure_observedInformation_of_tendstoInMeasure (ν := stdGaussian E) (p := pE)
    (θ₀ := 0) (δ := 1) (M := fun _ => 0) one_pos hasLaw_coord iIndepFun_coord measurable_const
    (integrable_const _) (fun x θ _ => by rw [fderiv_score_pE, fderiv_score_pE]; simp)
    (by rw [hD]; exact stronglyMeasurable_const) (by rw [hD]; exact integrable_const _) hinfo
    (fun n => (measurable_sampleMean n).aemeasurable) tendstoInMeasure_sampleMean

/-- **Non-vacuity of `tendstoInDistribution_waldStatistic_observedInformation`**: the Wald
statistic with the observed information at the sample mean converges to `χ²_d`. -/
theorem tendstoInDistribution_wald_observedInformation_sampleMean [Nontrivial E] :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → E) => n * ⟪observedInformation pE n (fun i => ω i) (sampleMean n ω)
        (sampleMean n ω - 0), sampleMean n ω - 0⟫) atTop id (fun _ => sampleE)
      (chiSquareMeasure (Module.finrank ℝ E)) := by
  have : IsProbabilityMeasure (lawOf (stdGaussian E) pE 0) := by rw [lawOf_pE]; infer_instance
  exact tendstoInDistribution_waldStatistic_observedInformation (ν := stdGaussian E) (p := pE)
    (θ₀ := 0) (δ := 1) (M := fun _ => 0) one_pos hasLaw_coord iIndepFun_coord
    (fun x θ _ => by simp_rw [score_pE]; fun_prop) measurable_const (integrable_const _)
    (fun x θ _ => by rw [fderiv_score_pE, fderiv_score_pE]; simp)
    (by rw [score_pE_zero]; exact measurable_id) hs_sq hmean hDs_meas
    (by rw [hD]; exact integrable_const _) hinfo fisherInformation_pE_pos Module.finrank_pos
    (fun n => (measurable_sampleMean n).aemeasurable) (tendsto_root _ rfl)
    tendstoInMeasure_sampleMean HasLaw.id

/-- **Non-vacuity of `tendstoInDistribution_scoreStatistic_observedInformation`**: Rao's
statistic with the observed information at `0` converges to `χ²_d`. -/
theorem tendstoInDistribution_score_observedInformation_sample [Nontrivial E] :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → E) =>
        ⟪Ring.inverse (observedInformation pE n (fun i => ω i) 0)
            ((√n)⁻¹ • ∑ i ∈ Finset.range n, score pE 0 (ω i)),
          (√n)⁻¹ • ∑ i ∈ Finset.range n, score pE 0 (ω i)⟫)
      atTop id (fun _ => sampleE) (chiSquareMeasure (Module.finrank ℝ E)) :=
  tendstoInDistribution_scoreStatistic_observedInformation (ν := stdGaussian E) (p := pE)
    (θ₀ := 0) hasLaw_coord iIndepFun_coord (by rw [score_pE_zero]; exact measurable_id) hs_sq
    hmean (by rw [hD]; exact stronglyMeasurable_const) (by
      have : IsProbabilityMeasure (lawOf (stdGaussian E) pE 0) := by
        rw [lawOf_pE]; infer_instance
      rw [hD]; exact integrable_const _) hinfo fisherInformation_pE_pos Module.finrank_pos
    HasLaw.id

/-- **Non-vacuity of `tendstoInMeasure_two_mul_logLikelihood_sub_sub_of_estimator`**: the
likelihood ratio at the sample mean minus the Wald statistic with the observed information at
the sample mean tends to `0` in probability. -/
theorem tendstoInMeasure_wilks_sub_wald_observedInformation_sampleMean :
    TendstoInMeasure sampleE
      (fun (n : ℕ) (ω : ℕ → E) => 2 * ∑ i ∈ Finset.range n,
          (Real.log (pE (sampleMean n ω) (ω i)) - Real.log (pE 0 (ω i))) -
        n * ⟪observedInformation pE n (fun i => ω i) (sampleMean n ω) (sampleMean n ω - 0),
          sampleMean n ω - 0⟫)
      atTop 0 := by
  have : IsProbabilityMeasure (lawOf (stdGaussian E) pE 0) := by rw [lawOf_pE]; infer_instance
  have hJ_meas : ∀ n, AEMeasurable
      (fun ω : ℕ → E => observedInformation pE n (fun i => ω i) (sampleMean n ω)) sampleE :=
    fun n => aemeasurable_observedInformation_comp hDs_meas
      (fun i => (measurable_pi_apply i).aemeasurable) (measurable_sampleMean n).aemeasurable n
  exact tendstoInMeasure_two_mul_logLikelihood_sub_sub_of_estimator (ν := stdGaussian E)
    (p := pE) (θ₀ := 0) (δ := 1) (M := fun _ => 0) one_pos hasLaw_coord iIndepFun_coord
    (fun x θ _ => (hasFDerivAt_log_pE θ x).differentiableAt)
    (fun x θ _ => by simp_rw [score_pE]; fun_prop) measurable_const (integrable_const _)
    (fun x θ _ => by rw [fderiv_score_pE, fderiv_score_pE]; simp)
    (by rw [score_pE_zero]; exact measurable_id) hs_sq hmean
    (by rw [hD]; exact stronglyMeasurable_const) (by rw [hD]; exact integrable_const _) hinfo
    (isUnit_of_inner_self_pos fisherInformation_pE_pos)
    (fun n => (measurable_sampleMean n).aemeasurable) (tendsto_root _ rfl)
    tendstoInMeasure_sampleMean hJ_meas tendstoInMeasure_observedInformation_sampleMean

/-! ### Continuous mapping on a deterministic sequence -/

/-- `TendstoInMeasure.continuousAt_comp_const`: `1 / (n + 1) → 0` deterministically, hence in
probability, and `exp` is continuous, so `exp (1 / (n + 1)) → 1` in probability. -/
example : TendstoInMeasure (sampleE (E := E)) (fun (n : ℕ) _ => Real.exp (1 / ((n : ℝ) + 1)))
    atTop (fun _ => 1) := by
  have h : TendstoInMeasure (sampleE (E := E)) (fun (n : ℕ) _ => 1 / ((n : ℝ) + 1)) atTop
      (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => tendsto_one_div_add_atTop_nhds_zero_nat)
  simpa using h.continuousAt_comp_const Real.continuous_exp.continuousAt

end MathlibExtTest.Probability.Statistics.EstimatedInformation
