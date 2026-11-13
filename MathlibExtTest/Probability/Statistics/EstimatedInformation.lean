/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.EstimatedInformation
public import MathlibExtTest.Probability.Statistics.VectorInference
import MathlibExt.Probability.BrownianQuadraticVariation

/-!
# Tests for estimated information in regular likelihood inference

* Boundary: the observed information of the empty sample is `0`, computed from the definition,
  so `Ĵ₀ ≠ I(θ₀)` whenever `E` is nontrivial; and `Ring.inverse 0 = 0`, so the score statistic
  with a singular information estimate is `0`.
* The observed information of the Gaussian location family `N(θ, Id)` (reused from the
  `VectorInference` tests) is `Id` for every `n ≥ 1` and every `θ`, computed from the definition.
* Non-vacuity on the Gaussian location family with the sample mean as root: every hypothesis
  of the observed-information consistency theorems, of Wald's test with `Ĵₙ(X̄ₙ)`, of Rao's
  test with `Ĵₙ(0)`, and of the likelihood-ratio/estimated-Wald equivalence holds. There `Ĵₙ`
  is the constant `Id`, so this instance does not exercise a random information estimate.
* A genuinely random `Ĵₙ`: the Gaussian family `N(0, θ)` with unknown variance `θ` (density
  `pV θ` with respect to `N(0, 1)`, `lawOf_pV_eq`), null `θ₀ = 1`, `I(1) = Id/2` computed from
  the definition (using `E X⁴ = 3`). The MLE `θ̂ₙ = n⁻¹ ∑ Xᵢ²` solves the likelihood equation
  almost surely for every `n ≥ 1` (`ae_sum_score_varHat_eq_zero`) and is consistent by the
  strong law (`tendstoInMeasure_varHat`), which gives `hroot` (`tendsto_rootV`). The envelope is
  `M x = 5 + 38 x²` on the ball of radius `1/2`, and `(θ, x) ↦ D_θ score` is jointly measurable
  (at `θ = 0` the score is not differentiable, `not_differentiableAt_score_pV_zero`). Every
  hypothesis of observed-information consistency at `1` and at `θ̂ₙ`, Wald with `Ĵₙ(θ̂ₙ)`, Rao
  with `Ĵₙ(1)`, likelihood ratio minus Wald with `Ĵₙ(θ̂ₙ)`, and the `VectorInference` Wilks
  theorem is discharged. `Ĵₙ(1) = (θ̂ₙ - 1/2) · Id` and `Ĵₙ(θ̂ₙ) = (2 θ̂ₙ²)⁻¹ · Id` each take
  values on both sides of a gap with positive probability for every `n ≥ 1`
  (`observedInformation_one_random`, `observedInformation_varHat_random`), so `Ĵₙ(θ̂ₙ)` is not
  a.s. constant (`not_ae_const_observedInformation_varHat`).
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

/-! ### A genuinely random `Ĵₙ`: the Gaussian family `N(0, θ)` with unknown variance

The family is written as the density `pV θ x = exp(-log θ / 2 - x² / (2θ) + x² / 2)` of
`N(0, θ)` with respect to `N(0, 1)` (`lawOf_pV_eq`), at the null `θ₀ = 1`, so the data law is
`N(0, 1)`. The score derivative `(1/(2θ²) - x²/θ³) · Id` depends on `x`, so the observed
information is random both at the null, `Ĵₙ(1) = (n⁻¹ ∑ Xᵢ² - 1/2) · Id`, and at the MLE
`θ̂ₙ = n⁻¹ ∑ Xᵢ²`, `Ĵₙ(θ̂ₙ) = (2 θ̂ₙ²)⁻¹ · Id`. -/

section VarianceFamily

/-- The log-density of `N(0, θ)` relative to `N(0, 1)`: `-log θ / 2 - x² / (2θ) + x² / 2`. -/
noncomputable def ellV (θ x : ℝ) : ℝ := -(Real.log θ) / 2 - x ^ 2 / (2 * θ) + x ^ 2 / 2

/-- The density of `N(0, θ)` with respect to `N(0, 1)` (for `θ > 0`; `lawOf_pV_eq`). -/
noncomputable def pV (θ x : ℝ) : ℝ := Real.exp (ellV θ x)

/-- The log-density is `ellV`. -/
theorem log_pV (θ x : ℝ) : Real.log (pV θ x) = ellV θ x := Real.log_exp _

/-- Derivative of the log-density in `θ ≠ 0`: `-1/(2θ) + x²/(2θ²)`. -/
private theorem hasDerivAt_ellV {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    HasDerivAt (fun t => ellV t x) (-1 / (2 * θ) + x ^ 2 / (2 * θ ^ 2)) θ := by
  have h1 := (Real.hasDerivAt_log hθ).div_const (-2)
  have h2 := (hasDerivAt_inv hθ).const_mul (-(x ^ 2) / 2)
  have h := (h1.add h2).add_const (x ^ 2 / 2)
  convert h using 1
  · funext t; simp only [ellV, Pi.add_apply]; field_simp; ring
  · field_simp

/-- The score of the variance family at `θ ≠ 0` is `-1/(2θ) + x²/(2θ²)`. -/
theorem score_pV {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    score pV θ x = -1 / (2 * θ) + x ^ 2 / (2 * θ ^ 2) := by
  rw [score, gradient_eq_deriv']
  simp_rw [log_pV]
  exact (hasDerivAt_ellV hθ x).deriv

/-- Derivative of the closed-form score in `θ ≠ 0`. -/
private theorem hasDerivAt_scoreV {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    HasDerivAt (fun t => -1 / (2 * t) + x ^ 2 / (2 * t ^ 2))
      (1 / (2 * θ ^ 2) - x ^ 2 / θ ^ 3) θ := by
  have h1 := (hasDerivAt_inv hθ).const_mul (-1 / 2 : ℝ)
  have h2 := ((hasDerivAt_inv hθ).pow 2).const_mul (x ^ 2 / 2)
  convert h1.add h2 using 1
  · funext t; simp only [Pi.add_apply, Pi.pow_apply]; field_simp
  · simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; field_simp; ring

/-- The score derivative at `θ ≠ 0` is `(1/(2θ²) - x²/θ³) · Id`; it depends on `x`. -/
theorem fderiv_score_pV {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    fderiv ℝ (fun t => score pV t x) θ =
      (1 / (2 * θ ^ 2) - x ^ 2 / θ ^ 3) • (1 : ℝ →L[ℝ] ℝ) := by
  have he : (fun t => score pV t x) =ᶠ[𝓝 θ] fun t => -1 / (2 * t) + x ^ 2 / (2 * t ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hθ] with t ht
    exact score_pV ht x
  rw [he.fderiv_eq, (hasDerivAt_scoreV hθ x).hasFDerivAt.fderiv]
  ext; simp


/-- At `θ₀ = 1` the density is `1`. -/
private theorem pV_one (x : ℝ) : pV 1 x = 1 := by simp [pV, ellV]

/-- At `θ₀ = 1` the data law is `N(0, 1)`. -/
theorem lawOf_pV : lawOf (gaussianReal 0 1) pV 1 = gaussianReal 0 1 := by
  have : (fun x => ENNReal.ofReal (pV 1 x)) = 1 := by funext x; simp [pV_one]
  rw [lawOf, this, withDensity_one]

/-- The score at `θ₀ = 1` is `(x² - 1)/2`. -/
theorem score_pV_one : score pV 1 = fun x => (x ^ 2 - 1) / 2 := by
  funext x; rw [score_pV one_ne_zero]; ring

/-- The score derivative at `θ₀ = 1` is `(1/2 - x²) · Id`. -/
theorem fderiv_score_pV_one (x : ℝ) :
    fderiv ℝ (fun t => score pV t x) 1 = (1 / 2 - x ^ 2) • (1 : ℝ →L[ℝ] ℝ) := by
  rw [fderiv_score_pV one_ne_zero]; norm_num

/-- `x²` is in `L²(N(0, 1))`. -/
private theorem memLp_sq_gaussianReal : MemLp (fun x : ℝ ↦ x ^ 2) 2 (gaussianReal 0 1) := by
  have h4 : MemLp (fun x : ℝ ↦ x) 4 (gaussianReal 0 1) := memLp_id_gaussianReal 4
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    change (↑(4 : NNReal) : ENNReal)⁻¹ + (↑(4 : NNReal) : ENNReal)⁻¹ = (↑(2 : NNReal) : ENNReal)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0), ← ENNReal.coe_add]
    norm_num⟩
  convert (h4.mul h4 : MemLp _ 2 _) using 1
  ext x
  simp [pow_two]

/-- The score at `1` is square integrable. -/
theorem memLp_score_pV : MemLp (score pV 1) 2 (lawOf (gaussianReal 0 1) pV 1) := by
  rw [score_pV_one, lawOf_pV]
  have h := MemLp.const_mul (memLp_sq_gaussianReal.sub (memLp_const 1)) (1 / 2 : ℝ)
  convert h using 1
  funext x; simp only [Pi.sub_apply]; ring

/-- `E[((X² - 1)/2)²] = 1/2` for `X ~ N(0, 1)`. -/
private theorem integral_score_pV_sq :
    ∫ x, ((x ^ 2 - 1) / 2) ^ 2 ∂(gaussianReal 0 1) = 1 / 2 := by
  have hi2 := memLp_sq_gaussianReal.integrable (by norm_num)
  have hi4 : Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 1) := by
    convert memLp_sq_gaussianReal.integrable_sq using 1
    ext x; ring
  have he : (fun x : ℝ ↦ ((x ^ 2 - 1) / 2) ^ 2) = fun x ↦ (x ^ 4 - 2 * x ^ 2 + 1) / 4 := by
    ext x; ring
  rw [he, integral_div, integral_add (f := fun x : ℝ => x ^ 4 - 2 * x ^ 2)
    (hi4.sub (hi2.const_mul 2)) (integrable_const 1),
    integral_sub (f := fun x : ℝ => x ^ 4) hi4 (hi2.const_mul 2), integral_const_mul,
    integral_pow_four_gaussianReal,
    MathlibExtTest.Probability.Statistics.VectorInference.integral_sq_gaussianReal]
  simp; norm_num

/-- **Fisher information of the variance family at `1`**: `I(1) = Id/2`, computed from the
definition (the second moment of the score). -/
theorem fisherInformation_pV :
    fisherInformation (gaussianReal 0 1) pV 1 = (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ) := by
  refine ContinuousLinearMap.ext fun u => ext_inner_right ℝ fun v => ?_
  rw [inner_fisherInformation_apply memLp_score_pV]
  simp_rw [score_pV_one, lawOf_pV]
  have e : (fun x : ℝ => ⟪(x ^ 2 - 1) / 2, u⟫ * ⟪(x ^ 2 - 1) / 2, v⟫) =
      fun x => (u * v) * ((x ^ 2 - 1) / 2) ^ 2 := by
    funext x; simp only [RCLike.inner_apply, conj_trivial]; ring
  rw [e, integral_const_mul, integral_score_pV_sq]
  simp only [FunLike.coe_smul, Pi.smul_apply, one_apply_eq_self, smul_eq_mul,
    RCLike.inner_apply, conj_trivial]
  ring


/-- The data law at `1` is a probability measure. -/
private theorem isProbabilityMeasure_lawOf_pV :
    IsProbabilityMeasure (lawOf (gaussianReal 0 1) pV 1) := by
  rw [lawOf_pV]; infer_instance

/-- The score at `1` is measurable. -/
theorem measurable_score_pV : Measurable (score pV 1) := by
  rw [score_pV_one]; fun_prop

/-- `‖score‖²` at `1` is integrable. -/
theorem integrable_sq_norm_score_pV :
    Integrable (fun x => ‖score pV 1 x‖ ^ 2) (lawOf (gaussianReal 0 1) pV 1) :=
  memLp_score_pV.integrable_norm_pow two_ne_zero

/-- The score at `1` is centered. -/
theorem integral_score_pV : ∫ x, score pV 1 x ∂(lawOf (gaussianReal 0 1) pV 1) = 0 := by
  have hi2 := memLp_sq_gaussianReal.integrable (by norm_num)
  rw [score_pV_one, lawOf_pV, integral_div, integral_sub hi2 (integrable_const 1),
    MathlibExtTest.Probability.Statistics.VectorInference.integral_sq_gaussianReal]
  simp

/-- The score derivative at `1`, as a function of `x`. -/
private theorem hD_pV : (fun x => fderiv ℝ (fun t => score pV t x) 1) =
    fun x => (1 / 2 - x ^ 2) • (1 : ℝ →L[ℝ] ℝ) := funext fderiv_score_pV_one

/-- The score derivative at `1` is strongly measurable. -/
theorem stronglyMeasurable_fderiv_score_pV :
    StronglyMeasurable fun x => fderiv ℝ (fun t => score pV t x) 1 := by
  rw [hD_pV]
  exact (by fun_prop : Continuous fun x : ℝ =>
    (1 / 2 - x ^ 2) • (1 : ℝ →L[ℝ] ℝ)).stronglyMeasurable

/-- The score derivative at `1` is integrable. -/
theorem integrable_fderiv_score_pV :
    Integrable (fun x => fderiv ℝ (fun t => score pV t x) 1) (lawOf (gaussianReal 0 1) pV 1) := by
  have hi2 := memLp_sq_gaussianReal.integrable (by norm_num)
  rw [hD_pV, lawOf_pV]
  exact ((integrable_const _).sub hi2).smul_const _

/-- Information identity at `1`: `E D_θ score = -I(1)`. -/
theorem integral_fderiv_score_pV :
    ∫ x, fderiv ℝ (fun t => score pV t x) 1 ∂(lawOf (gaussianReal 0 1) pV 1) =
      -fisherInformation (gaussianReal 0 1) pV 1 := by
  have hi2 := memLp_sq_gaussianReal.integrable (by norm_num)
  rw [hD_pV, lawOf_pV, integral_smul_const, integral_sub (integrable_const _) hi2,
    MathlibExtTest.Probability.Statistics.VectorInference.integral_sq_gaussianReal,
    fisherInformation_pV]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [← neg_smul]; norm_num

/-- `I(1) = Id/2` is positive definite. -/
theorem fisherInformation_pV_pos (u : ℝ) (hu : u ≠ 0) :
    0 < ⟪fisherInformation (gaussianReal 0 1) pV 1 u, u⟫ := by
  rw [fisherInformation_pV]
  simp only [FunLike.coe_smul, Pi.smul_apply, one_apply_eq_self, smul_eq_mul, RCLike.inner_apply,
    conj_trivial]
  have := sq_pos_of_ne_zero hu
  nlinarith

/-- Points of the ball of radius `1/2` about `1` are nonzero. -/
private theorem ne_zero_of_mem_ball {θ : ℝ} (hθ : θ ∈ Metric.ball (1 : ℝ) (1 / 2)) : θ ≠ 0 := by
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hθ
  intro h; rw [h] at hθ; linarith [hθ.1]

/-- Near `θ ≠ 0` the score agrees with its closed form. -/
private theorem score_pV_eventuallyEq {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    (fun t => score pV t x) =ᶠ[𝓝 θ] fun t => -1 / (2 * t) + x ^ 2 / (2 * t ^ 2) := by
  filter_upwards [isOpen_ne.mem_nhds hθ] with t ht
  exact score_pV ht x

/-- The score is differentiable at every `θ ≠ 0`. -/
theorem differentiableAt_score_pV {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    DifferentiableAt ℝ (fun t => score pV t x) θ :=
  (hasDerivAt_scoreV hθ x).differentiableAt.congr_of_eventuallyEq (score_pV_eventuallyEq hθ x)

/-- The log-density is differentiable at every `θ ≠ 0`. -/
theorem differentiableAt_log_pV {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    DifferentiableAt ℝ (fun t => Real.log (pV t x)) θ := by
  simp_rw [log_pV]; exact (hasDerivAt_ellV hθ x).differentiableAt

/-- Lipschitz envelope `M x = 5 + 38 x²` on the ball of radius `1/2` about `1`. -/
theorem norm_fderiv_score_pV_sub_le (x : ℝ) {θ : ℝ} (hθ : θ ∈ Metric.ball (1 : ℝ) (1 / 2)) :
    ‖fderiv ℝ (fun t => score pV t x) θ - fderiv ℝ (fun t => score pV t x) 1‖ ≤
      (5 + 38 * x ^ 2) * ‖θ - 1‖ := by
  have hθ0 := ne_zero_of_mem_ball hθ
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hθ
  obtain ⟨h1, h2⟩ := hθ
  have hpos : 0 < θ := by linarith
  rw [fderiv_score_pV hθ0, fderiv_score_pV one_ne_zero, ← sub_smul, norm_smul, norm_one,
    mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
  have e : 1 / (2 * θ ^ 2) - x ^ 2 / θ ^ 3 - (1 / (2 * 1 ^ 2) - x ^ 2 / 1 ^ 3) =
      (θ - 1) * (-((1 + θ) / (2 * θ ^ 2)) + x ^ 2 * ((1 + θ + θ ^ 2) / θ ^ 3)) := by
    field_simp; ring
  rw [e, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have ha : (1 + θ) / (2 * θ ^ 2) ≤ 5 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have ha0 : 0 ≤ (1 + θ) / (2 * θ ^ 2) := by positivity
  have hb : (1 + θ + θ ^ 2) / θ ^ 3 ≤ 38 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [mul_pos hpos hpos]
  have hb0 : 0 ≤ (1 + θ + θ ^ 2) / θ ^ 3 := by positivity
  have hx := sq_nonneg x
  calc |-((1 + θ) / (2 * θ ^ 2)) + x ^ 2 * ((1 + θ + θ ^ 2) / θ ^ 3)|
      ≤ |-((1 + θ) / (2 * θ ^ 2))| + |x ^ 2 * ((1 + θ + θ ^ 2) / θ ^ 3)| := abs_add_le _ _
    _ = (1 + θ) / (2 * θ ^ 2) + x ^ 2 * ((1 + θ + θ ^ 2) / θ ^ 3) := by
        rw [abs_neg, abs_of_nonneg ha0, abs_of_nonneg (mul_nonneg hx hb0)]
    _ ≤ 5 + 38 * x ^ 2 := by nlinarith

/-- The envelope `5 + 38 x²` is integrable under `N(0, 1)`. -/
theorem integrable_envelope_pV :
    Integrable (fun x : ℝ => 5 + 38 * x ^ 2) (lawOf (gaussianReal 0 1) pV 1) := by
  have hi2 := memLp_sq_gaussianReal.integrable (by norm_num)
  rw [lawOf_pV]; exact (integrable_const _).add (hi2.const_mul _)

/-- At `θ = 0` the score `(x² - t)/(2t²)` is unbounded, so it is not differentiable there. -/
theorem not_differentiableAt_score_pV_zero (x : ℝ) :
    ¬ DifferentiableAt ℝ (fun t => score pV t x) 0 := by
  intro hd
  have hc : Tendsto (fun t => score pV t x) (𝓝[≠] 0) (𝓝 (score pV 0 x)) :=
    hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  have hx : x ^ 2 = 0 := by
    have h1 : Tendsto (fun t : ℝ => 2 * t ^ 2 * score pV t x + t) (𝓝[≠] 0) (𝓝 0) := by
      simpa using (((ht0.pow 2).const_mul 2).mul hc).add ht0
    have h2 : (fun t : ℝ => 2 * t ^ 2 * score pV t x + t) =ᶠ[𝓝[≠] 0] fun _ => x ^ 2 := by
      filter_upwards [hev] with t ht
      rw [score_pV ht]; field_simp; ring
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' h2.symm) h1
  have h1 : Tendsto (fun t : ℝ => 2 * t * score pV t x) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (ht0.const_mul 2).mul hc
  have h2 : (fun t : ℝ => 2 * t * score pV t x) =ᶠ[𝓝[≠] 0] fun _ => -1 := by
    filter_upwards [hev] with t ht
    rw [score_pV ht, hx]; field_simp; ring
  have := tendsto_nhds_unique (tendsto_const_nhds.congr' h2.symm) h1
  norm_num at this

/-- Hence the junk value of the score derivative at `θ = 0` is `0`. -/
theorem fderiv_score_pV_zero (x : ℝ) : fderiv ℝ (fun t => score pV t x) 0 = 0 :=
  fderiv_zero_of_not_differentiableAt (not_differentiableAt_score_pV_zero x)

/-- The score derivative is jointly measurable in `(θ, x)`. -/
theorem measurable_fderiv_score_pV :
    Measurable fun q : ℝ × ℝ => fderiv ℝ (fun t => score pV t q.2) q.1 := by
  have e : (fun q : ℝ × ℝ => fderiv ℝ (fun t => score pV t q.2) q.1) = fun q =>
      if q.1 = 0 then 0 else (1 / (2 * q.1 ^ 2) - q.2 ^ 2 / q.1 ^ 3) • (1 : ℝ →L[ℝ] ℝ) := by
    funext q
    split_ifs with h
    · rw [h, fderiv_score_pV_zero]
    · exact fderiv_score_pV h q.2
  rw [e]
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const ?_
  exact Measurable.smul_const (by fun_prop) _


/-- The i.i.d. sample space: coordinates of the infinite product of `N(0, 1)`. -/
noncomputable def sampleV : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1

/-- The sample law is a probability measure. -/
instance : IsProbabilityMeasure sampleV := by unfold sampleV; infer_instance

/-- Each coordinate has the data law `pV 1 · N(0, 1) = N(0, 1)`. -/
theorem hasLaw_coordV (i : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω i) (lawOf (gaussianReal 0 1) pV 1) sampleV := by
  rw [lawOf_pV]
  exact ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

/-- The coordinates are independent. -/
theorem iIndepFun_coordV : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) sampleV :=
  iIndepFun_infinitePi (P := fun _ => gaussianReal 0 1) (X := fun _ => id) (fun _ => measurable_id)

/-- The maximum-likelihood estimator of the variance: `θ̂ₙ = n⁻¹ ∑_{i<n} Xᵢ²`. -/
noncomputable def varHat (n : ℕ) (ω : ℕ → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ω i ^ 2

/-- `θ̂ₙ` is measurable. -/
theorem measurable_varHat (n : ℕ) : Measurable (varHat n) :=
  (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2).const_mul _

/-- **Consistency of the MLE** (strong law): `θ̂ₙ → 1` in probability. -/
theorem tendstoInMeasure_varHat : TendstoInMeasure sampleV varHat atTop (fun _ => 1) := by
  refine tendstoInMeasure_of_tendsto_ae (fun n => (measurable_varHat n).aestronglyMeasurable) ?_
  have hpow : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have h := strong_law_ae (μ := sampleV) (fun i (ω : ℕ → ℝ) => ω i ^ 2)
    ((hasLaw_coordV 0).integrable_comp (f := fun x => x ^ 2) (by
      rw [lawOf_pV]; exact memLp_sq_gaussianReal.integrable (by norm_num)))
    (fun i j hij => (iIndepFun_coordV.indepFun hij).comp hpow hpow)
    (fun i => (⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      ((hasLaw_coordV i).map_eq.trans (hasLaw_coordV 0).map_eq.symm)⟩ :
        IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω => ω 0) sampleV sampleV).comp hpow)
  have h0 : ∫ ω, ω 0 ^ 2 ∂sampleV = 1 := by
    have := (hasLaw_coordV 0).integral_comp (f := fun x : ℝ => x ^ 2)
      hpow.aestronglyMeasurable
    simp only [Function.comp_def, lawOf_pV] at this
    rw [this, MathlibExtTest.Probability.Statistics.VectorInference.integral_sq_gaussianReal]
  rw [h0] at h
  simpa only [varHat, smul_eq_mul] using h

/-- The likelihood equation `∑ score pV θ Xᵢ = 0` holds at `θ̂ₙ` whenever `θ̂ₙ ≠ 0`. -/
theorem sum_score_varHat (n : ℕ) (ω : ℕ → ℝ) (h : varHat n ω ≠ 0) :
    ∑ i ∈ Finset.range n, score pV (varHat n ω) (ω i) = 0 := by
  simp_rw [score_pV h]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_div]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hS : ∑ i ∈ Finset.range n, ω i ^ 2 = n * varHat n ω := by
    simp only [varHat]; field_simp
  rw [hS, nsmul_eq_mul]
  field_simp
  ring

/-- **`hroot` for the variance family**: the likelihood equation fails at `θ̂ₙ` only on
`{θ̂ₙ = 0} ⊆ {|θ̂ₙ - 1| ≥ 1}`, whose probability tends to `0` by consistency. -/
theorem tendsto_rootV :
    Tendsto (fun n => sampleV {ω | ∑ i ∈ Finset.range n, score pV (varHat n ω) (ω i) ≠ 0})
      atTop (𝓝 0) := by
  have h := (tendstoInMeasure_iff_dist.1 tendstoInMeasure_varHat) 1 one_pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hlt
  have h0 : varHat n ω ≠ 0 := by
    intro h0; rw [h0, Real.dist_eq] at hlt; norm_num at hlt
  exact hω (sum_score_varHat n ω h0)


/-- `Ĵₙ(1) = (n⁻¹ ∑ xᵢ² - 1/2) · Id` for `n ≥ 1`. -/
theorem observedInformation_pV_one {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) :
    observedInformation pV n x 1 =
      ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i ^ 2 - 1 / 2) • (1 : ℝ →L[ℝ] ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [observedInformation, fderiv_score_pV_one, ← Finset.sum_smul, smul_smul, ← neg_smul]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- At the estimator, `Ĵₙ(θ̂ₙ) = (2 θ̂ₙ²)⁻¹ · Id` whenever `θ̂ₙ ≠ 0`. -/
theorem observedInformation_pV_varHat {n : ℕ} (ω : ℕ → ℝ) (h : varHat n ω ≠ 0) :
    observedInformation pV n (fun i => ω i) (varHat n ω) =
      (1 / (2 * varHat n ω ^ 2)) • (1 : ℝ →L[ℝ] ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [varHat] at h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [observedInformation, fderiv_score_pV h, ← Finset.sum_smul, smul_smul, ← neg_smul]
  congr 1
  have hS : ∑ i ∈ Finset.range n, ω i ^ 2 = n * varHat n ω := by
    simp only [varHat]; field_simp
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_div, hS]
  field_simp
  ring

/-! ### Discharging the estimated-information theorems -/

/-- Observed information at the null is consistent: `Ĵₙ(1) → I(1) = Id/2`. -/
theorem tendstoInMeasure_observedInformation_pV_one :
    TendstoInMeasure sampleV (fun n (ω : ℕ → ℝ) => observedInformation pV n (fun i => ω i) 1)
      atTop (fun _ => fisherInformation (gaussianReal 0 1) pV 1) :=
  haveI := isProbabilityMeasure_lawOf_pV
  tendstoInMeasure_observedInformation hasLaw_coordV iIndepFun_coordV
    stronglyMeasurable_fderiv_score_pV integrable_fderiv_score_pV integral_fderiv_score_pV

/-- Observed information at the MLE is consistent: `Ĵₙ(θ̂ₙ) → I(1)`. -/
theorem tendstoInMeasure_observedInformation_pV_varHat :
    TendstoInMeasure sampleV
      (fun n (ω : ℕ → ℝ) => observedInformation pV n (fun i => ω i) (varHat n ω))
      atTop (fun _ => fisherInformation (gaussianReal 0 1) pV 1) :=
  haveI := isProbabilityMeasure_lawOf_pV
  tendstoInMeasure_observedInformation_of_tendstoInMeasure (by norm_num : (0 : ℝ) < 1 / 2)
    hasLaw_coordV iIndepFun_coordV (by fun_prop) integrable_envelope_pV
    norm_fderiv_score_pV_sub_le stronglyMeasurable_fderiv_score_pV integrable_fderiv_score_pV
    integral_fderiv_score_pV (fun n => (measurable_varHat n).aemeasurable) tendstoInMeasure_varHat

/-- Wald with `Ĵₙ(θ̂ₙ)`: `n Ĵₙ(θ̂ₙ) (θ̂ₙ - 1)² → χ²₁`. -/
theorem tendstoInDistribution_wald_pV :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → ℝ) => n * ⟪observedInformation pV n (fun i => ω i) (varHat n ω)
        (varHat n ω - 1), varHat n ω - 1⟫) atTop id (fun _ => sampleV)
      (chiSquareMeasure (Module.finrank ℝ ℝ)) :=
  haveI := isProbabilityMeasure_lawOf_pV
  tendstoInDistribution_waldStatistic_observedInformation (by norm_num : (0 : ℝ) < 1 / 2)
    hasLaw_coordV iIndepFun_coordV (fun x θ hθ => differentiableAt_score_pV
      (ne_zero_of_mem_ball hθ) x) (by fun_prop) integrable_envelope_pV
    norm_fderiv_score_pV_sub_le measurable_score_pV integrable_sq_norm_score_pV
    integral_score_pV measurable_fderiv_score_pV integrable_fderiv_score_pV
    integral_fderiv_score_pV fisherInformation_pV_pos Module.finrank_pos
    (fun n => (measurable_varHat n).aemeasurable) tendsto_rootV tendstoInMeasure_varHat HasLaw.id

/-- Rao with `Ĵₙ(1)`: `Ĵₙ(1)⁻¹ Sₙ² → χ²₁`. -/
theorem tendstoInDistribution_score_pV :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → ℝ) =>
        ⟪Ring.inverse (observedInformation pV n (fun i => ω i) 1)
            ((√n)⁻¹ • ∑ i ∈ Finset.range n, score pV 1 (ω i)),
          (√n)⁻¹ • ∑ i ∈ Finset.range n, score pV 1 (ω i)⟫)
      atTop id (fun _ => sampleV) (chiSquareMeasure (Module.finrank ℝ ℝ)) :=
  haveI := isProbabilityMeasure_lawOf_pV
  tendstoInDistribution_scoreStatistic_observedInformation hasLaw_coordV iIndepFun_coordV
    measurable_score_pV integrable_sq_norm_score_pV integral_score_pV
    stronglyMeasurable_fderiv_score_pV integrable_fderiv_score_pV integral_fderiv_score_pV
    fisherInformation_pV_pos Module.finrank_pos HasLaw.id

/-- Likelihood ratio minus Wald with `Ĵₙ(θ̂ₙ)` tends to `0` in probability. -/
theorem tendstoInMeasure_wilks_sub_wald_pV :
    TendstoInMeasure sampleV
      (fun (n : ℕ) (ω : ℕ → ℝ) => 2 * ∑ i ∈ Finset.range n,
          (Real.log (pV (varHat n ω) (ω i)) - Real.log (pV 1 (ω i))) -
        n * ⟪observedInformation pV n (fun i => ω i) (varHat n ω) (varHat n ω - 1),
          varHat n ω - 1⟫)
      atTop 0 :=
  haveI := isProbabilityMeasure_lawOf_pV
  tendstoInMeasure_two_mul_logLikelihood_sub_sub_of_estimator (by norm_num : (0 : ℝ) < 1 / 2)
    hasLaw_coordV iIndepFun_coordV
    (fun x θ hθ => differentiableAt_log_pV (ne_zero_of_mem_ball hθ) x)
    (fun x θ hθ => differentiableAt_score_pV (ne_zero_of_mem_ball hθ) x) (by fun_prop)
    integrable_envelope_pV norm_fderiv_score_pV_sub_le measurable_score_pV
    integrable_sq_norm_score_pV integral_score_pV stronglyMeasurable_fderiv_score_pV
    integrable_fderiv_score_pV integral_fderiv_score_pV
    (isUnit_of_inner_self_pos fisherInformation_pV_pos)
    (fun n => (measurable_varHat n).aemeasurable) tendsto_rootV tendstoInMeasure_varHat
    (fun n => aemeasurable_observedInformation_comp measurable_fderiv_score_pV
      (fun i => (measurable_pi_apply i).aemeasurable) (measurable_varHat n).aemeasurable n)
    tendstoInMeasure_observedInformation_pV_varHat


/-! ### `Ĵₙ` is genuinely random -/

/-- Each nondegenerate interval has positive `N(0, 1)` probability. -/
theorem gaussianReal_Ioo_pos {a b : ℝ} (hab : a < b) : 0 < gaussianReal 0 1 (Set.Ioo a b) := by
  refine pos_iff_ne_zero.2 fun h => ?_
  have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
  rw [Real.volume_Ioo] at this
  exact (ENNReal.ofReal_eq_zero.1 this).not_gt (sub_pos.2 hab)

/-- The cylinder `{ω | ∀ i < n, ω i ∈ (a, b)}` has positive probability. -/
theorem sampleV_pi_Ioo_pos (n : ℕ) {a b : ℝ} (hab : a < b) :
    0 < sampleV (Set.pi (Finset.range n : Set ℕ) fun _ => Set.Ioo a b) := by
  rw [sampleV, Measure.infinitePi_pi (μ := fun _ => gaussianReal 0 1) (s := Finset.range n)
    (t := fun _ => Set.Ioo a b) fun _ _ => measurableSet_Ioo]
  exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => (gaussianReal_Ioo_pos hab).ne')

/-- On the cylinder with `0 ≤ a`, `a² < θ̂ₙ < b²`. -/
theorem varHat_mem_of_mem_pi {n : ℕ} (hn : 0 < n) {a b : ℝ} (ha : 0 ≤ a) {ω : ℕ → ℝ}
    (hω : ω ∈ Set.pi (Finset.range n : Set ℕ) fun _ => Set.Ioo a b) :
    a ^ 2 < varHat n ω ∧ varHat n ω < b ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (Finset.range n).Nonempty := Finset.nonempty_range_iff.2 hn.ne'
  have hlo : ∑ i ∈ Finset.range n, a ^ 2 < ∑ i ∈ Finset.range n, ω i ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hne fun i hi => by
      have := hω i (by simpa using hi)
      exact pow_lt_pow_left₀ this.1 ha two_ne_zero
  have hhi : ∑ i ∈ Finset.range n, ω i ^ 2 < ∑ i ∈ Finset.range n, b ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hne fun i hi => by
      have := hω i (by simpa using hi)
      exact pow_lt_pow_left₀ this.2 (ha.trans this.1.le) two_ne_zero
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlo hhi
  constructor
  · rw [varHat, lt_inv_mul_iff₀ hn0]; exact hlo
  · rw [varHat, inv_mul_lt_iff₀ hn0]; exact hhi

/-- **`Ĵₙ(θ̂ₙ)` is genuinely random**: for every `n ≥ 1` it is `< 1/32` with positive
probability and `> 1/2` with positive probability (applied to the unit vector `1`). -/
theorem observedInformation_varHat_random {n : ℕ} (hn : 0 < n) :
    0 < sampleV {ω | observedInformation pV n (fun i => ω i) (varHat n ω) 1 < 1 / 32} ∧
      0 < sampleV {ω | 1 / 2 < observedInformation pV n (fun i => ω i) (varHat n ω) 1} := by
  constructor
  · refine (sampleV_pi_Ioo_pos n (by norm_num : (2 : ℝ) < 3)).trans_le (measure_mono ?_)
    intro ω hω
    obtain ⟨h1, -⟩ := varHat_mem_of_mem_pi hn (by norm_num) hω
    have hv : varHat n ω ≠ 0 := by positivity
    simp only [Set.mem_ofPred_eq, observedInformation_pV_varHat ω hv, FunLike.coe_smul,
      Pi.smul_apply, one_apply_eq_self, smul_eq_mul, mul_one]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · refine (sampleV_pi_Ioo_pos n (by norm_num : (1 / 2 : ℝ) < 1)).trans_le (measure_mono ?_)
    intro ω hω
    obtain ⟨h1, h2⟩ := varHat_mem_of_mem_pi hn (by norm_num) hω
    have hv : varHat n ω ≠ 0 := by positivity
    simp only [Set.mem_ofPred_eq, observedInformation_pV_varHat ω hv, FunLike.coe_smul,
      Pi.smul_apply, one_apply_eq_self, smul_eq_mul, mul_one]
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith

/-- **`Ĵₙ(1)` is genuinely random**: for every `n ≥ 1` it is `< 1/2` with positive probability
and `> 7/2` with positive probability. -/
theorem observedInformation_one_random {n : ℕ} (hn : 0 < n) :
    0 < sampleV {ω | observedInformation pV n (fun i => ω i) 1 1 < 1 / 2} ∧
      0 < sampleV {ω | 7 / 2 < observedInformation pV n (fun i => ω i) 1 1} := by
  have e : ∀ ω : ℕ → ℝ, observedInformation pV n (fun i => ω i) 1 1 = varHat n ω - 1 / 2 :=
    fun ω => by
      rw [observedInformation_pV_one hn]
      simp [varHat]
  simp only [e]
  constructor
  · refine (sampleV_pi_Ioo_pos n (by norm_num : (1 / 2 : ℝ) < 1)).trans_le (measure_mono ?_)
    intro ω hω
    obtain ⟨-, h2⟩ := varHat_mem_of_mem_pi hn (by norm_num) hω
    simp only [Set.mem_ofPred_eq]; linarith
  · refine (sampleV_pi_Ioo_pos n (by norm_num : (2 : ℝ) < 3)).trans_le (measure_mono ?_)
    intro ω hω
    obtain ⟨h1, -⟩ := varHat_mem_of_mem_pi hn (by norm_num) hω
    simp only [Set.mem_ofPred_eq]; linarith

/-- Consequently `Ĵₙ(θ̂ₙ)` is not almost surely equal to any fixed operator. -/
theorem not_ae_const_observedInformation_varHat {n : ℕ} (hn : 0 < n) (A : ℝ →L[ℝ] ℝ) :
    ¬ ∀ᵐ ω ∂sampleV, observedInformation pV n (fun i => ω i) (varHat n ω) = A := by
  intro h
  obtain ⟨h1, h2⟩ := observedInformation_varHat_random hn
  rcases lt_or_ge (A 1) (1 / 2) with hA | hA
  · refine h2.ne' (measure_mono_null (fun ω hω => ?_) (ae_iff.1 h))
    simp only [Set.mem_ofPred_eq] at hω ⊢
    intro he; rw [he] at hω; linarith
  · refine h1.ne' (measure_mono_null (fun ω hω => ?_) (ae_iff.1 h))
    simp only [Set.mem_ofPred_eq] at hω ⊢
    intro he; rw [he] at hω; linarith


/-- The density is jointly measurable. -/
theorem measurable_uncurry_pV : Measurable (Function.uncurry pV) := by
  unfold Function.uncurry pV ellV; fun_prop

/-- Wilks: `2 (ℓₙ(θ̂ₙ) - ℓₙ(1)) → χ²₁`. -/
theorem tendstoInDistribution_wilks_pV :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → ℝ) => 2 * ∑ i ∈ Finset.range n,
        (Real.log (pV (varHat n ω) (ω i)) - Real.log (pV 1 (ω i))))
      atTop id (fun _ => sampleV) (chiSquareMeasure (Module.finrank ℝ ℝ)) :=
  haveI := isProbabilityMeasure_lawOf_pV
  tendstoInDistribution_two_mul_logLikelihood_sub (by norm_num : (0 : ℝ) < 1 / 2)
    measurable_uncurry_pV hasLaw_coordV iIndepFun_coordV
    (fun x θ hθ => differentiableAt_log_pV (ne_zero_of_mem_ball hθ) x)
    (fun x θ hθ => differentiableAt_score_pV (ne_zero_of_mem_ball hθ) x) (by fun_prop)
    integrable_envelope_pV norm_fderiv_score_pV_sub_le measurable_score_pV
    integrable_sq_norm_score_pV integral_score_pV stronglyMeasurable_fderiv_score_pV
    integrable_fderiv_score_pV integral_fderiv_score_pV fisherInformation_pV_pos
    Module.finrank_pos (fun n => (measurable_varHat n).aemeasurable) tendsto_rootV
    tendstoInMeasure_varHat HasLaw.id

/-- Fidelity: for `θ > 0`, `pV θ` is the density of `N(0, θ)` with respect to `N(0, 1)`. -/
theorem gaussianPDFReal_mul_pV {θ : ℝ} (hθ : 0 < θ) (x : ℝ) :
    gaussianPDFReal 0 1 x * pV θ x = gaussianPDFReal 0 θ.toNNReal x := by
  have hs : Real.exp (-Real.log θ / 2) = (√θ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hθ, ← Real.exp_neg]; ring_nf
  simp only [gaussianPDFReal, NNReal.coe_one, Real.coe_toNNReal _ hθ.le, mul_one, sub_zero, pV,
    ellV]
  rw [show -Real.log θ / 2 - x ^ 2 / (2 * θ) + x ^ 2 / 2 =
      -Real.log θ / 2 + (-x ^ 2 / (2 * θ) + x ^ 2 / 2) by ring, Real.exp_add, hs,
    Real.sqrt_mul (by positivity) θ, mul_inv]
  have e : Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / (2 * θ) + x ^ 2 / 2) =
      Real.exp (-x ^ 2 / (2 * θ)) := by rw [← Real.exp_add]; ring_nf
  calc (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
        ((√θ)⁻¹ * Real.exp (-x ^ 2 / (2 * θ) + x ^ 2 / 2))
      = (√(2 * Real.pi))⁻¹ * (√θ)⁻¹ *
          (Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / (2 * θ) + x ^ 2 / 2)) := by ring
    _ = _ := by rw [e]

/-- **Definition fidelity**: for `θ > 0` the law with density `pV θ` with respect to
`N(0, 1)` is `N(0, θ)`. -/
theorem lawOf_pV_eq {θ : ℝ} (hθ : 0 < θ) :
    lawOf (gaussianReal 0 1) pV θ = gaussianReal 0 θ.toNNReal := by
  have hθ' : θ.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hθ).ne'
  rw [lawOf, gaussianReal_of_var_ne_zero 0 one_ne_zero, gaussianReal_of_var_ne_zero 0 hθ',
    ← withDensity_mul _ (measurable_gaussianPDF 0 1)
      (by unfold pV ellV; fun_prop : Measurable fun x => ENNReal.ofReal (pV θ x))]
  congr 1
  funext x
  show gaussianPDF 0 1 x * ENNReal.ofReal (pV θ x) = gaussianPDF 0 θ.toNNReal x
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    gaussianPDFReal_mul_pV hθ]


/-- The likelihood equation has the root `θ̂ₙ` almost surely for every `n ≥ 1`: `θ̂ₙ = 0` forces
`X₀ = 0`, a null event. -/
theorem ae_sum_score_varHat_eq_zero {n : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂sampleV, ∑ i ∈ Finset.range n, score pV (varHat n ω) (ω i) = 0 := by
  have h0 : sampleV {ω : ℕ → ℝ | ω 0 = 0} = 0 := by
    have hm := (hasLaw_coordV 0).map_eq
    rw [lawOf_pV] at hm
    have : {ω : ℕ → ℝ | ω 0 = 0} = (fun ω : ℕ → ℝ => ω 0) ⁻¹' {0} := rfl
    rw [this, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton 0), hm]
    exact gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  refine sum_score_varHat n ω (ne_of_gt ?_)
  have hω' : ω 0 ≠ 0 := hω
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : ω 0 ^ 2 ≤ ∑ i ∈ Finset.range n, ω i ^ 2 :=
    Finset.single_le_sum (f := fun i => ω i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_range.2 hn)
  exact mul_pos (inv_pos.2 hn0) ((sq_pos_of_ne_zero hω').trans_le hle)

end VarianceFamily

end MathlibExtTest.Probability.Statistics.EstimatedInformation
