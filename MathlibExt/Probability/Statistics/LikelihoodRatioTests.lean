/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MLEAsymptoticNormality
public import MathlibExt.Probability.Distributions.ChiSquare
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.StrongLaw

/-!
# Score, Wald and likelihood-ratio tests: the chi-square limit

Let `X 0, X 1, …` be i.i.d. with density `p θ₀` with respect to `ν`, a positive one-parameter
family with Fisher information `0 < I(θ₀) < ∞`. For the simple null hypothesis `θ = θ₀` the
three classical large-sample test statistics are

* Rao's **score statistic** `Sₙ² / I(θ₀)`, `Sₙ = n^{-1/2} ∑_{i<n} ∂_θ log p θ₀ (X i)`;
* Wald's statistic `n (θ̂ₙ - θ₀)² I(θ₀)` for a consistent root `θ̂ₙ` of the likelihood equation;
* Wilks' **likelihood-ratio statistic** `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀))`,
  `ℓₙ θ = ∑_{i<n} log p θ (X i)`.

Under the null each converges in distribution to the chi-square law with one degree of
freedom, also when `I(θ₀)` is replaced by any estimator converging to it in probability (for
example the observed information). The chi-square limit comes from the measure identity
`law(Z²) = χ²₁` for a standard normal `Z`, proved here by analytic continuation of the complex
moment-generating functions from the real ones and uniqueness of characteristic functions.
For the one-sided parameter space `θ ∈ [0, ∞)` with `θ₀ = 0` on its boundary, the statistic of
the estimator projected onto `[0, ∞)` has the limit law `½ δ₀ + ½ χ²₁` (the law of
`max(Z, 0)²`), as in Chernoff (1954).

The regularity conditions are those of
`MLEAsymptoticNormality.tendstoInDistribution_sqrt_mul_sub_of_likelihoodEquation` (Cramér's
conditions: on a ball about `θ₀` the log-likelihood is three times differentiable in `θ` and
its third derivative has an integrable envelope). Only a one-dimensional parameter and a simple
null hypothesis are covered; composite hypotheses with `r` restrictions (limit `χ²_r`) are not.
The local power under contiguous alternatives is in `LikelihoodRatioLocalPower`. The
likelihood-ratio results are stated for consistent roots of the likelihood equation; when the
root maximizes the likelihood the statistic is the supremum form `2 (sup_θ ℓₙ θ - ℓₙ θ₀)`
(`tendstoInDistribution_two_mul_iSup_logLikelihood_sub`).

## Main results

* `ProbabilityTheory.gaussianReal_map_sq`: `(N(0, 1)).map (x ↦ x²) = χ²₁`.
* `ProbabilityTheory.gaussianReal_map_sq_div`: `(N(0, v)).map (x ↦ x² / v) = χ²₁` for `v ≠ 0`.
* `ProbabilityTheory.gaussianReal_map_max_zero_sq`:
  `(N(0, 1)).map (x ↦ max x 0 ²) = ½ δ₀ + ½ χ²₁`.
* `tendstoInDistribution_scoreStatistic`, `tendstoInDistribution_scoreStatistic_of_estimator`:
  Rao's score test.
* `tendstoInDistribution_waldStatistic`, `tendstoInDistribution_waldStatistic_of_estimator`:
  Wald's test.
* `tendstoInMeasure_observedInformation`: the observed information `-ℓₙ''(θ₀) / n` is a
  consistent estimator of `I(θ₀)`.
* `tendstoInMeasure_two_mul_logLikelihood_sub_sub`: the quadratic expansion
  `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) = n (θ̂ₙ - θ₀)² I(θ₀) + o_P(1)`.
* `tendstoInDistribution_two_mul_logLikelihood_sub`: Wilks' theorem for a simple null.
* `tendstoInDistribution_two_mul_logLikelihood_max_zero_sub`: the boundary case
  `θ ∈ [0, ∞)`, `θ₀ = 0`, with limit `½ δ₀ + ½ χ²₁`.

## References

* S. S. Wilks, "The large-sample distribution of the likelihood ratio for testing composite
  hypotheses", Ann. Math. Statist. 9 (1938) 60–62.
* A. Wald, "Tests of statistical hypotheses concerning several parameters when the number of
  observations is large", Trans. Amer. Math. Soc. 54 (1943) 426–482.
* C. R. Rao, "Large sample tests of statistical hypotheses concerning several parameters with
  applications to problems of estimation", Proc. Cambridge Philos. Soc. 44 (1948) 50–57.
* H. Chernoff, "On the distribution of the likelihood ratio", Ann. Math. Statist. 25 (1954)
  573–578.
* E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed. (1998), §6.3
  (asymptotic normality of consistent roots of the likelihood equation, used here).
* A. W. van der Vaart, *Asymptotic Statistics* (1998), ch. 16.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- **The square of a standard normal variable is chi-square with one degree of freedom**, as
an identity of measures on `ℝ`. -/
theorem gaussianReal_map_sq :
    (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) = chiSquareMeasure 1 := by
  set μ := (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) with hμ
  have : IsProbabilityMeasure (chiSquareMeasure 1) := isProbabilityMeasure_chiSquareMeasure one_pos
  set S : Set ℂ := {z | z.re ∈ Set.Ioo (-(1 / 4 : ℝ)) (1 / 4)} with hS
  have h1 : Set.Ioo (-(1 / 4 : ℝ)) (1 / 4) ⊆ interior (integrableExpSet id μ) :=
    Ioo_subset_interior_integrableExpSet_map_sq_stdGaussian (by norm_num) (by norm_num)
  have h2 : Set.Ioo (-(1 / 4 : ℝ)) (1 / 4) ⊆
      interior (integrableExpSet id (chiSquareMeasure 1)) :=
    Ioo_subset_interior_integrableExpSet_chiSquareMeasure one_pos (by norm_num) (by norm_num)
  have hF : AnalyticOnNhd ℂ (complexMGF id μ) S :=
    analyticOnNhd_complexMGF.mono fun z hz => h1 hz
  have hG : AnalyticOnNhd ℂ (complexMGF id (chiSquareMeasure 1)) S :=
    analyticOnNhd_complexMGF.mono fun z hz => h2 hz
  have hconv : Convex ℝ S := (convex_Ioo _ _).linear_preimage Complex.reLm
  -- the two complex MGFs agree on the strip, by analytic continuation from the reals
  have heq : Set.EqOn (complexMGF id μ) (complexMGF id (chiSquareMeasure 1)) S := by
    refine hF.eqOn_of_preconnected_of_frequently_eq hG hconv.isPreconnected (z₀ := 0)
      (by simp [hS]) ?_
    have h_real : ∃ᶠ (x : ℝ) in 𝓝[≠] (0 : ℝ),
        complexMGF id μ x = complexMGF id (chiSquareMeasure 1) x := by
      have hev : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x < 1 / 2 :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
      refine (hev.mono fun x hx => ?_).frequently
      rw [complexMGF_ofReal, complexMGF_ofReal, hμ, mgf_id_map_sq_stdGaussian,
        ← mgf_gammaMeasure_half_half_eq_sqrt hx, chiSquareMeasure]
      norm_num
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n => xs n, ?_, fun n => ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · rw [Complex.ofReal_zero.symm, Filter.tendsto_ofReal_iff]
        exact hx_tendsto.1
      · simpa using hx_tendsto.2
    · exact hx_eq n
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact heq (by simp [hS])

/-- A centered Gaussian is the image of the standard one under `x ↦ √v x`. -/
private theorem gaussianReal_zero_eq_map_mul (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x : ℝ => √(v : ℝ) * x) := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  ext
  simp

/-- If `Y ~ N(0, v)` with `v ≠ 0`, then `Y² / v ~ χ²₁`. -/
theorem gaussianReal_map_sq_div {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).map (fun x : ℝ => x ^ 2 / v) = chiSquareMeasure 1 := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  rw [gaussianReal_zero_eq_map_mul v, Measure.map_map (by fun_prop) (by fun_prop),
    ← gaussianReal_map_sq]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg v)]
  field_simp

/-- Reflection symmetry of `N(0, 1)`: a reflection-invariant event has half of its mass on
`(0, ∞)`. -/
private theorem two_mul_gaussianReal_inter_Ioi {A : Set ℝ} (hA : MeasurableSet A)
    (hsym : ∀ x, -x ∈ A ↔ x ∈ A) :
    2 * gaussianReal 0 1 (A ∩ Set.Ioi 0) = gaussianReal 0 1 A := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := 0) (v := 1)
  have hIio : gaussianReal 0 1 (A ∩ Set.Iio 0) = gaussianReal 0 1 (A ∩ Set.Ioi 0) := by
    conv_rhs => rw [← hneg]
    rw [Measure.map_apply (by fun_prop) (hA.inter measurableSet_Ioi)]
    congr 1
    ext x
    simp [hsym]
  have hIci : gaussianReal 0 1 (A ∩ Set.Ici 0) = gaussianReal 0 1 (A ∩ Set.Ioi 0) :=
    measure_congr (EventuallyEqSet.inter (ae_eq_refl A) (Ioi_ae_eq_Ici' (measure_singleton 0)).symm)
  rw [← measure_inter_add_sdiff A measurableSet_Iio, Set.sdiff_eq, Set.compl_Iio, hIio, hIci,
    two_mul]

/-- **Law of the positive part squared of a standard normal variable**: `max(Z, 0)²` has the
mixture law `½ δ₀ + ½ χ²₁` (chi-bar-square with weights `½, ½`). -/
theorem gaussianReal_map_max_zero_sq :
    (gaussianReal 0 1).map (fun x : ℝ => max x 0 ^ 2) =
      (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • chiSquareMeasure 1 := by
  rw [← gaussianReal_map_sq]
  have hsq : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.map_apply hsq hs, smul_eq_mul, smul_eq_mul]
  have hpre : (fun x : ℝ => max x 0 ^ 2) ⁻¹' s =
      (Set.Iic 0 ∩ {_x | (0 : ℝ) ∈ s}) ∪ ((fun x : ℝ => x ^ 2) ⁻¹' s ∩ Set.Ioi 0) := by
    ext x
    rcases le_or_gt x 0 with hx | hx
    · simp [hx, not_lt.2 hx]
    · simp [max_eq_left hx.le, hx, not_le.2 hx]
  have hdisj : Disjoint (Set.Iic 0 ∩ {_x | (0 : ℝ) ∈ s})
      ((fun x : ℝ => x ^ 2) ⁻¹' s ∩ Set.Ioi 0) :=
    Set.disjoint_left.2 fun x h1 h2 => absurd h2.2 (not_lt.2 h1.1)
  rw [hpre, measure_union hdisj ((hsq hs).inter measurableSet_Ioi)]
  have h2 := two_mul_gaussianReal_inter_Ioi (hsq hs) (fun x => by simp)
  have hU := two_mul_gaussianReal_inter_Ioi MeasurableSet.univ (fun x => by simp)
  rw [Set.univ_inter, measure_univ] at hU
  have hcancel : ∀ y : ℝ≥0∞, 2⁻¹ * (2 * y) = y := fun y => by
    rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hIoi : gaussianReal 0 1 (Set.Ioi 0) = 2⁻¹ := by
    rw [← hcancel (gaussianReal 0 1 (Set.Ioi 0)), hU, mul_one]
  have hIic : gaussianReal 0 1 (Set.Iic 0) = 2⁻¹ := by
    rw [← Set.compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ,
      hIoi, ENNReal.one_sub_inv_two]
  rw [← h2, hcancel]
  by_cases h0 : (0 : ℝ) ∈ s
  · simp [h0, hIic, Measure.dirac_apply' _ hs]
  · simp [h0, Measure.dirac_apply' _ hs]

end ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LikelihoodRatioTests

open MathlibExt.Probability.Statistics.FisherInformation
open MathlibExt.Probability.Statistics.MLEAsymptoticNormality

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- Convergence in distribution depends on the limit only through its law. -/
private theorem tendstoInDistribution_of_hasLaw {Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₂]
    [MeasurableSpace Ω₃] {P₂ : Measure Ω₂} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₂]
    [IsProbabilityMeasure P₃] {A : ℕ → Ω → ℝ} {Y : Ω₂ → ℝ} {Z : Ω₃ → ℝ} {ρ : Measure ℝ}
    (h : TendstoInDistribution A atTop Y (fun _ => P) P₂) (hY : HasLaw Y ρ P₂)
    (hZ : HasLaw Z ρ P₃) :
    TendstoInDistribution A atTop Z (fun _ => P) P₃ where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    convert h.tendsto using 3
    exact congrArg 𝓝 (Subtype.ext (hZ.map_eq.trans hY.map_eq.symm))

/-- `x² / I` maps `N(0, I)` to `χ²₁`. -/
private theorem hasLaw_sq_div {I : ℝ} (hI : 0 < I) :
    HasLaw (fun x : ℝ => x ^ 2 / I) (chiSquareMeasure 1) (gaussianReal 0 I.toNNReal) := by
  refine ⟨by fun_prop, ?_⟩
  have h := gaussianReal_map_sq_div (v := I.toNNReal) (by simpa using hI)
  rwa [Real.coe_toNNReal _ hI.le] at h

/-- `x² I` maps `N(0, 1 / I)` to `χ²₁`. -/
private theorem hasLaw_sq_mul {I : ℝ} (hI : 0 < I) :
    HasLaw (fun x : ℝ => x ^ 2 * I) (chiSquareMeasure 1) (gaussianReal 0 I⁻¹.toNNReal) := by
  refine ⟨by fun_prop, ?_⟩
  have h := gaussianReal_map_sq_div (v := I⁻¹.toNNReal) (by simpa using hI)
  rw [Real.coe_toNNReal _ (inv_nonneg.2 hI.le)] at h
  simpa only [div_inv_eq_mul] using h

/-- `I max(x, 0)²` maps `N(0, 1 / I)` to `½ δ₀ + ½ χ²₁`. -/
private theorem hasLaw_mul_max_zero_sq {I : ℝ} (hI : 0 < I) :
    HasLaw (fun x : ℝ => I * max x 0 ^ 2)
      ((2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • chiSquareMeasure 1)
      (gaussianReal 0 I⁻¹.toNNReal) := by
  refine ⟨by fun_prop, ?_⟩
  have hv : ((I⁻¹.toNNReal : ℝ≥0) : ℝ) = I⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 hI.le)
  rw [← gaussianReal_map_max_zero_sq, ProbabilityTheory.gaussianReal_zero_eq_map_mul,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  have hc : 0 ≤ √((I⁻¹.toNNReal : ℝ≥0) : ℝ) := Real.sqrt_nonneg _
  have hm : max (√((I⁻¹.toNNReal : ℝ≥0) : ℝ) * x) 0 = √((I⁻¹.toNNReal : ℝ≥0) : ℝ) * max x 0 := by
    rw [mul_max_of_nonneg _ _ hc, mul_zero]
  simp only [Function.comp_apply]
  rw [hm, mul_pow,
    Real.sq_sqrt (NNReal.coe_nonneg _), hv, ← mul_assoc, mul_inv_cancel₀ hI.ne', one_mul]

/-- The `√n`-scaled consistent root has the normal limit `N(0, 1 / I(θ₀))`, realized by the
identity on `(ℝ, N(0, 1 / I(θ₀)))`. -/
private theorem tendstoInDistribution_sqrt_mul_sub_aux
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ)
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : Measurable (p θ₀))
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀)) :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (θhat n ω - θ₀)) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 (fisherInformation ν p θ₀)⁻¹.toNNReal) := by
  have hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ₀ := fun x => by
    have e : (fun t => p t x) = fun t => Real.exp (Real.log (p t x)) := by
      funext t; rw [Real.exp_log (hp_pos t x)]
    rw [e]; exact (hℓ_diff x θ₀ (Metric.mem_ball_self hδ)).exp
  have hvar : (∫ x, score p θ₀ x ^ 2 ∂lawOf ν p θ₀) /
      (∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀) ^ 2 =
        (fisherInformation ν p θ₀)⁻¹ := by
    rw [integral_score_sq (hp_pos θ₀) hp_meas hp_diff, h_info, neg_sq, sq,
      div_mul_cancel_left₀ hI_pos.ne']
  refine tendstoInDistribution_sqrt_mul_sub_of_estimatingEquation hX_law hX_indep hδ hs_diff
    hs'_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int
    (by rw [h_info]; exact neg_ne_zero.2 hI_pos.ne') hθ_meas hroot hcons ?_
  rw [hvar]
  exact HasLaw.id

omit [IsProbabilityMeasure P] in
/-- Measurability of the log-likelihood ratio at a random parameter. -/
private theorem aemeasurable_logLikelihood_sub {p : ℝ → 𝓧 → ℝ} {θ₀ : ℝ}
    (hp_meas : Measurable (Function.uncurry p)) {X : ℕ → Ω → 𝓧}
    (hX : ∀ i, AEMeasurable (X i) P) {θ : Ω → ℝ} (hθ : AEMeasurable θ P) (n : ℕ) :
    AEMeasurable (fun ω => 2 * ∑ i ∈ Finset.range n,
      (Real.log (p (θ ω) (X i ω)) - Real.log (p θ₀ (X i ω)))) P := by
  have hp0 : Measurable (p θ₀) := hp_meas.comp (measurable_const.prodMk measurable_id)
  refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).const_mul 2
  exact ((Real.measurable_log.comp hp_meas).comp_aemeasurable (hθ.prodMk (hX i))).sub
    ((Real.measurable_log.comp hp0).comp_aemeasurable (hX i))

open Set in
/-- Second-order Taylor bound at the fixed point `θ₀` with a third-derivative bound `m` on a
ball: `|f θ₀ - f θ - (θ₀ - θ) f'(θ) - (θ₀ - θ)² / 2 · f''(θ₀)| ≤ m |θ - θ₀|³`. -/
private theorem abs_taylor_two_le {f f₁ f₂ f₃ : ℝ → ℝ} {θ₀ δ θ m : ℝ}
    (hf : ∀ t ∈ Metric.ball θ₀ δ, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Metric.ball θ₀ δ, HasDerivAt f₁ (f₂ t) t)
    (hf₂ : ∀ t ∈ Metric.ball θ₀ δ, HasDerivAt f₂ (f₃ t) t)
    (hm : ∀ t ∈ Metric.ball θ₀ δ, |f₃ t| ≤ m) (hθ : θ ∈ Metric.ball θ₀ δ) :
    |f θ₀ - f θ - (θ₀ - θ) * f₁ θ - (θ₀ - θ) ^ 2 / 2 * f₂ θ₀| ≤ m * |θ - θ₀| ^ 3 := by
  have h0 : θ₀ ∈ Metric.ball θ₀ δ := Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hθ)
  have hsub : uIcc θ₀ θ ⊆ Metric.ball θ₀ δ := by
    rw [Real.ball_eq_Ioo] at h0 hθ ⊢
    exact ordConnected_Ioo.uIcc_subset h0 hθ
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm θ₀ h0)
  -- the second derivative is `m`-Lipschitz on the ball
  have h2 : ∀ t ∈ uIcc θ₀ θ, |f₂ θ₀ - f₂ t| ≤ m * |θ - θ₀| := fun t ht => by
    have := (convex_ball θ₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hf₂ s hs).hasDerivWithinAt) (fun s hs => by
        rw [Real.norm_eq_abs]; exact hm s hs) (hsub ht) h0
    simp only [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by
      rw [abs_sub_comm]; exact abs_sub_left_of_mem_uIcc ht) hm0)
  set φ : ℝ → ℝ := fun t => f θ₀ - f t - (θ₀ - t) * f₁ t - (θ₀ - t) * (θ₀ - t) / 2 * f₂ θ₀
    with hφ_def
  have hφ : ∀ t ∈ uIcc θ₀ θ, HasDerivAt φ ((θ₀ - t) * (f₂ θ₀ - f₂ t)) t := fun t ht => by
    have hl : HasDerivAt (fun t : ℝ => θ₀ - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub θ₀
    have := (((hasDerivAt_const t (f θ₀)).sub (hf t (hsub ht))).sub
      (hl.mul (hf₁ t (hsub ht)))).sub (((hl.mul hl).div_const 2).mul_const (f₂ θ₀))
    convert this using 1
    ring
  have hφ' : ∀ t ∈ uIcc θ₀ θ, ‖(θ₀ - t) * (f₂ θ₀ - f₂ t)‖ ≤ m * |θ - θ₀| ^ 2 := fun t ht => by
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |θ₀ - t| ≤ |θ - θ₀| := by rw [abs_sub_comm]; exact abs_sub_left_of_mem_uIcc ht
    calc |θ₀ - t| * |f₂ θ₀ - f₂ t| ≤ |θ - θ₀| * (m * |θ - θ₀|) :=
          mul_le_mul h1 (h2 t ht) (abs_nonneg _) (abs_nonneg _)
      _ = m * |θ - θ₀| ^ 2 := by ring
  have key := (convex_uIcc θ₀ θ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hφ t ht).hasDerivWithinAt) hφ' left_mem_uIcc right_mem_uIcc
  have hφ0 : φ θ₀ = 0 := by simp [hφ_def]
  rw [hφ0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at key
  have e : f θ₀ - f θ - (θ₀ - θ) * f₁ θ - (θ₀ - θ) ^ 2 / 2 * f₂ θ₀ = φ θ := by
    simp only [hφ_def]; ring
  rw [e]
  calc |φ θ| ≤ m * |θ - θ₀| ^ 2 * |θ - θ₀| := key
    _ = m * |θ - θ₀| ^ 3 := by ring

omit [IsProbabilityMeasure P] in
/-- A sum of two sequences tending to `0` in probability tends to `0` in probability. -/
private theorem tendstoInMeasure_add_zero' {U V : ℕ → Ω → ℝ}
    (hU : TendstoInMeasure P U atTop 0) (hV : TendstoInMeasure P V atTop 0) :
    TendstoInMeasure P (fun i ω => U i ω + V i ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hU hV ⊢
  intro ε hε
  have h2 := (hU (ε / 2) (by positivity)).add (hV (ε / 2) (by positivity))
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun i => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
  linarith [abs_add_le (U i ω) (V i ω)]

/-- **Rao's score test, known information.** Under the conditions of
`tendstoInDistribution_score` and `0 < I(θ₀)`, the score statistic
`(n^{-1/2} ∑_{i<n} score p θ₀ (X i))² / I(θ₀)` converges in distribution to `χ²₁`.

Source: Rao (1948), one-parameter case; the central limit theorem for the score as in
Lehmann & Casella (1998), §6.3. -/
theorem tendstoInDistribution_scoreStatistic {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ : ℝ}
    (hp_pos : ∀ x, 0 < p θ₀ x) (hp_meas : Measurable (p θ₀))
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ₀)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => ((√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (X i ω)) ^ 2 /
        fisherInformation ν p θ₀) atTop Z (fun _ => P) P' := by
  have h := tendstoInDistribution_score
    (P' := gaussianReal 0 (fisherInformation ν p θ₀).toNNReal) hp_pos hp_meas hp_diff hX_law
    hX_indep hs_meas hs_sq hs_mean HasLaw.id
  exact tendstoInDistribution_of_hasLaw
    (h.continuous_comp (g := fun x => x ^ 2 / fisherInformation ν p θ₀) (by fun_prop))
    (hasLaw_sq_div hI_pos) hZ

/-- **Rao's score test with an estimated information.** As
`tendstoInDistribution_scoreStatistic`, with `I(θ₀)` replaced by any estimators `Î n`
converging to `I(θ₀)` in probability. Where `Î n ω = 0` the statistic takes Lean's value
`x / 0 = 0`; this event has probability tending to `0` because `0 < I(θ₀)`. -/
theorem tendstoInDistribution_scoreStatistic_of_estimator {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    {θ₀ : ℝ} (hp_pos : ∀ x, 0 < p θ₀ x) (hp_meas : Measurable (p θ₀))
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ₀)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {Ihat : ℕ → Ω → ℝ} (hIhat_meas : ∀ n, AEMeasurable (Ihat n) P)
    (hIhat : TendstoInMeasure P Ihat atTop (fun _ => fisherInformation ν p θ₀))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => ((√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (X i ω)) ^ 2 / Ihat n ω)
      atTop Z (fun _ => P) P' := by
  set I := fisherInformation ν p θ₀ with hI_def
  have hI2 : 0 < I / 2 := by positivity
  have h := tendstoInDistribution_score (P' := gaussianReal 0 I.toNNReal)
    hp_pos hp_meas hp_diff hX_law hX_indep hs_meas hs_sq hs_mean HasLaw.id
  have hg : Continuous fun z : ℝ × ℝ => z.1 ^ 2 / max z.2 (I / 2) :=
    (continuous_fst.pow 2).div (continuous_snd.max continuous_const)
      fun z => (lt_max_of_lt_right hI2).ne'
  have h2 := h.continuous_comp_prodMk_of_tendstoInMeasure_const hg hIhat hIhat_meas
  have hmax : max I (I / 2) = I := max_eq_left (by linarith)
  refine tendstoInDistribution_of_hasLaw
    (tendstoInDistribution_of_tendstoInMeasure_sub _ _ h2 ?_ fun n =>
      ((h.forall_aemeasurable n).pow_const 2).div (hIhat_meas n)) ?_ hZ
  · refine tendstoInMeasure_zero_of_abs_le (V := 0) (G := fun n => {ω | I / 2 ≤ Ihat n ω})
      ?_ ?_ ?_
    · rw [tendstoInMeasure_iff_norm]
      intro ε hε
      simp [not_le.2 hε]
    · have h1 := (tendstoInMeasure_iff_dist.1 hIhat) (I / 2) hI2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
        fun n => measure_mono fun ω hω => ?_
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
      simp only [Set.mem_ofPred_eq, Real.dist_eq]
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      linarith
    · intro n ω hω
      simp only [Set.mem_ofPred_eq] at hω
      simp [max_eq_left hω]
  · simpa only [id, hmax] using hasLaw_sq_div hI_pos

/-- **Consistency of the observed information.** For i.i.d. observations with law `p θ₀ ν`,
if `∂_θ score p θ₀` is measurable and integrable with `E ∂_θ score p θ₀ = -I(θ₀)` (the
information identity), then `-(1/n) ∑_{i<n} ∂_θ score p θ₀ (X i) → I(θ₀)` in probability. -/
theorem tendstoInMeasure_observedInformation {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ : ℝ}
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => -((∑ i ∈ Finset.range n, deriv (fun t => score p t (X i ω)) θ₀) / n))
      atTop (fun _ => fisherInformation ν p θ₀) := by
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  set g : 𝓧 → ℝ := fun x => deriv (fun t => score p t x) θ₀ with hg_def
  have hident : ∀ i, IdentDistrib (g ∘ X i) (g ∘ X 0) P P := fun i =>
    (⟨hXm i, hXm 0, (hX_law i).map_eq.trans (hX_law 0).map_eq.symm⟩ :
      IdentDistrib (X i) (X 0) P P).comp hs'_meas
  have h := strong_law_ae_real (fun i => g ∘ X i) ((hX_law 0).integrable_comp hs'_int)
    (fun i j hij => (hX_indep.comp (fun _ => g) (fun _ => hs'_meas)).indepFun hij) hident
  rw [(hX_law 0).integral_comp hs'_meas.aestronglyMeasurable, h_info] at h
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
  · exact ((Finset.aemeasurable_fun_sum _ fun i _ =>
      hs'_meas.comp_aemeasurable (hXm i)).div_const _).neg.aestronglyMeasurable
  · filter_upwards [h] with ω hω
    simpa using hω.neg

/-- **Wald's test.** Under the conditions of
`tendstoInDistribution_sqrt_mul_sub_of_likelihoodEquation` (without the normalization
`∫ p θ dν = 1`, which that proof does not use), the Wald statistic `n (θ̂ₙ - θ₀)² I(θ₀)` of a
consistent root `θ̂ₙ` of the likelihood equation converges in distribution to `χ²₁`.

Source: Wald (1943), one-parameter case; the asymptotic normality of `θ̂ₙ` as in
Lehmann & Casella (1998), §6.3. -/
theorem tendstoInDistribution_waldStatistic
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ)
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : Measurable (p θ₀))
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (n : ℝ) * (θhat n ω - θ₀) ^ 2 * fisherInformation ν p θ₀)
      atTop Z (fun _ => P) P' := by
  have h := tendstoInDistribution_sqrt_mul_sub_aux hδ hp_pos hp_meas hX_law hX_indep hℓ_diff
    hs_diff hs'_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI_pos
    hθ_meas hroot hcons
  have h2 : TendstoInDistribution
      (fun (n : ℕ) ω => (n : ℝ) * (θhat n ω - θ₀) ^ 2 * fisherInformation ν p θ₀) atTop
      (fun x : ℝ => x ^ 2 * fisherInformation ν p θ₀) (fun _ => P)
      (gaussianReal 0 (fisherInformation ν p θ₀)⁻¹.toNNReal) :=
    (h.continuous_comp (g := fun x => x ^ 2 * fisherInformation ν p θ₀) (by fun_prop)).congr
      (fun n => ae_of_all _ fun ω => by
        simp only [Function.comp_apply]
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]) (ae_of_all _ fun _ => rfl)
  exact tendstoInDistribution_of_hasLaw h2 (hasLaw_sq_mul hI_pos) hZ

/-- **Wald's test with an estimated information.** As `tendstoInDistribution_waldStatistic`,
with `I(θ₀)` replaced by any estimators `Î n → I(θ₀)` in probability (for example the observed
information of `tendstoInMeasure_observedInformation`; `I(θ̂ₙ)` also qualifies when
`θ ↦ I(θ)` is continuous at `θ₀`, by the continuous mapping theorem, not proved here). -/
theorem tendstoInDistribution_waldStatistic_of_estimator
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ)
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : Measurable (p θ₀))
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Ihat : ℕ → Ω → ℝ} (hIhat_meas : ∀ n, AEMeasurable (Ihat n) P)
    (hIhat : TendstoInMeasure P Ihat atTop (fun _ => fisherInformation ν p θ₀))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (n : ℝ) * (θhat n ω - θ₀) ^ 2 * Ihat n ω)
      atTop Z (fun _ => P) P' := by
  have h := tendstoInDistribution_sqrt_mul_sub_aux hδ hp_pos hp_meas hX_law hX_indep hℓ_diff
    hs_diff hs'_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI_pos
    hθ_meas hroot hcons
  have h2 := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : ℝ × ℝ => z.1 ^ 2 * z.2) (by fun_prop) hIhat hIhat_meas
  have h3 : TendstoInDistribution
      (fun (n : ℕ) ω => (n : ℝ) * (θhat n ω - θ₀) ^ 2 * Ihat n ω) atTop
      (fun x : ℝ => x ^ 2 * fisherInformation ν p θ₀) (fun _ => P)
      (gaussianReal 0 (fisherInformation ν p θ₀)⁻¹.toNNReal) :=
    h2.congr (fun n => ae_of_all _ fun ω => by
        simp only
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]) (ae_of_all _ fun _ => rfl)
  exact tendstoInDistribution_of_hasLaw h3 (hasLaw_sq_mul hI_pos) hZ

/-- **Quadratic expansion of the log-likelihood ratio.** Let `θ̂ₙ` be `√n`-consistent
(`√n (θ̂ₙ - θ₀)` converges in distribution) and solve the likelihood equation with probability
tending to one. If on the ball of radius `δ > 0` about `θ₀` the log-likelihood is twice
differentiable in `θ` with `|∂³_θ log p θ x| ≤ M x` for an integrable `M`, and
`∂²_θ log p θ₀` is integrable with mean `-I(θ₀)`, then
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - n (θ̂ₙ - θ₀)² I(θ₀) → 0` in probability, where
`ℓₙ θ = ∑_{i<n} log p θ (X i)`.

The positivity of `p` is not used: the expansion holds for any criterion `log p θ x` with these
derivatives, and the theorems below assume `0 < p θ x`.

Source: the second-order expansion of Wilks (1938); van der Vaart (1998), ch. 16. -/
theorem tendstoInMeasure_two_mul_logLikelihood_sub_sub
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Y : Ω' → ℝ}
    (hT : TendstoInDistribution (fun (n : ℕ) ω => √n * (θhat n ω - θ₀)) atTop Y
      (fun _ => P) P') :
    TendstoInMeasure P
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
          (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))) -
        (n : ℝ) * (θhat n ω - θ₀) ^ 2 * fisherInformation ν p θ₀)
      atTop 0 := by
  set I := fisherInformation ν p θ₀ with hI_def
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  have hθ₀ : θ₀ ∈ Metric.ball θ₀ δ := Metric.mem_ball_self hδ
  have hM0 : ∀ x, 0 ≤ M x := fun x => (abs_nonneg _).trans (hM x θ₀ hθ₀)
  set ψ' : 𝓧 → ℝ := fun x => deriv (fun t => score p t x) θ₀ with hψ'_def
  set T : ℕ → Ω → ℝ := fun n ω => √n * (θhat n ω - θ₀) with hT_def
  set B : ℕ → Ω → ℝ := fun n ω => -((∑ i ∈ Finset.range n, ψ' (X i ω)) / n) with hB_def
  set Mb : ℕ → Ω → ℝ := fun n ω => (∑ i ∈ Finset.range n, M (X i ω)) / n with hMb_def
  set η : ℕ → Ω → ℝ := fun n ω => |B n ω - I| + |θhat n ω - θ₀| * Mb n ω with hη_def
  have hMb_meas : ∀ n, AEMeasurable (Mb n) P := fun n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hM_meas.comp_aemeasurable (hXm i)).div_const _
  have hB_meas : ∀ n, AEMeasurable (B n) P := fun n =>
    ((Finset.aemeasurable_fun_sum _ fun i _ => hs'_meas.comp_aemeasurable (hXm i)).div_const
      _).neg
  have hη_meas : ∀ n, AEMeasurable (η n) P := fun n =>
    (continuous_abs.measurable.comp_aemeasurable ((hB_meas n).sub_const _)).add
      ((continuous_abs.measurable.comp_aemeasurable ((hθ_meas n).sub_const _)).mul (hMb_meas n))
  -- laws of large numbers
  have hB : TendstoInMeasure P B atTop (fun _ => I) :=
    tendstoInMeasure_observedInformation hX_law hX_indep hs'_meas hs'_int h_info
  have hMb : TendstoInMeasure P Mb atTop (fun _ => ∫ x, M x ∂lawOf ν p θ₀) := by
    have hident : ∀ i, IdentDistrib (M ∘ X i) (M ∘ X 0) P P := fun i =>
      (⟨hXm i, hXm 0, (hX_law i).map_eq.trans (hX_law 0).map_eq.symm⟩ :
        IdentDistrib (X i) (X 0) P P).comp hM_meas
    have h := strong_law_ae_real (fun i => M ∘ X i) ((hX_law 0).integrable_comp hM_int)
      (fun i j hij => (hX_indep.comp (fun _ => M) (fun _ => hM_meas)).indepFun hij) hident
    rw [(hX_law 0).integral_comp hM_meas.aestronglyMeasurable] at h
    exact tendstoInMeasure_of_tendsto_ae (fun n => (hMb_meas n).aestronglyMeasurable) h
  have hBI : TendstoInMeasure P (fun n ω => |B n ω - I|) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hB ⊢
    simpa using hB
  have hdθ : TendstoInMeasure P (fun n ω => |θhat n ω - θ₀|) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hcons ⊢
    simpa using hcons
  have hrem : TendstoInMeasure P (fun n ω => |θhat n ω - θ₀| * Mb n ω) atTop 0 := by
    have h := (hMb.tendstoInDistribution_of_aemeasurable hMb_meas aemeasurable_const
      ).mul_tendstoInMeasure_zero hdθ
      (fun n => continuous_abs.measurable.comp_aemeasurable ((hθ_meas n).sub_const _))
    simpa only [mul_comm] using h
  have hη : TendstoInMeasure P η atTop 0 := tendstoInMeasure_add_zero' hBI hrem
  -- the good events
  set G : ℕ → Set Ω := fun n => {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) = 0} ∩
    {ω | |θhat n ω - θ₀| < δ} with hG_def
  have hG : Tendsto (fun n => P (G n)ᶜ) atTop (𝓝 0) := by
    have h1 := (tendstoInMeasure_iff_dist.1 hcons) δ hδ
    have h3 := hroot.add h1
    rw [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
      fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [hG_def, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or,
      not_lt] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq]
    exact hω
  -- the deterministic bound on the good events
  have hbound : ∀ n, ∀ ω ∈ G n,
      |2 * ∑ i ∈ Finset.range n,
          (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))) -
        (n : ℝ) * (θhat n ω - θ₀) ^ 2 * I| ≤ (2 * T n ω ^ 2) * η n ω := by
    intro n ω hω
    obtain ⟨hroot', hclose⟩ := hω
    simp only [Set.mem_ofPred_eq] at hroot' hclose
    have hball : θhat n ω ∈ Metric.ball θ₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq]; exact hclose
    have hT2 : T n ω ^ 2 = n * (θhat n ω - θ₀) ^ 2 := by
      simp only [hT_def]; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hη_def, hT_def]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hSM : 0 ≤ ∑ i ∈ Finset.range n, M (X i ω) := Finset.sum_nonneg fun i _ => hM0 _
    have htay : |-(∑ i ∈ Finset.range n,
          (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω)))) -
        (θhat n ω - θ₀) ^ 2 / 2 * ∑ i ∈ Finset.range n, ψ' (X i ω)| ≤
          (∑ i ∈ Finset.range n, M (X i ω)) * |θhat n ω - θ₀| ^ 3 := by
      have e : -(∑ i ∈ Finset.range n,
          (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω)))) -
            (θhat n ω - θ₀) ^ 2 / 2 * ∑ i ∈ Finset.range n, ψ' (X i ω) =
          ∑ i ∈ Finset.range n, (Real.log (p θ₀ (X i ω)) - Real.log (p (θhat n ω) (X i ω)) -
            (θ₀ - θhat n ω) * score p (θhat n ω) (X i ω) -
              (θ₀ - θhat n ω) ^ 2 / 2 * ψ' (X i ω)) := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hroot', mul_zero]
        ring
      rw [e, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact abs_taylor_two_le (f := fun t => Real.log (p t (X i ω)))
        (f₁ := fun t => score p t (X i ω)) (f₂ := fun t => deriv (fun s => score p s (X i ω)) t)
        (f₃ := fun t => deriv (fun t => deriv (fun s => score p s (X i ω)) t) t)
        (fun t ht => (hℓ_diff _ t ht).hasDerivAt) (fun t ht => (hs_diff _ t ht).hasDerivAt)
        (fun t ht => (hs'_diff _ t ht).hasDerivAt) (fun t ht => hM _ t ht) hball
    generalize hL : ∑ i ∈ Finset.range n,
      (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))) = L at htay
    generalize hS : ∑ i ∈ Finset.range n, ψ' (X i ω) = S at htay
    generalize hSM' : ∑ i ∈ Finset.range n, M (X i ω) = SM at htay hSM
    have hB' : B n ω = -S / n := by simp only [hB_def, hS]; ring
    have hMb' : Mb n ω = SM / n := by simp only [hMb_def, hSM']
    have hη' : η n ω = |B n ω - I| + |θhat n ω - θ₀| * Mb n ω := rfl
    rw [hη', hT2, hB', hMb']
    generalize θhat n ω - θ₀ = d at htay ⊢
    have h1 : |-S / n - I| = |S + n * I| / n := by
      rw [show -S / n - I = -(S + n * I) / n by field_simp; ring, abs_div, abs_neg,
        abs_of_pos hn']
    rw [h1]
    have e2 : 2 * L - n * d ^ 2 * I = -2 * (-L - d ^ 2 / 2 * S) - d ^ 2 * (S + n * I) := by ring
    have e3 : 2 * (n * d ^ 2) * (|S + n * I| / n + |d| * (SM / n)) =
        2 * d ^ 2 * |S + n * I| + 2 * SM * (d ^ 2 * |d|) := by field_simp
    have e4 : |d| ^ 3 = d ^ 2 * |d| := by rw [pow_succ, sq_abs]
    rw [e2, e3]
    calc |-2 * (-L - d ^ 2 / 2 * S) - d ^ 2 * (S + n * I)|
        ≤ 2 * |-L - d ^ 2 / 2 * S| + d ^ 2 * |S + n * I| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_nonneg (sq_nonneg d)]
      _ ≤ 2 * (SM * |d| ^ 3) + d ^ 2 * |S + n * I| := by linarith
      _ ≤ 2 * d ^ 2 * |S + n * I| + 2 * SM * (d ^ 2 * |d|) := by
          rw [e4]; nlinarith [mul_nonneg (sq_nonneg d) (abs_nonneg (S + n * I))]
  -- `(2 T²) η → 0` in probability
  have hV : TendstoInMeasure P (fun n ω => (2 * T n ω ^ 2) * η n ω) atTop 0 :=
    (hT.continuous_comp (g := fun x => 2 * x ^ 2) (by fun_prop)).mul_tendstoInMeasure_zero hη
      hη_meas
  exact tendstoInMeasure_zero_of_abs_le hV hG hbound

/-- **Wilks' theorem (simple null).** Under the conditions of `tendstoInDistribution_waldStatistic`
and joint measurability of `(θ, x) ↦ p θ x`, the log-likelihood-ratio statistic
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀))`, `ℓₙ θ = ∑_{i<n} log p θ (X i)`, of a consistent root `θ̂ₙ` of the
likelihood equation converges in distribution to `χ²₁`.

Source: Wilks (1938), case of a one-dimensional parameter and a simple null hypothesis;
van der Vaart (1998), ch. 16. -/
theorem tendstoInDistribution_two_mul_logLikelihood_sub
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ)
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : Measurable (Function.uncurry p))
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
        (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))))
      atTop Z (fun _ => P) P' := by
  have hp0 : Measurable (p θ₀) := hp_meas.comp (measurable_const.prodMk measurable_id)
  have hW := tendstoInDistribution_waldStatistic hδ hp_pos hp0 hX_law hX_indep hℓ_diff hs_diff
    hs'_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI_pos hθ_meas
    hroot hcons hZ
  have hT := tendstoInDistribution_sqrt_mul_sub_aux hδ hp_pos hp0 hX_law hX_indep hℓ_diff
    hs_diff hs'_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI_pos
    hθ_meas hroot hcons
  have hQ := tendstoInMeasure_two_mul_logLikelihood_sub_sub hδ hX_law hX_indep hℓ_diff hs_diff
    hs'_diff hM_meas hM_int hM hs'_meas hs'_int h_info hθ_meas hroot hcons hT
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ Z hW hQ fun n =>
    aemeasurable_logLikelihood_sub hp_meas (fun i => (hX_law i).aemeasurable) (hθ_meas n) n

/-- **Wilks' theorem, supremum form.** If moreover `θ̂ₙ ω` maximizes the log-likelihood
`ℓₙ θ = ∑_{i<n} log p θ (X i ω)` over all `θ` for every `n` and `ω`, then the
likelihood-ratio statistic `2 (sup_θ ℓₙ θ - ℓₙ θ₀)` converges in distribution to `χ²₁`. -/
theorem tendstoInDistribution_two_mul_iSup_logLikelihood_sub
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ)
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : Measurable (Function.uncurry p))
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    (hmax : ∀ n ω θ, ∑ i ∈ Finset.range n, Real.log (p θ (X i ω)) ≤
      ∑ i ∈ Finset.range n, Real.log (p (θhat n ω) (X i ω)))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ((⨆ θ, ∑ i ∈ Finset.range n, Real.log (p θ (X i ω))) -
        ∑ i ∈ Finset.range n, Real.log (p θ₀ (X i ω))))
      atTop Z (fun _ => P) P' := by
  have e : ∀ n ω, (⨆ θ, ∑ i ∈ Finset.range n, Real.log (p θ (X i ω))) =
      ∑ i ∈ Finset.range n, Real.log (p (θhat n ω) (X i ω)) := fun n ω =>
    le_antisymm (ciSup_le (hmax n ω))
      (le_ciSup ⟨_, Set.forall_mem_range.2 (hmax n ω)⟩ (θhat n ω))
  have h := tendstoInDistribution_two_mul_logLikelihood_sub hδ hp_pos hp_meas hX_law hX_indep
    hℓ_diff hs_diff hs'_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info
    hI_pos hθ_meas hroot hcons hZ
  simp_rw [e, ← Finset.sum_sub_distrib]
  exact h

/-- **Likelihood ratio on the boundary** (one-sided parameter space `θ ∈ [0, ∞)`, true value
`θ₀ = 0`). Let the model be defined and regular on a ball about `0` as in
`tendstoInDistribution_two_mul_logLikelihood_sub` (so `0` is interior to the domain of the
family, though not to the parameter space), and let `θ̂ₙ` be a consistent root of the
likelihood equation. The statistic `2 (ℓₙ(max θ̂ₙ 0) - ℓₙ(0))` of the estimator projected onto
`[0, ∞)` converges in distribution to the mixture `½ δ₀ + ½ χ²₁`. The projection `max θ̂ₙ 0`
is the restricted maximizer when, for example, `ℓₙ` is concave; that is not assumed here.

Source: Chernoff (1954); van der Vaart (1998), ch. 16. -/
theorem tendstoInDistribution_two_mul_logLikelihood_max_zero_sub
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : Measurable (Function.uncurry p))
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p 0) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball 0 δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball 0 δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball 0 δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p 0))
    (hM : ∀ x, ∀ θ ∈ Metric.ball 0 δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs_meas : Measurable (score p 0))
    (hs_sq : Integrable (fun x => score p 0 x ^ 2) (lawOf ν p 0))
    (hs_mean : ∫ x, score p 0 x ∂lawOf ν p 0 = 0)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) 0)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) 0) (lawOf ν p 0))
    (h_info : ∫ x, deriv (fun t => score p t x) 0 ∂lawOf ν p 0 = -fisherInformation ν p 0)
    (hI_pos : 0 < fisherInformation ν p 0)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => 0))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z ((2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
        (Real.log (p (max (θhat n ω) 0) (X i ω)) - Real.log (p 0 (X i ω))))
      atTop Z (fun _ => P) P' := by
  have hp0 : Measurable (p 0) := hp_meas.comp (measurable_const.prodMk measurable_id)
  have hT := tendstoInDistribution_sqrt_mul_sub_aux hδ hp_pos hp0 hX_law hX_indep hℓ_diff
    hs_diff hs'_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI_pos
    hθ_meas hroot hcons
  have hQ := tendstoInMeasure_two_mul_logLikelihood_sub_sub hδ hX_law hX_indep hℓ_diff hs_diff
    hs'_diff hM_meas hM_int hM hs'_meas hs'_int h_info hθ_meas hroot hcons hT
  set I := fisherInformation ν p 0 with hI_def
  have h2 := hT.continuous_comp (g := fun x => I * max x 0 ^ 2) (by fun_prop)
  refine tendstoInDistribution_of_hasLaw
    (tendstoInDistribution_of_tendstoInMeasure_sub _ _ h2 ?_ fun n =>
      aemeasurable_logLikelihood_sub hp_meas (fun i => (hX_law i).aemeasurable)
        ((hθ_meas n).max aemeasurable_const) n) (hasLaw_mul_max_zero_sq hI_pos) hZ
  refine tendstoInMeasure_zero_of_abs_le (G := fun _ => Set.univ)
    (V := fun n ω => |2 * ∑ i ∈ Finset.range n,
        (Real.log (p (θhat n ω) (X i ω)) - Real.log (p 0 (X i ω))) -
        (n : ℝ) * (θhat n ω - 0) ^ 2 * I|) ?_ (by simp) ?_
  · rw [tendstoInMeasure_iff_norm] at hQ ⊢
    simpa using hQ
  · intro n ω _
    simp only [Pi.sub_apply, Function.comp_apply]
    rcases le_or_gt 0 (θhat n ω) with hθ | hθ
    · have hs : 0 ≤ √(n : ℝ) * (θhat n ω - 0) := by
        rw [sub_zero]; exact mul_nonneg (Real.sqrt_nonneg _) hθ
      rw [max_eq_left hθ, max_eq_left hs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      apply le_of_eq
      congr 1
      ring
    · have hs : √(n : ℝ) * (θhat n ω - 0) ≤ 0 := by
        rw [sub_zero]; exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hθ.le
      rw [max_eq_right hθ.le, max_eq_right hs]
      simp

end MathlibExt.Probability.Statistics.LikelihoodRatioTests
