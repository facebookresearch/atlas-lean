/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ContinuousDistributions

/-!
# Tests for continuous distributions, sampling identities and sampling limits

The statements of each part in their stated form, concrete numeric instances, a non-vacuity
check for `StudentTPivotLaw`, a point-counting area-fraction estimator, and `#print axioms` for
every public declaration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal
open MathlibExt.Probability.ContinuousDistributions

namespace MathlibExtTest.Probability.ContinuousDistributions

/-! ### A. Gaussian and exponential laws -/

/-- Gaussian normalization, for `v ≠ 0`: Mathlib's `integral_gaussianPDFReal_eq_one`. -/
example (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ∫ x, gaussianPDFReal μ v x = 1 :=
  integral_gaussianPDFReal_eq_one μ hv

/-- Gaussian mean: Mathlib's `integral_id_gaussianReal`. -/
example (μ : ℝ) (v : ℝ≥0) : ∫ x, x ∂gaussianReal μ v = μ :=
  integral_id_gaussianReal

/-- Gaussian second central moment in its stated form, for `0 < v` (the lemma needs no
hypothesis on `v`). -/
example (μ : ℝ) {v : ℝ≥0} (_hv : 0 < v) : ∫ x, (x - μ) ^ 2 ∂gaussianReal μ v = (v : ℝ) :=
  integral_sub_sq_gaussianReal μ v

/-- Exponential normalization, for `0 < r`: Mathlib's `lintegral_exponentialPDF_eq_one`. -/
example {r : ℝ} (hr : 0 < r) : ∫⁻ x, exponentialPDF r x = 1 :=
  lintegral_exponentialPDF_eq_one hr

/-- Exponential mean, for `0 < r`. -/
example {r : ℝ} (hr : 0 < r) : ∫ x, x ∂expMeasure r = 1 / r :=
  integral_id_expMeasure_eq_one_div hr

/-- `N(1, 4)` has central second moment `4`, and `Exp(2)` has mean `1 / 2`. -/
example : ∫ x, (x - 1) ^ 2 ∂gaussianReal 1 4 = 4 ∧ ∫ x, x ∂expMeasure 2 = 1 / 2 := by
  refine ⟨?_, integral_id_expMeasure_eq_one_div (by norm_num)⟩
  rw [integral_sub_sq_gaussianReal]
  norm_num

/-! ### B. Sample mean and the Student-t pivot -/

/-- The finite-sample expectation identity `E[(∑ i < n, X i) / n] = E[X 0]`, for `n ≥ 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hint : Integrable (X 0) P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {n : ℕ}
    (hn : 1 ≤ n) :
    ∫ ω, (∑ i ∈ Finset.range n, X i ω) / n ∂P = ∫ ω, X 0 ω ∂P :=
  integral_sampleMean hint hident (by omega)

/-- `Var[(∑ i < n, X i) / n] = Var[X 0] / n`, for `n ≥ 1`. Mutual independence, the hypothesis
of ATLAS's `variance_sample_mean_of_iid`, gives the pairwise hypothesis of
`variance_sampleMean`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (h2 : MemLp (X 0) 2 P) (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {n : ℕ} (hn : 1 ≤ n) :
    Var[fun ω => (∑ i ∈ Finset.range n, X i ω) / n; P] = Var[X 0; P] / n :=
  variance_sampleMean h2 (fun _ _ hij => hindep.indepFun hij) hident (by omega)

/-- Nominal `95 %` coverage, conditional on `StudentTPivotLaw`, for a critical value `q` whose
two tails under the pivot law have mass `0.025` each. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {μ σ q : ℝ} {n : ℕ}
    {tLaw : ℕ → Measure ℝ} (h : StudentTPivotLaw X μ σ n tLaw P) (hq : 0 ≤ q)
    (hlower : (tLaw (n - 1)).real (Iio (-q)) = 0.025)
    (hupper : (tLaw (n - 1)).real (Ioi q) = 0.025) :
    P.real {ω | μ ∈ studentTInterval X n q ω} = 0.95 := by
  rw [h.measureReal_mem_studentTInterval (α := 0.05) hq (by rw [hlower]; norm_num)
    (by rw [hupper]; norm_num)]
  norm_num

/-- Coverage for every `q` is the mass of `[-q, q]` under the pivot law. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {μ σ : ℝ} {n : ℕ}
    {tLaw : ℕ → Measure ℝ} (h : StudentTPivotLaw X μ σ n tLaw P) (q : ℝ) :
    P {ω | μ ∈ studentTInterval X n q ω} = tLaw (n - 1) (Icc (-q) q) :=
  h.measure_mem_studentTInterval q

/-- Non-vacuity of `StudentTPivotLaw`: for independent standard normal observations every field
holds when `tLaw` is the law of the pivot itself. This only checks that the fields are
consistent; it does not identify that law with a Student-t law. (Mathlib's
`ProbabilityTheory.exists_iid` supplies such observations.) -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) :
    StudentTPivotLaw X 0 1 2 (fun _ => P.map (studentTPivot X 0 2)) P where
  two_le := le_rfl
  sigma_pos := one_pos
  indep := hindep.precomp Fin.val_injective
  hasLaw_sample i _ := by simpa using hlaw i
  hasLaw_pivot := by
    refine ⟨Measurable.aemeasurable ?_, rfl⟩
    have hmean : Measurable (sampleMean X 2) :=
      (Finset.measurable_sum _ fun i _ => hX i).div_const _
    have hvar : Measurable (sampleVariance X 2) :=
      (Finset.measurable_sum _ fun i _ => ((hX i).sub hmean).pow_const 2).div_const _
    exact ((hmean.sub_const 0).const_mul _).div hvar.sqrt

/-! ### C. Strong law of large numbers -/

/-- The strong law: sample means converge almost surely to `E[X 0]`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hint : Integrable (X 0) P) (hindep : Pairwise fun i j => IndepFun (X i) (X j) P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n) atTop
      (𝓝 (∫ ω, X 0 ω ∂P)) :=
  ae_tendsto_sampleMean hint hindep hident

/-- **Point-counting estimator of an area fraction.** Test points `ξ i` are sampled uniformly on
the unit square `U = [0, 1] × [0, 1]`, which has area `1`: each has law `volume.restrict U` (so
`P` is a probability measure), and the points are pairwise independent. The observable is the
indicator `Y i ω = A.indicator 1 (ξ i ω)` of the event that `ξ i ω` falls in a measurable phase
`A ⊆ U`. It is measurable and bounded by `1`, hence integrable, and its mean is the area fraction
of `A` in `U`, the normalized planar area `volume.real A`. The point fraction `x̄ₙ` is unbiased for
every `n ≠ 0` (finite sample) and converges to `volume.real A` almost surely (strong law).
(Mathlib's `ProbabilityTheory.exists_iid` supplies such points.) -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℕ → Ω → ℝ × ℝ}
    (hξ : ∀ i, Measurable (ξ i)) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A)
    (hAU : A ⊆ Icc (0, 0) (1, 1))
    (hlaw : ∀ i, HasLaw (ξ i) (volume.restrict (Icc (0, 0) (1, 1))) P)
    (hindep : Pairwise fun i j => IndepFun (ξ i) (ξ j) P) :
    (∀ n, n ≠ 0 → ∫ ω, sampleMean (fun i ω => A.indicator 1 (ξ i ω)) n ω ∂P = volume.real A) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => sampleMean (fun i ω => A.indicator 1 (ξ i ω)) n ω) atTop
        (𝓝 (volume.real A)) := by
  have hU : volume (Icc (0, 0) (1, 1) : Set (ℝ × ℝ)) = 1 := by
    rw [← Icc_prod_Icc, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    norm_num
  have : IsProbabilityMeasure (volume.restrict (Icc (0, 0) (1, 1) : Set (ℝ × ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ, hU]⟩
  have := (hlaw 0).isProbabilityMeasure
  have hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P := fun i => (hlaw i).identDistrib (hlaw 0)
  have hφ : Measurable (A.indicator (1 : ℝ × ℝ → ℝ)) := measurable_one.indicator hA
  have hYindep : Pairwise fun i j =>
      IndepFun (fun ω => A.indicator 1 (ξ i ω)) (fun ω => A.indicator 1 (ξ j ω)) P :=
    fun _ _ hij => (hindep hij).comp hφ hφ
  have hYident : ∀ i, IdentDistrib (fun ω => A.indicator 1 (ξ i ω))
      (fun ω => A.indicator (1 : ℝ × ℝ → ℝ) (ξ 0 ω)) P P :=
    fun i => (hident i).comp hφ
  have hY0 : (fun ω => A.indicator (1 : ℝ × ℝ → ℝ) (ξ 0 ω)) = (ξ 0 ⁻¹' A).indicator 1 := by
    funext ω
    exact (indicator_comp_right (ξ 0) (g := 1)).symm
  have hYint : Integrable (fun ω => A.indicator (1 : ℝ × ℝ → ℝ) (ξ 0 ω)) P := by
    rw [hY0]
    exact (integrable_const (1 : ℝ)).indicator (hξ 0 hA)
  have hmean : ∫ ω, A.indicator (1 : ℝ × ℝ → ℝ) (ξ 0 ω) ∂P = volume.real A := by
    rw [← Function.comp_def (A.indicator 1) (ξ 0), (hlaw 0).integral_comp hφ.aestronglyMeasurable,
      integral_indicator_one hA, measureReal_restrict_apply hA, inter_eq_left.2 hAU]
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [integral_sampleMean hYint hYident hn, hmean]
  · simpa [hmean] using ae_tendsto_sampleMean hYint hYindep hYident

/-! ### D. Weibull survival and weakest-link scaling -/

/-- `S(0) = 1`, `x ≤ y → S(y) ≤ S(x)`, `S → 0` at `∞`, and the assumed hazard. -/
example {k lam : ℝ} (hk : 0 < k) (hlam : 0 < lam) :
    weibullSurvival k lam 0 = 1 ∧
      (∀ x y, x ≤ y → weibullSurvival k lam y ≤ weibullSurvival k lam x) ∧
      Tendsto (weibullSurvival k lam) atTop (𝓝 0) ∧
      ∀ x, 0 ≤ x → -Real.log (weibullSurvival k lam x) = (x / lam) ^ k :=
  ⟨weibullSurvival_zero hk.ne' lam, fun _ _ hxy => antitone_weibullSurvival hk.le hlam.le hxy,
    tendsto_weibullSurvival_atTop hk hlam, fun _ hx => neg_log_weibullSurvival hx⟩

/-- Shape `2`, scale `1`: `S(1) = exp (-1)` and `S(-1) = 1`. -/
example : weibullSurvival 2 1 1 = Real.exp (-1) ∧ weibullSurvival 2 1 (-1) = 1 := by
  refine ⟨?_, weibullSurvival_of_neg (by norm_num)⟩
  rw [weibullSurvival_of_nonneg zero_le_one]
  norm_num

/-- Weakest link: `n` links of survival `S` whose joint survival is the product give `S ^ n`. -/
example {n : ℕ} {S system : ℝ → ℝ} (hindep : ∀ x, system x = ∏ _i ∈ Finset.range n, S x)
    (x : ℝ) : system x = S x ^ n :=
  weakestLink_survival_eq_pow (link := fun _ => S) hindep (fun _ _ _ => rfl) x

/-- Independent random link strengths with a common Weibull survival function: a chain of
`n ≠ 0` links survives the load `x` with the Weibull survival of the same shape and scale
`lam / n ^ (1 / k)`. Both hypotheses are used. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ} (hT : iIndepFun T P)
    {k lam : ℝ} (hk : 0 < k) (hlam : 0 < lam)
    (hS : ∀ i x, P.real {ω | x < T i ω} = weibullSurvival k lam x) {n : ℕ} (hn : n ≠ 0)
    (x : ℝ) :
    P.real {ω | ∀ i < n, x < T i ω} = weibullSurvival k (lam / (n : ℝ) ^ (1 / k)) x := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [weakestLink_survival_eq_pow (system := fun x => P.real {ω | ∀ i < n, x < T i ω})
    (link := fun i x => P.real {ω | x < T i ω}) (measureReal_forall_lt_eq_prod hT n)
    (fun i _ x => hS i x) x, ← weibullSurvival_rpow hk hlam hn', rpow_natCast]

/-- Size scaling: a specimen of volume `V = 3 V₀` that behaves as three independent reference
volumes has survival `Sref ^ (V / V₀)`; for a Weibull reference this is the Weibull survival with
scale `lam / (V / V₀) ^ (1 / k)`. -/
example {V V₀ : ℝ} (hV₀ : V₀ ≠ 0) (hV : V = 3 * V₀) {k lam : ℝ} (hk : 0 < k) (hlam : 0 < lam)
    {specimen : ℝ → ℝ}
    (hindep : ∀ x, specimen x = ∏ _i ∈ Finset.range 3, weibullSurvival k lam x) (x : ℝ) :
    specimen x = weibullSurvival k lam x ^ (V / V₀) ∧
      specimen x = weibullSurvival k (lam / (V / V₀) ^ (1 / k)) x := by
  have hm : V / V₀ = ((3 : ℕ) : ℝ) := by
    rw [hV, mul_div_assoc, div_self hV₀]
    norm_num
  have h := sizeScaling_survival_eq_rpow hm (piece := fun _ => weibullSurvival k lam) hindep
    (fun _ _ _ => rfl) x
  refine ⟨h, ?_⟩
  rw [h, weibullSurvival_rpow hk hlam (by rw [hm]; norm_num)]

/-! ### E. JMAK void probability -/

/-- The void probability is `1` at volume `0`, decreasing, tends to `0`, and the transformed
fraction lies in `[0, 1]`. -/
example {kappa : ℝ} (hkappa : 0 < kappa) :
    voidProbability kappa 0 = 1 ∧
      (∀ v w, v ≤ w → voidProbability kappa w ≤ voidProbability kappa v) ∧
      Tendsto (fun v => voidProbability kappa v) atTop (𝓝 0) ∧
      ∀ volume, 0 ≤ volume → 1 - voidProbability kappa volume ∈ Icc 0 1 :=
  ⟨voidProbability_zero kappa, fun _ _ hvw => antitone_voidProbability hkappa.le hvw,
    tendsto_voidProbability_atTop hkappa,
    fun _ hvolume => one_sub_voidProbability_mem_Icc hkappa.le hvolume⟩

/-- Avrami substitution with extended volume `K t ^ n`; the Avrami fraction lies in `[0, 1]`
for `0 < K` and `0 ≤ t`. -/
example {K t n : ℝ} (hK : 0 < K) (ht : 0 ≤ t) :
    1 - voidProbability 1 (K * t ^ n) = 1 - Real.exp (-K * t ^ n) ∧
      1 - Real.exp (-K * t ^ n) ∈ Icc 0 1 := by
  have h := one_sub_voidProbability_eq_avrami (kappa := 1) (volume := K * t ^ n) (one_mul _)
  refine ⟨h, ?_⟩
  rw [← h]
  exact one_sub_voidProbability_mem_Icc zero_le_one (mul_nonneg hK.le (rpow_nonneg ht n))

/-- Intensity `2`, volume `3`: void probability `exp (-6)`. -/
example : voidProbability 2 3 = Real.exp (-6) := by
  norm_num [voidProbability]

/-! ### F. Maxwell speed density -/

/-- Scale `a = 1`: the density is nonnegative, its normalization specializes, and the second
moment is `3`. -/
example : (∀ v, 0 ≤ maxwellSpeedPDF 1 v) ∧ ∫ v in Ioi 0, maxwellSpeedPDF 1 v = 1 ∧
    ∫ v in Ioi 0, v ^ 2 * maxwellSpeedPDF 1 v = 3 := by
  refine ⟨maxwellSpeedPDF_nonneg zero_le_one, integral_maxwellSpeedPDF one_pos, ?_⟩
  rw [integral_sq_mul_maxwellSpeedPDF one_pos]
  norm_num

/-- Scale `a = 1`, speed `v = 1`: the density is `√(2 / π) exp (-1 / 2)`. -/
example : maxwellSpeedPDF 1 1 = Real.sqrt (2 / Real.pi) * Real.exp (-1 / 2) := by
  norm_num [maxwellSpeedPDF]

end MathlibExtTest.Probability.ContinuousDistributions

/-! ### Axioms of every public declaration -/

#print axioms MathlibExt.Probability.ContinuousDistributions.integral_sub_sq_gaussianReal
#print axioms MathlibExt.Probability.ContinuousDistributions.integral_id_expMeasure_eq_one_div
#print axioms MathlibExt.Probability.ContinuousDistributions.sampleMean
#print axioms MathlibExt.Probability.ContinuousDistributions.integral_sampleMean
#print axioms MathlibExt.Probability.ContinuousDistributions.variance_sampleMean
#print axioms MathlibExt.Probability.ContinuousDistributions.sampleVariance
#print axioms MathlibExt.Probability.ContinuousDistributions.sampleStdDev
#print axioms MathlibExt.Probability.ContinuousDistributions.studentTPivot
#print axioms MathlibExt.Probability.ContinuousDistributions.studentTInterval
#print axioms MathlibExt.Probability.ContinuousDistributions.StudentTPivotLaw
#print axioms MathlibExt.Probability.ContinuousDistributions.StudentTPivotLaw.two_le
#print axioms MathlibExt.Probability.ContinuousDistributions.StudentTPivotLaw.sigma_pos
#print axioms MathlibExt.Probability.ContinuousDistributions.StudentTPivotLaw.indep
#print axioms MathlibExt.Probability.ContinuousDistributions.StudentTPivotLaw.hasLaw_sample
#print axioms MathlibExt.Probability.ContinuousDistributions.StudentTPivotLaw.hasLaw_pivot
#print axioms MathlibExt.Probability.ContinuousDistributions.StudentTPivotLaw.ae_sampleStdDev_pos
#print axioms
  MathlibExt.Probability.ContinuousDistributions.StudentTPivotLaw.measure_mem_studentTInterval
#print axioms
  MathlibExt.Probability.ContinuousDistributions.StudentTPivotLaw.measureReal_mem_studentTInterval
#print axioms MathlibExt.Probability.ContinuousDistributions.ae_tendsto_sampleMean
#print axioms MathlibExt.Probability.ContinuousDistributions.weibullSurvival
#print axioms MathlibExt.Probability.ContinuousDistributions.weibullSurvival_of_neg
#print axioms MathlibExt.Probability.ContinuousDistributions.weibullSurvival_of_nonneg
#print axioms MathlibExt.Probability.ContinuousDistributions.weibullSurvival_zero
#print axioms MathlibExt.Probability.ContinuousDistributions.antitone_weibullSurvival
#print axioms MathlibExt.Probability.ContinuousDistributions.tendsto_weibullSurvival_atTop
#print axioms MathlibExt.Probability.ContinuousDistributions.neg_log_weibullSurvival
#print axioms MathlibExt.Probability.ContinuousDistributions.weakestLink_survival_eq_pow
#print axioms MathlibExt.Probability.ContinuousDistributions.measureReal_forall_lt_eq_prod
#print axioms MathlibExt.Probability.ContinuousDistributions.sizeScaling_survival_eq_rpow
#print axioms MathlibExt.Probability.ContinuousDistributions.weibullSurvival_rpow
#print axioms MathlibExt.Probability.ContinuousDistributions.voidProbability
#print axioms MathlibExt.Probability.ContinuousDistributions.voidProbability_zero
#print axioms MathlibExt.Probability.ContinuousDistributions.antitone_voidProbability
#print axioms MathlibExt.Probability.ContinuousDistributions.tendsto_voidProbability_atTop
#print axioms MathlibExt.Probability.ContinuousDistributions.one_sub_voidProbability_mem_Icc
#print axioms MathlibExt.Probability.ContinuousDistributions.one_sub_voidProbability_eq_avrami
#print axioms MathlibExt.Probability.ContinuousDistributions.maxwellSpeedPDF
#print axioms MathlibExt.Probability.ContinuousDistributions.maxwellSpeedPDF_nonneg
#print axioms MathlibExt.Probability.ContinuousDistributions.integral_maxwellSpeedPDF
#print axioms MathlibExt.Probability.ContinuousDistributions.integral_sq_mul_maxwellSpeedPDF
