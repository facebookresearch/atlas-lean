/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Halmos–Savage factorization, necessity, for countable parameter families

Let `P : Θ → Measure Ω` be a countable family of probability measures on `(Ω, m₀)`,
dominated by a σ-finite measure `μ`, and let `T : Ω → τ` be a measurable statistic that is
sufficient for the family (the σ-algebra `comap T` it generates is `IsSufficient`). Then every
density factors as `dP_θ/dμ = g_θ(T) · h` with measurable `g_θ` and a measurable `h` that does
not depend on `θ`.

The proof enumerates `Θ = {θ₀, θ₁, …}` and forms the mixture `Q = ∑ₙ 2⁻⁽ⁿ⁺¹⁾ • P θₙ`, a
probability measure with `P θ ≪ Q ≪ μ` for every `θ`. On `comap T` the Radon–Nikodym
derivative of `P θ` with respect to `Q` factors through `T` as `g_θ ∘ T`, sufficiency gives
`P θ = g_θ(T) · Q`, and `h = dQ/dμ`. An empty `Θ` is trivial (`g = 0`, `h = 0`).

This is the countable-`Θ` slice of the necessity half of the Halmos–Savage theorem, whose
sufficiency half is `isSufficient_comap_of_factorization_of_sigmaFinite_trim`. Uncountable
parameter families remain the Wanted entry `exists_factorization_of_isSufficient_comap` in
`WantedExt.Probability.Statistics.HalmosSavageFactorizationWanted`.

## Main results

* `exists_factorization_of_isSufficient_comap_countable`

## References

* P. R. Halmos and L. J. Savage, *Application of the Radon–Nikodym theorem to the theory of
  sufficient statistics*, Ann. Math. Statist. 20 (1949), 225–241.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Sufficiency

open MeasureTheory Filter Topology

open scoped ENNReal

/-- Mixture weights `2⁻¹ ^ (n+1)`: strictly positive with total mass 1. -/
private noncomputable def mixW : ℕ → ℝ≥0∞ := fun n => (2 : ℝ≥0∞)⁻¹ ^ (n + 1)

private lemma mixW_ne_zero (n : ℕ) : mixW n ≠ 0 := by
  simp [mixW, ne_eq, ENNReal.inv_eq_zero]

private lemma mixW_ne_top (n : ℕ) : mixW n ≠ ∞ := by
  simp [mixW]

private lemma mixW_tsum : ∑' n, mixW n = 1 := by
  have h := ENNReal.tsum_geometric_add_one (2 : ℝ≥0∞)⁻¹
  simp only [mixW]
  rw [h]
  have hr0 : (2 : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hrTop : (2 : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
  have hsub : 1 - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    have h2r : ((2 : ℝ≥0∞)⁻¹).toReal = 1 / 2 := by simp [ENNReal.toReal_inv]
    have hle : (2 : ℝ≥0∞)⁻¹ ≤ 1 := by simp
    have hfin : 1 - (2 : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
    apply (ENNReal.toReal_eq_toReal_iff' hfin hrTop).mp
    rw [ENNReal.toReal_sub_of_le hle (by simp), h2r]
    simp
    norm_num
  rw [hsub, ENNReal.mul_inv_cancel hr0 hrTop]

/-- Positive-weight mixture `Q = ∑ₙ wₙ • P (e n)` dominating the whole family. -/
private noncomputable def mixQ {Ω Θ : Type*} {m₀ : MeasurableSpace Ω}
    (P : Θ → Measure[m₀] Ω) (e : ℕ → Θ) : Measure[m₀] Ω :=
  Measure.sum (fun n => mixW n • P (e n))

private instance mixQ_isProb {Ω Θ : Type*} {m₀ : MeasurableSpace Ω}
    (P : Θ → Measure[m₀] Ω) [∀ θ, IsProbabilityMeasure (P θ)] (e : ℕ → Θ) :
    IsProbabilityMeasure (mixQ P e) := by
  rw [isProbabilityMeasure_iff]
  simp only [mixQ, Measure.sum_apply_of_countable _ Set.univ]
  simp_rw [Measure.smul_apply, smul_eq_mul, IsProbabilityMeasure.measure_univ, mul_one]
  exact mixW_tsum

/-- Every family member is absolutely continuous w.r.t. the mixture. -/
private lemma ac_of_mem_range {Ω Θ : Type*} {m₀ : MeasurableSpace Ω}
    {P : Θ → Measure[m₀] Ω} {e : ℕ → Θ} {θ : Θ} (hθ : θ ∈ Set.range e) :
    P θ ≪ mixQ P e := by
  obtain ⟨n, rfl⟩ := hθ
  apply MeasureTheory.Measure.absolutelyContinuous_sum_right n
  exact MeasureTheory.Measure.AbsolutelyContinuous.rfl.smul_right (mixW_ne_zero n)

/-- The mixture is dominated by `μ` when every member is. -/
private lemma ac_mixQ_mu {Ω Θ : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure[m₀] Ω} {P : Θ → Measure[m₀] Ω}
    (hdom : ∀ θ, P θ ≪ μ) (e : ℕ → Θ) :
    mixQ P e ≪ μ := by
  apply MeasureTheory.Measure.absolutelyContinuous_sum_left
  intro n
  exact (MeasureTheory.Measure.smul_absolutelyContinuous.trans (hdom _))

/-- Trimming preserves absolute continuity. -/
private lemma ac_trim {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {Pθ Q : Measure[m₀] Ω} (h : Pθ ≪ Q) (hm : m ≤ m₀) :
    Pθ.trim hm ≪ Q.trim hm :=
  h.trim hm

/-- The Radon–Nikodym derivative of the trimmed measures: `m`-measurable by construction. -/
private noncomputable def trimRN {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    (Pθ Q : Measure[m₀] Ω) (hm : m ≤ m₀) : Ω → ℝ≥0∞ :=
  (Pθ.trim hm).rnDeriv (Q.trim hm)

private lemma trimRN_measurable {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    (Pθ Q : Measure[m₀] Ω) (hm : m ≤ m₀) :
    Measurable[m] (trimRN Pθ Q hm) :=
  Measure.measurable_rnDeriv _ _

private lemma trimRN_measurable0 {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    (Pθ Q : Measure[m₀] Ω) (hm : m ≤ m₀) :
    Measurable[m₀] (trimRN Pθ Q hm) :=
  (trimRN_measurable Pθ Q hm).mono hm le_rfl

private lemma trimRN_strong_toReal {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    (Pθ Q : Measure[m₀] Ω) (hm : m ≤ m₀) :
    StronglyMeasurable[m] (fun x => (trimRN Pθ Q hm x).toReal) :=
  ((trimRN_measurable Pθ Q hm).ennreal_toReal).stronglyMeasurable

/-- The trimmed density is a.e. finite w.r.t. the full mixture measure. -/
private lemma trimRN_ae_lt_top {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {Pθ Q : Measure[m₀] Ω} [IsFiniteMeasure Pθ] [IsFiniteMeasure Q] (hm : m ≤ m₀) :
    ∀ᵐ x ∂Q, trimRN Pθ Q hm x < ∞ := by
  have hmeas : MeasurableSet[m] {x | trimRN Pθ Q hm x = ∞} := by
    have h : MeasurableSet[m] (trimRN Pθ Q hm ⁻¹' {∞}) :=
      (trimRN_measurable Pθ Q hm) (measurableSet_singleton (∞ : ℝ≥0∞))
    have hset2 : {x : Ω | trimRN Pθ Q hm x = ∞} = trimRN Pθ Q hm ⁻¹' {∞} := rfl
    rwa [hset2]
  have hset : {x : Ω | ¬ trimRN Pθ Q hm x < ∞} = {x | trimRN Pθ Q hm x = ∞} := by
    ext x
    simp [lt_top_iff_ne_top]
  rw [MeasureTheory.ae_iff, hset, ← trim_measurableSet_eq hm hmeas]
  have htrim : ∀ᵐ x ∂(Q.trim hm), trimRN Pθ Q hm x < ∞ :=
    Measure.rnDeriv_lt_top _ _
  have h0 := MeasureTheory.ae_iff.mp htrim
  rwa [hset] at h0

/-- The trimmed density integrates to one: it is a probability density. -/
private lemma trimRN_lintegral_eq_one {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {Pθ Q : Measure[m₀] Ω} [IsProbabilityMeasure Pθ] [IsProbabilityMeasure Q]
    (hm : m ≤ m₀) (h : Pθ ≪ Q) :
    ∫⁻ x, trimRN Pθ Q hm x ∂Q = 1 := by
  have htrim : Pθ.trim hm ≪ Q.trim hm := h.trim hm
  rw [← lintegral_trim hm (trimRN_measurable Pθ Q hm)]
  change ∫⁻ x, ((Pθ.trim hm).rnDeriv (Q.trim hm)) x ∂(Q.trim hm) = 1
  rw [Measure.lintegral_rnDeriv htrim]
  rw [trim_measurableSet_eq hm MeasurableSet.univ]
  exact IsProbabilityMeasure.measure_univ

/-- The trimmed density has finite total integral. -/
private lemma trimRN_lintegral_ne_top {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {Pθ Q : Measure[m₀] Ω} [IsProbabilityMeasure Pθ] [IsProbabilityMeasure Q]
    (hm : m ≤ m₀) (h : Pθ ≪ Q) :
    ∫⁻ x, trimRN Pθ Q hm x ∂Q ≠ ∞ := by
  rw [trimRN_lintegral_eq_one hm h]
  exact (by simp : (1 : ℝ≥0∞) ≠ ∞)

/-- The `θ`-free factor: density of the mixture w.r.t. the dominating measure. -/
private noncomputable def mixH {Ω Θ : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure[m₀] Ω) (P : Θ → Measure[m₀] Ω) (e : ℕ → Θ) : Ω → ℝ≥0∞ :=
  (mixQ P e).rnDeriv μ

private lemma mixH_measurable {Ω Θ : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure[m₀] Ω) (P : Θ → Measure[m₀] Ω) (e : ℕ → Θ) :
    Measurable[m₀] (mixH μ P e) :=
  Measure.measurable_rnDeriv _ _

private lemma mixQ_eq_withDensity {Ω Θ : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure[m₀] Ω} [SigmaFinite μ] {P : Θ → Measure[m₀] Ω}
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hdom : ∀ θ, P θ ≪ μ) (e : ℕ → Θ) :
    μ.withDensity (mixH μ P e) = mixQ P e :=
  Measure.withDensity_rnDeriv_eq _ _ (ac_mixQ_mu hdom e)

/-- Indicators are integrable w.r.t. any finite measure. -/
private lemma indicator_one_integrable {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {Q : Measure[m₀] Ω} [IsFiniteMeasure Q]
    {s : Set Ω} (hs : MeasurableSet[m₀] s) :
    Integrable (s.indicator (fun _ => (1 : ℝ))) Q :=
  (integrable_const (1 : ℝ)).indicator hs

/-- The real-valued trimmed density is integrable w.r.t. the mixture. -/
private lemma trimRN_toReal_integrable {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {Pθ Q : Measure[m₀] Ω} [IsProbabilityMeasure Pθ] [IsProbabilityMeasure Q]
    (hm : m ≤ m₀) (h : Pθ ≪ Q) :
    Integrable (fun x => (trimRN Pθ Q hm x).toReal) Q :=
  integrable_toReal_of_lintegral_ne_top
    (trimRN_measurable0 Pθ Q hm).aemeasurable
    (trimRN_lintegral_ne_top hm h)

/-- The product of the trimmed density with an indicator is integrable. -/
private lemma trimRN_indicator_integrable {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {Pθ Q : Measure[m₀] Ω} [IsProbabilityMeasure Pθ] [IsProbabilityMeasure Q]
    (hm : m ≤ m₀) (h : Pθ ≪ Q)
    {s : Set Ω} (hs : MeasurableSet[m₀] s) :
    Integrable (fun x => (trimRN Pθ Q hm x).toReal * s.indicator (fun _ => (1 : ℝ)) x) Q := by
  have hI_meas : Measurable[m₀] (s.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hs
  have hbound : ∀ᵐ x ∂Q, ‖s.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    filter_upwards with x
    by_cases hx : x ∈ s <;> simp [hx]
  exact (trimRN_toReal_integrable hm h).mul_bdd (c := (1 : ℝ)) hI_meas.aestronglyMeasurable hbound

/-- Conditional expectations of indicators are a.e. bounded by 1. -/
private lemma condExp_indicator_ae_norm_le_one {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    {Pθ : Measure[m₀] Ω} [IsProbabilityMeasure Pθ] (hm : m ≤ m₀)
    {s : Set Ω} (hs : MeasurableSet[m₀] s) :
    ∀ᵐ x ∂Pθ, ‖(Pθ)[s.indicator (fun _ => (1 : ℝ)) | m] x‖ ≤ 1 := by
  have hI_int : Integrable (s.indicator (fun _ => (1 : ℝ))) Pθ :=
    indicator_one_integrable hs
  have h0 : (0 : Ω → ℝ) ≤ᵐ[Pθ] s.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards with x
    by_cases hx : x ∈ s <;> simp [hx]
  have h1 : s.indicator (fun _ => (1 : ℝ)) ≤ᵐ[Pθ] (fun _ => (1 : ℝ)) := by
    filter_upwards with x
    by_cases hx : x ∈ s <;> simp [hx]
  have hlo : (Pθ)[(0 : Ω → ℝ) | m] ≤ᵐ[Pθ] (Pθ)[s.indicator (fun _ => (1 : ℝ)) | m] :=
    condExp_mono (integrable_const (0 : ℝ)) hI_int h0
  have hhi : (Pθ)[s.indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[Pθ] (Pθ)[(fun _ => (1 : ℝ)) | m] :=
    condExp_mono hI_int (integrable_const (1 : ℝ)) h1
  rw [condExp_zero] at hlo
  rw [condExp_const hm (1 : ℝ)] at hhi
  filter_upwards [hlo, hhi] with x hx0 hx1
  have hx0' : 0 ≤ (Pθ)[s.indicator (fun _ => (1 : ℝ)) | m] x := hx0
  have hx1' : (Pθ)[s.indicator (fun _ => (1 : ℝ)) | m] x ≤ 1 := hx1
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- A common conditional expectation version is a.e. bounded by 1 under the mixture. -/
private lemma eta_ae_norm_le_one_mixQ {Ω Θ : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (hm : m ≤ m₀) (e : ℕ → Θ)
    {s : Set Ω} (hs : MeasurableSet[m₀] s) {η : Ω → ℝ}
    (hη : ∀ θ, η =ᵐ[P θ] (P θ)[s.indicator (fun _ => (1 : ℝ)) | m]) :
    ∀ᵐ x ∂(mixQ P e), ‖η x‖ ≤ 1 := by
  change ∀ᵐ x ∂(Measure.sum (fun n => mixW n • P (e n))), ‖η x‖ ≤ 1
  rw [Measure.ae_sum_iff]
  intro n
  rw [Measure.ae_ennreal_smul_measure_iff (mixW_ne_zero n)]
  have hb := condExp_indicator_ae_norm_le_one (Pθ := P (e n)) hm hs
  filter_upwards [hη (e n), hb] with x hx hb'
  rw [hx]
  exact hb'

/-- A common conditional expectation version is integrable w.r.t. the mixture. -/
private lemma eta_integrable_mixQ {Ω Θ : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (hm : m ≤ m₀) (e : ℕ → Θ)
    {s : Set Ω} (hs : MeasurableSet[m₀] s) {η : Ω → ℝ}
    (hηm : StronglyMeasurable[m] η)
    (hη : ∀ θ, η =ᵐ[P θ] (P θ)[s.indicator (fun _ => (1 : ℝ)) | m]) :
    Integrable η (mixQ P e) := by
  refine Integrable.of_bound ?_ 1 (eta_ae_norm_le_one_mixQ hm e hs hη)
  exact ((hηm.measurable).mono hm le_rfl).stronglyMeasurable.aestronglyMeasurable

/-- The common version is also a version of the conditional expectation under the mixture. -/
private lemma eta_ae_eq_condExp_mixQ {Ω Θ : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (hP : IsSufficient m P) (e : ℕ → Θ)
    {s : Set Ω} (hs : MeasurableSet[m₀] s) {η : Ω → ℝ}
    (hηm : StronglyMeasurable[m] η)
    (hη : ∀ θ, η =ᵐ[P θ] (P θ)[s.indicator (fun _ => (1 : ℝ)) | m]) :
    η =ᵐ[mixQ P e] (mixQ P e)[s.indicator (fun _ => (1 : ℝ)) | m] := by
  have hm := hP.1
  have hη_int : Integrable η (mixQ P e) := eta_integrable_mixQ hm e hs hηm hη
  have hI_int : Integrable (s.indicator (fun _ => (1 : ℝ))) (mixQ P e) :=
    indicator_one_integrable hs
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hI_int ?_ ?_ hηm.aestronglyMeasurable
  · intro t ht _
    exact hη_int.integrableOn
  · intro t ht _
    have ht0 : MeasurableSet[m₀] t := hm t ht
    have hInt_eta : Integrable (t.indicator η) (mixQ P e) := hη_int.indicator ht0
    have hInt_I : Integrable (t.indicator (s.indicator (fun _ => (1 : ℝ)))) (mixQ P e) :=
      hI_int.indicator ht0
    have hper : ∀ n, ∫ x, t.indicator η x ∂(mixW n • P (e n))
        = ∫ x, t.indicator (s.indicator (fun _ => (1 : ℝ))) x ∂(mixW n • P (e n)) := by
      intro n
      rw [integral_smul_measure, integral_smul_measure]
      congr 1
      rw [integral_indicator ht0, integral_indicator ht0]
      have h1 : ∫ x in t, η x ∂P (e n)
          = ∫ x in t, (P (e n))[s.indicator (fun _ => (1 : ℝ)) | m] x ∂P (e n) := by
        apply setIntegral_congr_ae ht0
        exact (hη (e n)).mono (fun x hx _ => hx)
      rw [h1]
      exact setIntegral_condExp hm (indicator_one_integrable hs) ht
    have hInt_eta' : Integrable (t.indicator η)
        (Measure.sum (fun n => mixW n • P (e n))) := hInt_eta
    have hInt_I' : Integrable (t.indicator (s.indicator (fun _ => (1 : ℝ))))
        (Measure.sum (fun n => mixW n • P (e n))) := hInt_I
    calc ∫ x in t, η x ∂(mixQ P e)
        = ∫ x, t.indicator η x ∂(mixQ P e) := (integral_indicator ht0).symm
      _ = ∑' n, ∫ x, t.indicator η x ∂(mixW n • P (e n)) :=
          integral_sum_measure hInt_eta'
      _ = ∑' n, ∫ x, t.indicator (s.indicator (fun _ => (1 : ℝ))) x ∂(mixW n • P (e n)) :=
          tsum_congr hper
      _ = ∫ x, t.indicator (s.indicator (fun _ => (1 : ℝ))) x ∂(mixQ P e) :=
          (integral_sum_measure hInt_I').symm
      _ = ∫ x in t, s.indicator (fun _ => (1 : ℝ)) x ∂(mixQ P e) :=
          integral_indicator ht0

/-- The mixture weighted by the trimmed-RN density recovers the family member.
This is the heart of the factorization: sufficiency (via the common conditional
expectation `η`) identifies the `m`-measurable density integral with `P θ s`. -/
private theorem factorMeasure_eq {Ω Θ : Type*} {m m₀ : MeasurableSpace Ω}
    {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (hP : IsSufficient m P) (e : ℕ → Θ) {θ : Θ} (hθ : θ ∈ Set.range e) :
    (mixQ P e).withDensity (trimRN (P θ) (mixQ P e) hP.1) = P θ := by
  have hm := hP.1
  have hQθ : P θ ≪ mixQ P e := ac_of_mem_range hθ
  have htrim : (P θ).trim hm ≪ (mixQ P e).trim hm := hQθ.trim hm
  have hD1 : ∫⁻ x, trimRN (P θ) (mixQ P e) hm x ∂(mixQ P e) = 1 :=
    trimRN_lintegral_eq_one hm hQθ
  apply Measure.ext
  intro s hs
  have hfin2 : P θ s ≠ ∞ := (measure_lt_top _ _).ne
  have hfin1 : (mixQ P e).withDensity (trimRN (P θ) (mixQ P e) hm) s ≠ ∞ := by
    have hle := measure_mono (Set.subset_univ s)
      (μ := (mixQ P e).withDensity (trimRN (P θ) (mixQ P e) hm))
    have h1 : (mixQ P e).withDensity (trimRN (P θ) (mixQ P e) hm) Set.univ = 1 := by
      rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      exact hD1
    have hne1 : (mixQ P e).withDensity (trimRN (P θ) (mixQ P e) hm) Set.univ ≠ ∞ := by
      rw [h1]
      exact (by simp : (1 : ℝ≥0∞) ≠ ∞)
    exact ne_top_of_le_ne_top hne1 hle
  apply (ENNReal.toReal_eq_toReal_iff' hfin1 hfin2).mp
  rw [← measureReal_def, ← measureReal_def]
  have hLHS : ((mixQ P e).withDensity (trimRN (P θ) (mixQ P e) hm)).real s
      = ∫ x in s, (trimRN (P θ) (mixQ P e) hm x).toReal ∂(mixQ P e) := by
    rw [measureReal_def, MeasureTheory.withDensity_apply _ hs]
    have hD0r : AEMeasurable (trimRN (P θ) (mixQ P e) hm)
        ((mixQ P e).restrict s) :=
      (trimRN_measurable0 _ _ hm).aemeasurable.restrict
    have hfin_ae : ∀ᵐ x ∂((mixQ P e).restrict s), trimRN (P θ) (mixQ P e) hm x < ∞ :=
      ae_restrict_of_ae (trimRN_ae_lt_top hm)
    exact (integral_toReal hD0r hfin_ae).symm
  rw [hLHS]
  obtain ⟨η, hηm, hηθ⟩ := hP.2.2 s hs
  have hηQ : η =ᵐ[mixQ P e] (mixQ P e)[s.indicator (fun _ => (1 : ℝ)) | m] :=
    eta_ae_eq_condExp_mixQ hP e hs hηm hηθ
  have hDrM := trimRN_strong_toReal (P θ) (mixQ P e) hm
  have hF_int : Integrable (fun x => (trimRN (P θ) (mixQ P e) hm x).toReal
      * s.indicator (fun _ => (1 : ℝ)) x) (mixQ P e) :=
    trimRN_indicator_integrable hm hQθ hs
  have hI_intQ : Integrable (s.indicator (fun _ => (1 : ℝ))) (mixQ P e) :=
    indicator_one_integrable hs
  have hFI : (fun x => (trimRN (P θ) (mixQ P e) hm x).toReal
      * s.indicator (fun _ => (1 : ℝ)) x)
      = s.indicator (fun x => (trimRN (P θ) (mixQ P e) hm x).toReal) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hT01 : (∫ x in s, (trimRN (P θ) (mixQ P e) hm x).toReal ∂(mixQ P e))
      = ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal
        * s.indicator (fun _ => (1 : ℝ)) x) ∂(mixQ P e) := by
    have hbase := integral_indicator (s := s)
      (f := fun x => (trimRN (P θ) (mixQ P e) hm x).toReal) (μ := mixQ P e) hs
    rw [← hbase, ← hFI]
  have hpull : (mixQ P e)[(fun x => (trimRN (P θ) (mixQ P e) hm x).toReal)
      * s.indicator (fun _ => (1 : ℝ)) | m]
      =ᵐ[mixQ P e] (fun x => (trimRN (P θ) (mixQ P e) hm x).toReal)
        * (mixQ P e)[s.indicator (fun _ => (1 : ℝ)) | m] :=
    condExp_mul_of_stronglyMeasurable_left hDrM hF_int hI_intQ
  have htower : ∫ x, (mixQ P e)[(fun x => (trimRN (P θ) (mixQ P e) hm x).toReal)
      * s.indicator (fun _ => (1 : ℝ)) | m] x ∂(mixQ P e)
      = ∫ x, (((fun x => (trimRN (P θ) (mixQ P e) hm x).toReal)
        * s.indicator (fun _ => (1 : ℝ))) x) ∂(mixQ P e) :=
    integral_condExp hm
  have hT12 : (∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal
        * s.indicator (fun _ => (1 : ℝ)) x) ∂(mixQ P e))
      = ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal
        * (mixQ P e)[s.indicator (fun _ => (1 : ℝ)) | m] x) ∂(mixQ P e) := by
    calc ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal
          * s.indicator (fun _ => (1 : ℝ)) x) ∂(mixQ P e)
        = ∫ x, (((fun x => (trimRN (P θ) (mixQ P e) hm x).toReal)
          * s.indicator (fun _ => (1 : ℝ))) x) ∂(mixQ P e) := rfl
      _ = ∫ x, (mixQ P e)[(fun x => (trimRN (P θ) (mixQ P e) hm x).toReal)
          * s.indicator (fun _ => (1 : ℝ)) | m] x ∂(mixQ P e) := htower.symm
      _ = ∫ x, (((fun x => (trimRN (P θ) (mixQ P e) hm x).toReal)
          * (mixQ P e)[s.indicator (fun _ => (1 : ℝ)) | m]) x) ∂(mixQ P e) :=
          integral_congr_ae hpull
      _ = ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal
          * (mixQ P e)[s.indicator (fun _ => (1 : ℝ)) | m] x) ∂(mixQ P e) := rfl
  have hT23 : (∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal
        * (mixQ P e)[s.indicator (fun _ => (1 : ℝ)) | m] x) ∂(mixQ P e))
      = ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal * η x) ∂(mixQ P e) := by
    apply integral_congr_ae
    exact hηQ.mono (fun x hx => by simp only [hx])
  have hDrEtaM : StronglyMeasurable[m] (fun x =>
      (trimRN (P θ) (mixQ P e) hm x).toReal * η x) :=
    hDrM.mul hηm
  have hT34 : (∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal * η x) ∂(mixQ P e))
      = ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal * η x) ∂((mixQ P e).trim hm) :=
    integral_trim hm hDrEtaM
  have hT45 : (∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal * η x) ∂((mixQ P e).trim hm))
      = ∫ x, η x ∂((P θ).trim hm) :=
    integral_toReal_rnDeriv_mul htrim
  have hT56 : (∫ x, η x ∂((P θ).trim hm)) = ∫ x, η x ∂(P θ) :=
    (integral_trim hm hηm).symm
  have hT67 : (∫ x, η x ∂(P θ))
      = ∫ x, (P θ)[s.indicator (fun _ => (1 : ℝ)) | m] x ∂(P θ) :=
    integral_congr_ae (hηθ θ)
  have hT78 : (∫ x, (P θ)[s.indicator (fun _ => (1 : ℝ)) | m] x ∂(P θ))
      = ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂(P θ) :=
    integral_condExp hm
  have hT89 : (∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂(P θ)) = (P θ).real s := by
    rw [integral_indicator hs]
    show ∫ x in s, (1 : ℝ) ∂(P θ) = (P θ).real s
    rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
  calc ∫ x in s, (trimRN (P θ) (mixQ P e) hm x).toReal ∂(mixQ P e)
      = ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal
        * s.indicator (fun _ => (1 : ℝ)) x) ∂(mixQ P e) := hT01
    _ = ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal
        * (mixQ P e)[s.indicator (fun _ => (1 : ℝ)) | m] x) ∂(mixQ P e) := hT12
    _ = ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal * η x) ∂(mixQ P e) := hT23
    _ = ∫ x, ((trimRN (P θ) (mixQ P e) hm x).toReal * η x) ∂((mixQ P e).trim hm) := hT34
    _ = ∫ x, η x ∂((P θ).trim hm) := hT45
    _ = ∫ x, η x ∂(P θ) := hT56
    _ = ∫ x, (P θ)[s.indicator (fun _ => (1 : ℝ)) | m] x ∂(P θ) := hT67
    _ = ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂(P θ) := hT78
    _ = (P θ).real s := hT89

/-- **Halmos–Savage factorization, necessity, for countable parameter families.** If a
countable family of probability measures `P` is dominated by a σ-finite measure
`μ` and the statistic `T` is sufficient for `P`, then the densities factor as
`dP_θ/dμ = g_θ(T) · h` with measurable `g_θ` and `h`, `h` free of `θ`.

This is the countable-`Θ` slice of `exists_factorization_of_isSufficient_comap` in
`WantedExt.Probability.Statistics.HalmosSavageFactorizationWanted`; uncountable `Θ` stays with
the Wanted entry. -/
theorem exists_factorization_of_isSufficient_comap_countable
    {Ω Θ τ : Type*} [MeasurableSpace τ] {m₀ : MeasurableSpace Ω} {T : Ω → τ}
    (hT : Measurable T)
    (μ : Measure[m₀] Ω) [SigmaFinite μ] (P : Θ → Measure[m₀] Ω)
    [Countable Θ]
    [∀ θ, IsProbabilityMeasure (P θ)] (hdom : ∀ θ, P θ ≪ μ)
    (hP : IsSufficient (MeasurableSpace.comap T ‹MeasurableSpace τ›) P) :
    ∃ (g : Θ → τ → ℝ≥0∞) (h : Ω → ℝ≥0∞), (∀ θ, Measurable (g θ)) ∧ Measurable h ∧
      ∀ θ, P θ = μ.withDensity (fun ω => g θ (T ω) * h ω) := by
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · exact ⟨fun _ _ => 0, fun _ => 0, isEmptyElim, measurable_const, isEmptyElim⟩
  obtain ⟨e, he⟩ := exists_surjective_nat Θ
  have hfac : ∀ θ, ∃ gθ : τ → ℝ≥0∞,
      Measurable gθ ∧ trimRN (P θ) (mixQ P e) hP.1 = gθ ∘ T := by
    intro θ
    exact Measurable.exists_eq_measurable_comp (trimRN_measurable (P θ) (mixQ P e) hP.1)
  choose g hgmeas hgeq using hfac
  refine ⟨g, mixH μ P e, hgmeas, mixH_measurable μ P e, fun θ => ?_⟩
  have hθmem : θ ∈ Set.range e := by
    obtain ⟨n, hn⟩ := he θ
    exact ⟨n, hn⟩
  have hFM : (mixQ P e).withDensity (trimRN (P θ) (mixQ P e) hP.1) = P θ :=
    factorMeasure_eq hP e hθmem
  have hQeq : μ.withDensity (mixH μ P e) = mixQ P e := mixQ_eq_withDensity hdom e
  have hcomp : Measurable (fun ω => g θ (T ω)) := (hgmeas θ).comp hT
  have hmulcomm : ((mixH μ P e) * (fun ω => g θ (T ω)))
      = (fun ω => g θ (T ω) * mixH μ P e ω) := by
    ext ω
    exact mul_comm _ _
  calc P θ = (mixQ P e).withDensity (trimRN (P θ) (mixQ P e) hP.1) := hFM.symm
    _ = (mixQ P e).withDensity (fun ω => g θ (T ω)) := by
        congr 1
        exact hgeq θ
    _ = (μ.withDensity (mixH μ P e)).withDensity (fun ω => g θ (T ω)) := by rw [hQeq]
    _ = μ.withDensity ((mixH μ P e) * (fun ω => g θ (T ω))) :=
        (withDensity_mul μ (mixH_measurable μ P e) hcomp).symm
    _ = μ.withDensity (fun ω => g θ (T ω) * mixH μ P e ω) := by rw [hmulcomm]

end MathlibExt.Probability.Statistics.Sufficiency
