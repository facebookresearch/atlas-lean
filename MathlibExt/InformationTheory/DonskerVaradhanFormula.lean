/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.DonskerVaradhan

/-!
# The Donsker–Varadhan variational formula

For probability measures `μ`, `ν`,

`KL(μ ‖ ν) = sup_f (∫ f dμ - log ∫ exp f dν)⁺`,

the supremum being over bounded measurable `f : α → ℝ`. The inequality `≥` is
`ofReal_integral_sub_log_integral_exp_le_klDiv`. This file proves `≤`.

## Proof idea

* If `μ` is not absolutely continuous with respect to `ν`, pick a measurable `A` with
  `ν A = 0 < μ A`. The test function `t • 1_A` has value `t μ(A)`, so the supremum is `∞`.
* If `μ ≪ ν`, write `ρ = dμ/dν` and `fₖ = clampLog k ρ`, the logarithm of `ρ` clamped to
  `[-k, k]` (and `-k` where `ρ = 0`). Since `log z ≤ z - 1`,
  `∫ fₖ dμ - log ∫ exp fₖ dν ≥ ∫ (ρ fₖ - exp fₖ + 1) dν`. The integrand `ρ fₖ - exp fₖ + 1` is
  nonnegative and tends pointwise to `klFun ρ = ρ log ρ + 1 - ρ`; Fatou's lemma and
  `KL(μ ‖ ν) = ∫⁻ klFun ρ dν` conclude. This argument does not split on whether the
  log-likelihood ratio is integrable.

## Source

S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 3, Lemma 1.2 in the notes' numbering
(https://math.nyu.edu/~varadhan/LDP/Spring2010.3.pdf).

## Main results

* `clampLog`: the clamped logarithm used as test function.
* `iSup_eq_top_of_not_absolutelyContinuous`: the supremum is `∞` when `¬ μ ≪ ν`.
* `klDiv_le_iSup_of_absolutelyContinuous`: `KL(μ ‖ ν) ≤ sup` when `μ ≪ ν`.
* `klDiv_eq_iSup`: the Donsker–Varadhan variational formula.
-/

@[expose] public section

open MeasureTheory Real Set InformationTheory Filter Topology
open scoped ENNReal

namespace MathlibExt.InformationTheory.DonskerVaradhan

/-- **Clamped logarithm.** `clampLog k r` is `log r` clamped to `[-k, k]` when `r > 0`, and
`-k` when `r ≤ 0`. -/
noncomputable def clampLog (k r : ℝ) : ℝ :=
  if 0 < r then max (-k) (min (log r) k) else -k

/-- **Measurability of the clamped logarithm.** -/
theorem measurable_clampLog (k : ℝ) : Measurable (clampLog k) := by
  unfold clampLog
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (measurable_const.max (measurable_log.min measurable_const)) measurable_const

/-- **The clamped logarithm is bounded.** For `k ≥ 0`, `|clampLog k r| ≤ k`. -/
theorem abs_clampLog_le {k : ℝ} (hk : 0 ≤ k) (r : ℝ) : |clampLog k r| ≤ k := by
  unfold clampLog
  split_ifs
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  · rw [abs_neg, abs_of_nonneg hk]

/-- **Nonnegativity of the Donsker–Varadhan gain.** For `k ≥ 0` and `r ≥ 0`, with
`f = clampLog k r`, `0 ≤ r f - exp f + 1`. -/
theorem clampLog_gain_nonneg {k : ℝ} (hk : 0 ≤ k) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ r * clampLog k r - exp (clampLog k r) + 1 := by
  by_cases hr0 : 0 < r
  · have key : ∀ f : ℝ, exp f - 1 ≤ f * exp f := fun f => by
      have h1 := add_one_le_exp (-f)
      have h2 : exp (-f) * exp f = 1 := by rw [← exp_add]; simp
      nlinarith [exp_pos f]
    suffices prod : 0 ≤ clampLog k r * (r - exp (clampLog k r)) by
      nlinarith [key (clampLog k r)]
    simp only [clampLog, hr0, ↓reduceIte]
    by_cases h1 : log r ≤ k
    · rw [min_eq_left h1]
      by_cases h2 : -k ≤ log r
      · rw [max_eq_right h2, exp_log hr0]; simp
      · push Not at h2
        rw [max_eq_left h2.le]
        have : r ≤ exp (-k) := by
          rw [← exp_log hr0]; exact exp_le_exp.2 h2.le
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · push Not at h1
      rw [min_eq_right h1.le, max_eq_right (by linarith)]
      have : exp k ≤ r := by
        rw [← exp_log hr0]; exact exp_le_exp.2 h1.le
      exact mul_nonneg hk (by linarith)
  · have hr' : r = 0 := le_antisymm (not_lt.1 hr0) hr
    subst hr'
    simp only [clampLog, lt_irrefl, ↓reduceIte, zero_mul, zero_sub]
    have : exp (-k) ≤ 1 := exp_le_one_iff.2 (by linarith)
    linarith

/-- **Convergence of the Donsker–Varadhan gain.** For `r ≥ 0`,
`r fₖ - exp fₖ + 1 → klFun r` as `k → ∞`, where `fₖ = clampLog k r`. -/
theorem tendsto_clampLog_gain {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun k : ℕ => r * clampLog k r - exp (clampLog k r) + 1) atTop
      (𝓝 (klFun r)) := by
  by_cases hr0 : 0 < r
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop |log r|] with k hk
    have hk' := abs_le.1 hk
    have : clampLog k r = log r := by
      simp only [clampLog, hr0, ↓reduceIte]
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    rw [this, klFun_apply, exp_log hr0]
    ring
  · have hr' : r = 0 := le_antisymm (not_lt.1 hr0) hr
    subst hr'
    simp only [clampLog, lt_irrefl, ↓reduceIte, zero_mul, zero_sub, klFun_zero]
    have h := (tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).neg.add_const
      (1 : ℝ)
    simpa using h

variable {α : Type*} {mα : MeasurableSpace α}

/-- **The Donsker–Varadhan supremum is infinite without absolute continuity.** If `μ` is not
absolutely continuous with respect to `ν`, then
`sup_f (∫ f dμ - log ∫ exp f dν)⁺ = ∞` over bounded measurable `f`. -/
theorem iSup_eq_top_of_not_absolutelyContinuous (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ¬ μ ≪ ν) :
    ⨆ (f : α → ℝ) (_ : Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C),
      ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)) = ⊤ := by
  obtain ⟨s, hνs, hμs⟩ : ∃ s, ν s = 0 ∧ μ s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h fun s hs => hcon s hs
  set A := toMeasurable ν s with hA_def
  have hA : MeasurableSet A := measurableSet_toMeasurable ν s
  have hνA : ν A = 0 := by rw [hA_def, measure_toMeasurable]; exact hνs
  have hμA : 0 < μ.real A := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos
      (fun h0 => hμs (measure_mono_null (subset_toMeasurable ν s) h0)) (measure_ne_top _ _)
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  set t : ℝ := r / μ.real A with ht_def
  have ht : 0 ≤ t := div_nonneg r.2 hμA.le
  let f : α → ℝ := A.indicator fun _ => t
  have hfm : Measurable f := measurable_const.indicator hA
  have hfb : ∀ x, |f x| ≤ t := fun x => by
    by_cases hx : x ∈ A
    · simp [f, hx, abs_of_nonneg ht]
    · simp [f, hx, ht]
  refine le_iSup₂_of_le f ⟨hfm, t, hfb⟩ (le_of_eq ?_)
  have h1 : ∫ x, f x ∂μ = r := by
    simp only [f]
    rw [integral_indicator_const _ hA, smul_eq_mul, ht_def]
    field_simp
  have h2 : ∫ x, exp (f x) ∂ν = 1 := by
    have hae : (fun x => exp (f x)) =ᵐ[ν] fun _ => (1 : ℝ) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hνA] with x hx
      simp [f, hx]
    rw [integral_congr_ae hae]
    simp
  rw [h1, h2, log_one, sub_zero, ENNReal.ofReal_coe_nnreal]

/-- **Donsker–Varadhan lower bound on the supremum.** If `μ ≪ ν` are probability measures,
then `KL(μ ‖ ν) ≤ sup_f (∫ f dμ - log ∫ exp f dν)⁺` over bounded measurable `f`; the
clamped log-likelihood ratios `clampLog k (dμ/dν)` approach the supremum. -/
theorem klDiv_le_iSup_of_absolutelyContinuous (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    klDiv μ ν ≤ ⨆ (f : α → ℝ) (_ : Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C),
      ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)) := by
  set S := ⨆ (f : α → ℝ) (_ : Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C),
      ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)) with hS_def
  have hρm : Measurable fun x => (μ.rnDeriv ν x).toReal :=
    (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hfm : ∀ k : ℕ, Measurable fun x => clampLog k (μ.rnDeriv ν x).toReal :=
    fun k => (measurable_clampLog k).comp hρm
  have hfb : ∀ (k : ℕ) x, |clampLog k (μ.rnDeriv ν x).toReal| ≤ k :=
    fun k x => abs_clampLog_le (Nat.cast_nonneg k) _
  have hgm : ∀ k : ℕ, Measurable fun x => (μ.rnDeriv ν x).toReal *
      clampLog k (μ.rnDeriv ν x).toReal - exp (clampLog k (μ.rnDeriv ν x).toReal) + 1 :=
    fun k => ((hρm.mul (hfm k)).sub (hfm k).exp).add_const 1
  have hstep : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv ν x).toReal *
      clampLog k (μ.rnDeriv ν x).toReal - exp (clampLog k (μ.rnDeriv ν x).toReal) + 1) ∂ν
        ≤ S := by
    intro k
    have hfμ := (integrable_of_bounded (μ := μ) (hfm k) (hfb k)).1
    have hexp := (integrable_of_bounded (μ := ν) (hfm k) (hfb k)).2
    have hρf : Integrable (fun x => (μ.rnDeriv ν x).toReal *
        clampLog k (μ.rnDeriv ν x).toReal) ν :=
      (integrable_toReal_rnDeriv_mul_iff hμν).2 hfμ
    have hint : Integrable (fun x => (μ.rnDeriv ν x).toReal *
        clampLog k (μ.rnDeriv ν x).toReal - exp (clampLog k (μ.rnDeriv ν x).toReal) + 1) ν :=
      (hρf.sub hexp).add (integrable_const (1 : ℝ))
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun x => clampLog_gain_nonneg (Nat.cast_nonneg k) ENNReal.toReal_nonneg)]
    refine le_iSup₂_of_le (fun x => clampLog k (μ.rnDeriv ν x).toReal)
      ⟨hfm k, k, hfb k⟩ (ENNReal.ofReal_le_ofReal ?_)
    have hsub : Integrable (fun x => (μ.rnDeriv ν x).toReal *
        clampLog k (μ.rnDeriv ν x).toReal - exp (clampLog k (μ.rnDeriv ν x).toReal)) ν :=
      hρf.sub hexp
    beta_reduce
    rw [integral_add hsub (integrable_const _), integral_sub hρf hexp,
      integral_toReal_rnDeriv_mul hμν]
    have hpos := integral_exp_pos (μ := ν) hexp
    have hlog := log_le_sub_one_of_pos hpos
    simp only [integral_const, probReal_univ, one_smul]
    linarith
  rw [klDiv_eq_lintegral_klFun_of_ac hμν]
  calc ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν
      = ∫⁻ x, liminf (fun k : ℕ => ENNReal.ofReal ((μ.rnDeriv ν x).toReal *
          clampLog k (μ.rnDeriv ν x).toReal - exp (clampLog k (μ.rnDeriv ν x).toReal) + 1))
          atTop ∂ν := by
        refine lintegral_congr fun x => ?_
        exact (((ENNReal.continuous_ofReal.tendsto _).comp
          (tendsto_clampLog_gain ENNReal.toReal_nonneg)).liminf_eq).symm
    _ ≤ liminf (fun k : ℕ => ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv ν x).toReal *
          clampLog k (μ.rnDeriv ν x).toReal - exp (clampLog k (μ.rnDeriv ν x).toReal) + 1)
          ∂ν) atTop :=
        lintegral_liminf_le fun k => (hgm k).ennreal_ofReal
    _ ≤ S := by
        refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
        obtain ⟨k, hk⟩ := hb.exists
        exact hk.trans (hstep k)

/-- **Donsker–Varadhan variational formula.** For probability measures `μ`, `ν`,
`KL(μ ‖ ν) = sup_f (∫ f dμ - log ∫ exp f dν)⁺`, the supremum being over bounded measurable
`f : α → ℝ` (the positive part comes from `ENNReal.ofReal`).

Source: S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University,
Spring 2010, Section 3, Lemma 1.2 in the notes' numbering
(https://math.nyu.edu/~varadhan/LDP/Spring2010.3.pdf). -/
theorem klDiv_eq_iSup {α : Type*} {mα : MeasurableSpace α} (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv μ ν = ⨆ (f : α → ℝ) (_ : Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C),
      ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)) := by
  refine le_antisymm ?_ (iSup₂_le fun f ⟨hf, C, hC⟩ =>
    ofReal_integral_sub_log_integral_exp_le_klDiv hf hC)
  by_cases hμν : μ ≪ ν
  · exact klDiv_le_iSup_of_absolutelyContinuous μ ν hμν
  · rw [iSup_eq_top_of_not_absolutelyContinuous μ ν hμν]
    exact le_top

end MathlibExt.InformationTheory.DonskerVaradhan
