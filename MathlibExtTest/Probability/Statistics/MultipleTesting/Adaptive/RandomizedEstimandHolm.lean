/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimandHolm
public import MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand

/-!
# Tests for Holm, BH under PRDS and Benjamini–Yekutieli on zero-ATE endpoints

* The randomized trial of the `RandomizedEstimand` tests (four fair coins, endpoint `0` with ATE
  `0`, endpoint `1` with ATE `2`, `ateNulls = {0}`) is reused. Besides its independent p-values,
  a **comonotone** pair driven by the same coin is used: it is PRDS on the causal nulls but not
  independent, so the PRDS and Benjamini–Yekutieli theorems are exercised beyond independence.
  Every hypothesis of the Holm, BH-under-PRDS and BY theorems is discharged.
* The realized Holm rejection set on the trial is computed.
* The positivity-failure boundary: Holm FWER `1 > 1/20`; BH under PRDS with PRDS holding has FDR
  `1 > 1/20`; Benjamini–Yekutieli FDR `1 > 1/20`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Statistics.MultipleTesting
  MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimandHolm

/-! ### Comonotone p-values on the trial -/

/-- Comonotone p-values: both driven by coin `2`. The null one has law `pv0` (valid), the
non-null one is `1/100` or `1`. -/
noncomputable def pvalC : Fin 2 → (Fin 4 → Bool) → ℝ :=
  ![fun ω => pv0 (ω 2), fun ω => pv1 (ω 2)]

/-- The monotone map sending the null p-value to the whole vector. -/
noncomputable def coMap : ℝ → Fin 2 → ℝ := fun x => ![x, if x < 1 then 1 / 100 else 1]

lemma monotone_coMap : Monotone coMap := by
  intro x y hxy j
  fin_cases j
  · simpa [coMap] using hxy
  · simp only [coMap, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    split_ifs with hx hy hy <;> norm_num
    exact absurd (hxy.trans_lt hy) hx

lemma pvalC_eq_coMap (ω : Fin 4 → Bool) : (fun j => pvalC j ω) = coMap (pvalC 0 ω) := by
  funext j
  fin_cases j
  · rfl
  · cases h : ω 2 <;> norm_num [pvalC, coMap, pv0, pv1, h]

/-- The comonotone p-values are PRDS on the causal nulls `{0}`. -/
lemma isPRDSOn_pvalC : IsPRDSOn trial pvalC (ateNulls trial y0 y1) := by
  refine isPRDSOn_of_monotone_comp _ _ (fun _ => Measurable.of_discrete) _ fun i hi => ?_
  rw [ateNulls_trial, Finset.mem_singleton] at hi
  subst hi
  exact ⟨coMap, monotone_coMap, pvalC_eq_coMap⟩

/-- The comonotone p-values are **not** independent: both are small exactly when coin `2` shows
`true`, so `P(p₀ ≤ 1/2, p₁ ≤ 1/100) = 1/2 ≠ 1/4`. -/
lemma not_indepFun_pvalC : ¬ IndepFun (pvalC 0) (pvalC 1) trial := by
  intro h
  have hm := h.measure_inter_preimage_eq_mul (Set.Iic (1 / 2)) (Set.Iic (1 / 100))
    measurableSet_Iic measurableSet_Iic
  have h0 : pvalC 0 ⁻¹' Set.Iic (1 / 2) = {ω | ω 2 ∈ ({true} : Set Bool)} := by
    ext ω; cases h : ω 2 <;> norm_num [pvalC, pv0, h]
  have h1 : pvalC 1 ⁻¹' Set.Iic (1 / 100) = {ω | ω 2 ∈ ({true} : Set Bool)} := by
    ext ω; cases h : ω 2 <;> norm_num [pvalC, pv1, h]
  rw [h0, h1, Set.inter_self, trial_preimage_coord, coin_apply_singleton] at hm
  have : (2⁻¹ : ENNReal) = 2⁻¹ * 2⁻¹ := hm
  rw [← ENNReal.mul_inv (by simp) (by simp)] at this
  norm_num at this

lemma isValidPValue_pvalC_zero : IsValidPValue trial (pvalC 0) := by
  have : pvalC 0 = pval 0 := rfl
  rw [this]
  exact isValidPValue_pval_zero

/-- The comonotone p-values are calibrated for the observed-data IPW null. -/
lemma isIPWNullCalibrated_pvalC :
    IsIPWNullCalibrated trial treated (fun _ => ())
      (fun j => observed treated (y0 j) (y1 j)) pvalC := by
  rintro j ⟨_, hj⟩
  fin_cases j
  · exact isValidPValue_pvalC_zero
  · rw [ipwContrast_trial] at hj
    norm_num [eff] at hj

lemma trial_real_treated_pos : 0 < trial.real treated := by
  rw [trial_real_treated]; norm_num

lemma trial_real_treated_lt_one : trial.real treated < 1 := by
  rw [trial_real_treated]; norm_num

/-! ### Non-vacuity: every hypothesis discharged -/

/-- **Holm (randomized trial, dependent p-values)**: FWER over `ateNulls = {0}` at most `α`. -/
example {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    trial {ω | (holmRejections α (fun i => pvalC i ω) ∩ ateNulls trial y0 y1).Nonempty} ≤
      ENNReal.ofReal α :=
  measure_holm_ateNulls_familywiseError_le_of_indep measurableSet_treated trial_real_treated_pos
    trial_real_treated_lt_one (fun _ _ => Measurable.of_discrete)
    (fun _ _ => Measurable.of_discrete) (fun _ _ => Integrable.of_finite)
    (fun _ _ => Integrable.of_finite) (fun j _ => indep_treated j) isIPWNullCalibrated_pvalC
    hα₀ hα₁

/-- **Holm (general identification theorem)**, with strong ignorability supplied directly. -/
example {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    trial {ω | (holmRejections α (fun i => pval i ω) ∩ ateNulls trial y0 y1).Nonempty} ≤
      ENNReal.ofReal α :=
  measure_holm_ateNulls_familywiseError_le measurableSet_treated measurable_const
    (fun _ _ => Measurable.of_discrete) (fun _ _ => Measurable.of_discrete)
    (fun _ _ => Integrable.of_finite) (fun _ _ => Integrable.of_finite)
    (fun j _ => stronglyIgnorable_trial j) isIPWNullCalibrated_trial hα₀ hα₁

/-- **BH under PRDS (randomized trial, comonotone p-values that are not independent)**: FDR over
`ateNulls = {0}` at most `q / 2`. -/
example (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls trial y0 y1)
      (bhRejections q fun i => pvalC i ω) ∂trial ≤ q / 2 := by
  have h := integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_isPRDSOn_of_indep
    measurableSet_treated trial_real_treated_pos trial_real_treated_lt_one
    (fun _ _ => Measurable.of_discrete) (fun _ _ => Measurable.of_discrete)
    (fun _ _ => Integrable.of_finite) (fun _ _ => Integrable.of_finite)
    (fun j _ => indep_treated j) (fun _ => Measurable.of_discrete) isPRDSOn_pvalC
    isIPWNullCalibrated_pvalC q hq₀ hq₁
  rw [ateNulls_trial] at h ⊢
  simpa using h

/-- **BH under PRDS with independent p-values** (`isPRDSOn_of_iIndepFun`), general theorem. -/
example (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls trial y0 y1)
      (bhRejections q fun i => pval i ω) ∂trial ≤ q * (ateNulls trial y0 y1).card / 2 :=
  integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_isPRDSOn measurableSet_treated
    measurable_const (fun _ _ => Measurable.of_discrete) (fun _ _ => Measurable.of_discrete)
    (fun _ _ => Integrable.of_finite) (fun _ _ => Integrable.of_finite)
    (fun j _ => stronglyIgnorable_trial j) (fun _ => Measurable.of_discrete)
    (isPRDSOn_of_iIndepFun _ _ (fun _ => Measurable.of_discrete) iIndepFun_pval _)
    isIPWNullCalibrated_trial q hq₀ hq₁

/-- **Benjamini–Yekutieli (randomized trial, dependent p-values)**: BH at level `q / H_2`,
`H_2 = 3/2`, has FDR over `ateNulls = {0}` at most `q / 2`. -/
example (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls trial y0 y1)
      (bhRejections (q / (3 / 2)) fun i => pvalC i ω) ∂trial ≤ q / 2 := by
  have h := integral_falseDiscoveryProportion_byRejections_ateNulls_le_of_indep
    measurableSet_treated trial_real_treated_pos trial_real_treated_lt_one
    (fun _ _ => Measurable.of_discrete) (fun _ _ => Measurable.of_discrete)
    (fun _ _ => Integrable.of_finite) (fun _ _ => Integrable.of_finite)
    (fun j _ => indep_treated j) (fun _ => Measurable.of_discrete)
    isIPWNullCalibrated_pvalC q hq₀ hq₁
  have hH : (harmonic 2 : ℝ) = 3 / 2 := by
    norm_num [harmonic_succ]
  rw [ateNulls_trial] at h ⊢
  rw [hH] at h
  simpa using h

/-- **Benjamini–Yekutieli (general identification theorem)**, independent p-values. -/
example (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls trial y0 y1)
      (bhRejections (q / harmonic 2) fun i => pval i ω) ∂trial ≤
      q * (ateNulls trial y0 y1).card / 2 :=
  integral_falseDiscoveryProportion_byRejections_ateNulls_le measurableSet_treated
    measurable_const (fun _ _ => Measurable.of_discrete) (fun _ _ => Measurable.of_discrete)
    (fun _ _ => Integrable.of_finite) (fun _ _ => Integrable.of_finite)
    (fun j _ => stronglyIgnorable_trial j) (fun _ => Measurable.of_discrete)
    isIPWNullCalibrated_trial q hq₀ hq₁

/-! ### Realized Holm rejections on the trial -/

/-- At `α = 1/20` Holm rejects only the second of the p-values `(1/2, 1/100)`: `1/100 ≤ α/2`, then
`1/2 > α`. -/
lemma holmRejections_half_hundredth :
    holmRejections (1 / 20) (![1 / 2, 1 / 100] : Fin 2 → ℝ) = {1} := by
  have hnb : ∀ t : ℝ, 1 / 100 ≤ t → t < 1 / 2 →
      numBelow (![1 / 2, 1 / 100] : Fin 2 → ℝ) t = 1 := fun t h1 h2 => by
    rw [numBelow, show (Finset.univ.filter fun i => (![1 / 2, 1 / 100] : Fin 2 → ℝ) i ≤ t) = {1}
      by ext i; fin_cases i <;> norm_num <;> linarith]
    rfl
  have h1 : 1 ≤ holmIndex (1 / 20) (![1 / 2, 1 / 100] : Fin 2 → ℝ) := by
    refine le_holmIndex (by norm_num) fun k hk => ?_
    obtain rfl : k = 1 := le_antisymm (Finset.mem_Icc.1 hk).2 (Finset.mem_Icc.1 hk).1
    rw [hnb _ (by norm_num) (by norm_num)]
  have h2 : holmIndex (1 / 20) (![1 / 2, 1 / 100] : Fin 2 → ℝ) ≠ 2 := by
    intro h
    have := le_numBelow_of_le_holmIndex (α := 1 / 20) (p := ![1 / 2, 1 / 100]) (k := 2)
      (by norm_num) h.ge
    rw [hnb _ (by norm_num) (by norm_num)] at this
    omega
  have hidx : holmIndex (1 / 20) (![1 / 2, 1 / 100] : Fin 2 → ℝ) = 1 := by
    have := holmIndex_le (1 / 20) (![1 / 2, 1 / 100] : Fin 2 → ℝ)
    omega
  rw [holmRejections, hidx]
  ext i
  fin_cases i <;> norm_num

/-- When coins `2` and `3` both show `true`, the trial's p-values are `(1/2, 1/100)`, and at
`α = 1/20` Holm rejects only the non-null endpoint `1`, so no causal null is rejected. -/
example (ω : Fin 4 → Bool) (h2 : ω 2 = true) (h3 : ω 3 = true) :
    holmRejections (1 / 20) (fun i => pval i ω) = {1} := by
  have hp : (fun i => pval i ω) = (![1 / 2, 1 / 100] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> simp [pval, pv0, pv1, h2, h3]
  rw [hp, holmRejections_half_hundredth]

/-! ### Positivity failure -/

/-- Holm rejects the causal null of the positivity-failure example at every level `α ≥ 0`. -/
example : holmRejections 0 (fun _ : Fin 1 => (0 : ℝ)) = Finset.univ :=
  holmRejections_untreated le_rfl

/-- **The Holm conclusion fails without positivity**: FWER `1 > 1/20`. -/
example : ¬ (Measure.dirac () {_ω : Unit | (holmRejections (1 / 20) (fun _ => (0 : ℝ)) ∩
      ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome).Nonempty} ≤
      ENNReal.ofReal (1 / 20)) := by
  rw [measure_holm_familywiseError_untreated (by norm_num), not_le, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)

/-- **The BH-under-PRDS conclusion fails without positivity, with PRDS holding**: the always-reject
p-value is PRDS on the causal nulls, yet the FDR is `1 > 1/20 = q |ateNulls| / m`. -/
example : IsPRDSOn (Measure.dirac ()) (fun (_ : Fin 1) (_ : Unit) => (0 : ℝ))
      (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome) ∧
    ¬ (∫ _, falseDiscoveryProportion
      (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome)
      (bhRejections (1 / 20) fun _ => (0 : ℝ)) ∂(Measure.dirac ()) ≤
      1 / 20 * (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome).card /
        ((1 : ℕ) : ℝ)) := by
  refine ⟨isPRDSOn_untreated, ?_⟩
  rw [integral_falseDiscoveryProportion_bhRejections_untreated (by norm_num), ateNulls_untreated]
  norm_num

/-- **The Benjamini–Yekutieli conclusion fails without positivity**: at `q = 1/20` the FDR of BH
at level `q / H_1` is `1 > 1/20`. -/
example : ¬ (∫ _, falseDiscoveryProportion
      (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome)
      (bhRejections ((1 / 20) / harmonic 1) fun _ => (0 : ℝ)) ∂(Measure.dirac ()) ≤
      1 / 20 * (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome).card /
        ((1 : ℕ) : ℝ)) := by
  rw [integral_falseDiscoveryProportion_byRejections_untreated (by norm_num), ateNulls_untreated]
  norm_num

end MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimandHolm
