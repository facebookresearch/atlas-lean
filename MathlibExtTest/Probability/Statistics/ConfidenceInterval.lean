/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.ConfidenceInterval
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi

/-!
# Confidence-interval consumers and boundaries

A real-valued fair coin and its canonical finite/infinite product measures
supply all independence, measurability, expectation and variance hypotheses.
The four-coin Hoeffding event is not certain: the all-zero atom has mass `1/16`
and is outside its interval. The numerical constants below are proved exactly.
Test theorems are named and private so every proof is retained for the trust audit.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace ConfidenceIntervalTest

private noncomputable def coin : Measure ℝ :=
  bernoulliMeasure 0 1 ⟨1 / 2, by norm_num⟩

private instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

private lemma coin_values : ∀ᵐ x ∂coin, x = 0 ∨ x = 1 := by
  rw [ae_iff]
  exact bernoulliMeasure_apply_of_notMem_of_notMem _ (by measurability) (by simp) (by simp)

private lemma coin_mean : (∫ x, x ∂coin) = 1 / 2 := by
  rw [coin, integral_bernoulliMeasure]
  norm_num

private lemma coin_memLp : MemLp (id : ℝ → ℝ) 2 coin := by
  apply (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
  exact integrable_bernoulliMeasure _ _ _ _

private lemma coin_variance : variance (id : ℝ → ℝ) coin = 1 / 4 := by
  rw [variance_eq_sub coin_memLp]
  change (∫ x : ℝ, x ^ 2 ∂coin) - (∫ x, x ∂coin) ^ 2 = 1 / 4
  rw [coin_mean, coin, integral_bernoulliMeasure]
  norm_num

private noncomputable def fourCoins : Measure (Fin 4 → ℝ) := Measure.pi (fun _ => coin)

private instance : IsProbabilityMeasure fourCoins := by unfold fourCoins; infer_instance

private lemma four_law (i : Fin 4) : HasLaw (fun ω : Fin 4 → ℝ => ω i) coin fourCoins :=
  (measurePreserving_eval (fun _ : Fin 4 => coin) i).hasLaw

private lemma four_indep : iIndepFun (fun i (ω : Fin 4 → ℝ) => ω i) fourCoins :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

private lemma four_coverage :
    1 / 2 ≤ fourCoins.real {ω | |(∑ i, ω i) / 4 - 1 / 2| ≤ Real.sqrt (Real.log 4 / 8)} := by
  have h := bernoulli_mean_hoeffding_ci (μ := fourCoins) (by norm_num : 0 < 4)
    (fun i ω => ω i) (1 / 2) (1 / 2) four_indep
    (fun i => (four_law i).aemeasurable)
    (fun i => ((four_law i).ae_iff (by measurability)).2 coin_values)
    (fun i => (four_law i).integral_eq.trans coin_mean) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- A fixed population mean belongs to the random CLOSED interval with the stated probability. -/
private theorem four_interval_coverage : 1 / 2 ≤ fourCoins.real {ω | (1 / 2 : ℝ) ∈
    Set.Icc ((∑ i, ω i) / 4 - Real.sqrt (Real.log 4 / 8))
      ((∑ i, ω i) / 4 + Real.sqrt (Real.log 4 / 8))} := by
  convert four_coverage using 2
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_sub_le_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private lemma four_radius_pos : 0 < Real.sqrt (Real.log 4 / 8) :=
  Real.sqrt_pos.2 (div_pos (Real.log_pos (by norm_num)) (by norm_num))

private lemma four_radius_lt_half : Real.sqrt (Real.log 4 / 8) < 1 / 2 := by
  have hlog : Real.log 4 < 2 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    have he : Real.log 4 = Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hs := Real.sq_sqrt (show 0 ≤ Real.log 4 / 8 by positivity)
  nlinarith [Real.sqrt_nonneg (Real.log 4 / 8)]

/-- The all-zero four-coin outcome is genuinely outside the coverage event. -/
private theorem zero_outside_coverage : (fun _ : Fin 4 => (0 : ℝ)) ∉
    {ω | |(∑ i, ω i) / 4 - 1 / 2| ≤ Real.sqrt (Real.log 4 / 8)} := by
  simpa using four_radius_lt_half.not_ge

private lemma four_zero_mass : fourCoins.real {fun _ : Fin 4 => (0 : ℝ)} = 1 / 16 := by
  simp only [fourCoins, measureReal_def, Measure.pi_singleton]
  have hzero : coin {(0 : ℝ)} = ENNReal.ofReal (1 / 2) := by
    rw [coin, bernoulliMeasure_apply_of_mem_of_notMem _ (by measurability) (by simp) (by norm_num)]
    simp only [ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal]
  simp_rw [hzero]
  norm_num

/-- Failure has positive probability, not merely an exceptional zero-mass point. -/
private theorem failure_probability_pos :
    0 < fourCoins.real {ω | Real.sqrt (Real.log 4 / 8) < |(∑ i, ω i) / 4 - 1 / 2|} := by
  have hsub : {fun _ : Fin 4 => (0 : ℝ)} ⊆
      {ω | Real.sqrt (Real.log 4 / 8) < |(∑ i, ω i) / 4 - 1 / 2|} := by
    intro ω hω
    rcases Set.mem_singleton_iff.1 hω with rfl
    simpa using four_radius_lt_half
  have h := measureReal_mono (μ := fourCoins) hsub
  rw [four_zero_mass] at h
  linarith

private noncomputable def coins : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ => coin)

private instance : IsProbabilityMeasure coins := by unfold coins; infer_instance

private lemma sample_law (i : ℕ) : HasLaw (fun ω : ℕ → ℝ => ω i) coin coins :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => coin) i).hasLaw

private lemma samples_indep : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) coins :=
  iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)

private lemma samples_ident (i : ℕ) :
    IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω => ω 0) coins coins :=
  (sample_law i).identDistrib (sample_law 0)

private lemma sample_variance : variance (fun ω : ℕ → ℝ => ω 0) coins = 1 / 4 := by
  rw [((sample_law 0).identDistrib (HasLaw.id (μ := coin))).variance_eq, coin_variance]

private lemma iid_coverage :
    1 / 2 ≤ coins.real {ω | |(∑ i ∈ Finset.range 4, ω i) / 4 - 1 / 2| < Real.sqrt (1 / 8)} := by
  have h := sample_mean_chebyshev_ci (μ := coins) (fun i ω => ω i) samples_indep samples_ident
    ((sample_law 0).memLp coin_memLp) (n := 4) (by norm_num) (v := 1 / 4) (α := 1 / 2)
    (by norm_num) (by rw [sample_variance]) (by norm_num)
  rw [(sample_law 0).integral_eq, coin_mean] at h
  norm_num at h ⊢
  exact h

/-- A fixed population mean belongs to the random OPEN interval. -/
private theorem iid_interval_coverage : 1 / 2 ≤ coins.real {ω | (1 / 2 : ℝ) ∈
    Set.Ioo ((∑ i ∈ Finset.range 4, ω i) / 4 - Real.sqrt (1 / 8))
      ((∑ i ∈ Finset.range 4, ω i) / 4 + Real.sqrt (1 / 8))} := by
  convert iid_coverage using 2
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo, abs_sub_lt_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private lemma constant_indep : iIndepFun (fun (_ : ℕ) (_ : ℕ → ℝ) => (1 : ℝ)) coins :=
  samples_indep.comp (fun _ _ => (1 : ℝ)) (fun _ => measurable_const)

/-- The constant Bernoulli family discharges every premise, for every positive sample size. -/
private theorem constant_coverage_lower_bound {n : ℕ} (hn : 0 < n) :
    1 - (1 / 2 : ℝ) ≤ coins.real {_ω | |(∑ _i : Fin n, (1 : ℝ)) / n - 1| ≤
      Real.sqrt (Real.log (2 / (1 / 2)) / (2 * n))} := by
  exact bernoulli_mean_hoeffding_ci hn (fun _ _ => 1) 1 (1 / 2)
    (.precomp Fin.val_injective constant_indep) (fun _ => aemeasurable_const)
    (fun _ => Filter.Eventually.of_forall (fun _ => Or.inr rfl))
    (fun _ => by simp) (by norm_num) (by norm_num)

/-- Constant-family coverage is exactly one, not just the lower confidence bound. -/
private theorem constant_coverage_one {n : ℕ} (hn : 0 < n) :
    coins.real {_ω | |(∑ _i : Fin n, (1 : ℝ)) / n - 1| ≤
      Real.sqrt (Real.log (2 / (1 / 2)) / (2 * n))} = 1 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, div_self hnR, sub_self, abs_zero, Real.sqrt_nonneg, Set.ofPred_true, probReal_univ]

/-- A conventional meaningful alpha gives a strictly positive radius. -/
private theorem hoeffding_radius_pos {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    0 < Real.sqrt (Real.log (2 / α) / (2 * n)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact Real.sqrt_pos.2 (div_pos
    (Real.log_pos ((lt_div_iff₀ hα).2 (by linarith))) (by positivity))

/-- At alpha=2 the radius vanishes, but the requested lower bound is nonpositive. -/
private theorem alpha_two_vacuous : Real.sqrt (Real.log (2 / (2 : ℝ)) / (2 * 4)) = 0 ∧
    1 - (2 : ℝ) ≤ fourCoins.real {ω | |(∑ i, ω i) / 4 - 1 / 2| ≤ 0} := by
  constructor
  · simp
  · exact le_trans (by norm_num) measureReal_nonneg

/-- Zero is a true variance bound for a constant sample, but its OPEN zero-radius interval is empty. -/
private theorem zero_variance_open_failure : variance (fun _ : ℕ → ℝ => (1 : ℝ)) coins = 0 ∧
    ¬ (1 - (1 / 2 : ℝ) ≤ coins.real {_ω | |(∑ _i ∈ Finset.range 1, (1 : ℝ)) / 1 - 1| <
      Real.sqrt ((0 : ℝ) / (1 * (1 / 2)))}) := by
  constructor
  · rw [variance_eq_integral aemeasurable_const]
    simp
  · norm_num

/-- Open and closed intervals genuinely disagree at their endpoints. -/
private theorem endpoint_membership : (1 / 2 : ℝ) ∈ Set.Icc (0 - 1 / 2) (0 + 1 / 2) ∧
    (1 / 2 : ℝ) ∉ Set.Ioo (0 - 1 / 2) (0 + 1 / 2) := by norm_num

/-- The nondegenerate IID fixture has strictly positive population variance. -/
private theorem iid_variance_pos : 0 < variance (fun ω : ℕ → ℝ => ω 0) coins := by
  rw [sample_variance]
  norm_num

/-- The four-coin radius is positive and smaller than the endpoint estimation error. -/
private theorem four_radius_bounds : 0 < Real.sqrt (Real.log 4 / 8) ∧ Real.sqrt (Real.log 4 / 8) < 1 / 2 :=
  ⟨four_radius_pos, four_radius_lt_half⟩

/-- Omitting the deterministic variance bound can give zero coverage even for one fair coin. -/
private theorem understated_variance_failure : (1 / 16 : ℝ) < variance (fun ω : ℕ → ℝ => ω 0) coins ∧
    ¬ (1 - (1 / 2 : ℝ) ≤ coins.real {ω | |(∑ i ∈ Finset.range 1, ω i) / 1 - 1 / 2| <
      Real.sqrt ((1 / 16 : ℝ) / (1 * (1 / 2)))}) := by
  have hr : Real.sqrt (1 / 8 : ℝ) < 1 / 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith [Real.sqrt_nonneg (1 / 8 : ℝ)]
  constructor
  · rw [sample_variance]; norm_num
  · have hev : {ω : ℕ → ℝ | |ω 0 - 1 / 2| < Real.sqrt (1 / 8)} =ᵐ[coins] ∅ := by
      filter_upwards [((sample_law 0).ae_iff (by measurability)).2 coin_values] with ω hω
      have herr : |ω 0 - 1 / 2| = (1 / 2 : ℝ) := by
        rcases hω with hω | hω <;> norm_num [hω]
      apply propext
      change (|ω 0 - 1 / 2| < Real.sqrt (1 / 8)) ↔ False
      rw [herr]
      exact iff_false_intro (not_lt.mpr hr.le)
    have hm := measureReal_congr hev
    norm_num at hm ⊢
    linarith

/-- Empty families meet the other Hoeffding premises; nonemptiness cannot be omitted. -/
private theorem empty_sample_failure : let X : Fin 0 → (ℕ → ℝ) → ℝ := fun _ _ => 1
    iIndepFun X coins ∧ (∀ i, AEMeasurable (X i) coins) ∧
      (∀ i, ∀ᵐ ω ∂coins, X i ω = 0 ∨ X i ω = 1) ∧
      (∀ i, ∫ ω, X i ω ∂coins = 1) ∧
      ¬ (1 - (1 / 2 : ℝ) ≤ coins.real {ω | |(∑ i, X i ω) / 0 - 1| ≤
        Real.sqrt (Real.log (2 / (1 / 2)) / (2 * 0))}) := by
  refine ⟨.precomp Fin.val_injective constant_indep, fun _ => aemeasurable_const,
    fun _ => Filter.Eventually.of_forall (fun _ => Or.inr rfl), fun _ => by simp, ?_⟩
  norm_num

end ConfidenceIntervalTest
