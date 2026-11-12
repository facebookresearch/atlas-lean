/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Bernoulli likelihood is maximized at the sample proportion

For a nonempty binary sample, the Bernoulli likelihood at any
`θ ∈ [0, 1]` is at most the likelihood at the sample proportion, with
explicit boundary cases (all successes: likelihood `θ ^ n`,
proportion `1`; no successes: likelihood `(1 - θ) ^ n`, proportion
`0`). With both outcomes present the sample proportion is the unique
maximizer. The proof goes through the log-likelihood and the scalar
inequality `log x ≤ x - 1` (Atlas roadmap ST09.T01).
-/

@[expose] public section


open Finset

namespace MathlibExt.Probability.Statistics.BernoulliMLE

/-- The Bernoulli likelihood of a binary sample `x` at success probability
`θ`: the product over observations of `θ` for successes and `1 - θ`
for failures. -/
noncomputable def bernoulliLikelihood {n : ℕ} (x : Fin n → Bool) (θ : ℝ) : ℝ :=
  ∏ i, if x i = true then θ else (1 - θ)

/-- The sample proportion: the fraction of successes in the sample. -/
noncomputable def sampleProportion {n : ℕ} (x : Fin n → Bool) : ℝ :=
  ((Finset.univ.filter (fun i => x i = true)).card : ℝ) / n

/-- The likelihood factors through the success count `k`: it is
`θ ^ k * (1 - θ) ^ (n - k)`. -/
theorem bernoulliLikelihood_eq_pow {n : ℕ} (x : Fin n → Bool) (θ : ℝ) :
    bernoulliLikelihood x θ = θ ^ (Finset.univ.filter (fun i => x i = true)).card *
      (1 - θ) ^ (n - (Finset.univ.filter (fun i => x i = true)).card) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n))
    (fun i => x i = true) (fun i => if x i = true then θ else (1 - θ))
  have h1 : (∏ i ∈ Finset.univ.filter (fun i : Fin n => x i = true),
      (if x i = true then θ else (1 - θ))) =
      θ ^ (Finset.univ.filter (fun i => x i = true)).card := by
    trans ∏ _i ∈ Finset.univ.filter (fun i : Fin n => x i = true), θ
    · apply Finset.prod_congr rfl
      intro i hi
      exact ite_eq_left (Finset.mem_filter.mp hi).2
    · exact Finset.prod_const θ
  have h2 : (∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬x i = true),
      (if x i = true then θ else (1 - θ))) =
      (1 - θ) ^ (Finset.univ.filter (fun i => ¬x i = true)).card := by
    trans ∏ _i ∈ Finset.univ.filter (fun i : Fin n => ¬x i = true), (1 - θ)
    · apply Finset.prod_congr rfl
      intro i hi
      exact ite_eq_right (Finset.mem_filter.mp hi).2
    · exact Finset.prod_const (1 - θ)
  have hcard : (Finset.univ.filter (fun i : Fin n => ¬x i = true)).card =
      n - (Finset.univ.filter (fun i => x i = true)).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i => x i = true)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h' : (Finset.univ.filter (fun i : Fin n => x i = true)).card +
        (Finset.univ.filter (fun i => ¬x i = true)).card = n := h
    omega
  unfold bernoulliLikelihood
  calc (∏ i, (if x i = true then θ else (1 - θ)))
      = (∏ i ∈ Finset.univ.filter (fun i => x i = true),
          (if x i = true then θ else (1 - θ))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬x i = true),
          (if x i = true then θ else (1 - θ))) := hsplit.symm
    _ = θ ^ (Finset.univ.filter (fun i => x i = true)).card *
        (1 - θ) ^ (n - (Finset.univ.filter (fun i => x i = true)).card) := by
        rw [h1, h2, hcard]

/-- All successes: the sample proportion is `1`. -/
theorem sampleProportion_eq_one_of_all_true {n : ℕ} (x : Fin n → Bool)
    (hn : 0 < n) (hx : ∀ i, x i = true) : sampleProportion x = 1 := by
  unfold sampleProportion
  have h : Finset.univ.filter (fun i : Fin n => x i = true) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    exact hx i
  rw [h, Finset.card_univ, Fintype.card_fin]
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  exact div_self hnne

/-- No successes: the sample proportion is `0`. -/
theorem sampleProportion_eq_zero_of_all_false {n : ℕ} (x : Fin n → Bool)
    (hx : ∀ i, x i = false) : sampleProportion x = 0 := by
  unfold sampleProportion
  have h : Finset.univ.filter (fun i : Fin n => x i = true) = ∅ := by
    apply Finset.filter_false_of_mem
    intro i _
    simp [hx i]
  rw [h]
  simp

/-- All successes: the likelihood is `θ ^ n`. -/
theorem bernoulliLikelihood_all_true {n : ℕ} (x : Fin n → Bool)
    (hx : ∀ i, x i = true) (θ : ℝ) : bernoulliLikelihood x θ = θ ^ n := by
  unfold bernoulliLikelihood
  trans ∏ _ : Fin n, θ
  · apply Finset.prod_congr rfl
    intro i _
    exact ite_eq_left (hx i)
  · simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- No successes: the likelihood is `(1 - θ) ^ n`. -/
theorem bernoulliLikelihood_all_false {n : ℕ} (x : Fin n → Bool)
    (hx : ∀ i, x i = false) (θ : ℝ) : bernoulliLikelihood x θ = (1 - θ) ^ n := by
  unfold bernoulliLikelihood
  trans ∏ _ : Fin n, (1 - θ)
  · apply Finset.prod_congr rfl
    intro i _
    exact ite_eq_right (by simp [hx i])
  · simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem log_likelihood_eq {n k : ℕ} (hkn : k ≤ n) (θ : ℝ) (hθ0 : θ ≠ 0)
    (h1θ : 1 - θ ≠ 0) :
    Real.log (θ ^ k * (1 - θ) ^ (n - k))
      = (k : ℝ) * Real.log θ + ((n : ℝ) - k) * Real.log (1 - θ) := by
  rw [Real.log_mul (pow_ne_zero k hθ0) (pow_ne_zero (n - k) h1θ),
    Real.log_pow, Real.log_pow, Nat.cast_sub hkn]

private theorem mle_key_identity {n k : ℕ} (hn : 0 < n) (hk0 : 0 < k) (hkn : k < n)
    (θ : ℝ) :
    (k : ℝ) * (θ / ((k : ℝ) / n) - 1)
      + ((n : ℝ) - k) * ((1 - θ) / (1 - (k : ℝ) / n) - 1) = 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hphat0 : (0 : ℝ) < (k : ℝ) / n := div_pos hkR hnR
  have hphat1 : (k : ℝ) / n < 1 := (div_lt_one hnR).mpr hknR
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hphatne : (k : ℝ) / n ≠ 0 := ne_of_gt hphat0
  have h1phatne : (1 : ℝ) - (k : ℝ) / n ≠ 0 := ne_of_gt (sub_pos.mpr hphat1)
  have hsubne : (n : ℝ) - k ≠ 0 := ne_of_gt (sub_pos.mpr hknR)
  field_simp
  ring

private theorem pow_mul_pow_le_at_sample {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    θ ^ k * (1 - θ) ^ (n - k)
      ≤ ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) := by
  obtain ⟨h0, h1⟩ := Set.mem_Icc.mp hθ
  by_cases hk0 : k = 0
  · rw [hk0]
    simp only [pow_zero, Nat.sub_zero, sub_zero, one_pow, mul_one, one_mul,
      zero_div, Nat.cast_zero]
    exact pow_le_one₀ (by linarith) (by linarith)
  · by_cases hkn' : k = n
    · rw [hkn']
      have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
      simp only [Nat.sub_self, pow_zero, mul_one]
      rw [div_self hnne, one_pow]
      exact pow_le_one₀ h0 h1
    · have hk0' : 0 < k := by omega
      have hkn'' : k < n := by omega
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk0'
      have hknR : (k : ℝ) < n := by exact_mod_cast hkn''
      have hphat0 : (0 : ℝ) < (k : ℝ) / n := div_pos hkR hnR
      have hphat1 : (k : ℝ) / n < 1 := (div_lt_one hnR).mpr hknR
      have h1phat0 : (0 : ℝ) < 1 - (k : ℝ) / n := sub_pos.mpr hphat1
      have hRHS : (0 : ℝ) < ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) :=
        mul_pos (pow_pos hphat0 k) (pow_pos h1phat0 _)
      have hnk : 0 < n - k := by omega
      by_cases hθ0 : θ = 0
      · rw [hθ0, zero_pow (ne_of_gt hk0'), zero_mul]
        exact le_of_lt hRHS
      · by_cases hθ1 : θ = 1
        · rw [hθ1, sub_self, zero_pow (ne_of_gt hnk), mul_zero]
          exact le_of_lt hRHS
        · have hθ0' : (0 : ℝ) < θ := lt_of_le_of_ne h0 (Ne.symm hθ0)
          have hθ1' : θ < 1 := lt_of_le_of_ne h1 hθ1
          have h1θ0 : (0 : ℝ) < 1 - θ := sub_pos.mpr hθ1'
          have hLHS : (0 : ℝ) < θ ^ k * (1 - θ) ^ (n - k) :=
            mul_pos (pow_pos hθ0' k) (pow_pos h1θ0 _)
          rw [← Real.log_le_log_iff hLHS hRHS]
          have e1 := log_likelihood_eq hkn θ (ne_of_gt hθ0') (ne_of_gt h1θ0)
          have e2 := log_likelihood_eq hkn ((k : ℝ) / n) (ne_of_gt hphat0)
            (ne_of_gt h1phat0)
          have b1 : Real.log (θ / ((k : ℝ) / n)) ≤ θ / ((k : ℝ) / n) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hθ0' hphat0)
          have b2 : Real.log ((1 - θ) / (1 - (k : ℝ) / n))
              ≤ (1 - θ) / (1 - (k : ℝ) / n) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos h1θ0 h1phat0)
          have g1 : (k : ℝ) * Real.log (θ / ((k : ℝ) / n))
              ≤ (k : ℝ) * (θ / ((k : ℝ) / n) - 1) :=
            mul_le_mul_of_nonneg_left b1 (le_of_lt hkR)
          have g2 : ((n : ℝ) - k) * Real.log ((1 - θ) / (1 - (k : ℝ) / n))
              ≤ ((n : ℝ) - k) * ((1 - θ) / (1 - (k : ℝ) / n) - 1) :=
            mul_le_mul_of_nonneg_left b2 (le_of_lt (sub_pos.mpr hknR))
          have hsum := mle_key_identity hn hk0' hkn'' θ
          have hle : (k : ℝ) * Real.log (θ / ((k : ℝ) / n))
              + ((n : ℝ) - k) * Real.log ((1 - θ) / (1 - (k : ℝ) / n)) ≤ 0 :=
            calc (k : ℝ) * Real.log (θ / ((k : ℝ) / n))
                  + ((n : ℝ) - k) * Real.log ((1 - θ) / (1 - (k : ℝ) / n))
                ≤ (k : ℝ) * (θ / ((k : ℝ) / n) - 1)
                  + ((n : ℝ) - k) * ((1 - θ) / (1 - (k : ℝ) / n) - 1) :=
                  add_le_add g1 g2
              _ = 0 := hsum
          rw [e1, e2]
          have hdiv1 : Real.log (θ / ((k : ℝ) / n))
              = Real.log θ - Real.log ((k : ℝ) / n) :=
            Real.log_div (ne_of_gt hθ0') (ne_of_gt hphat0)
          have hdiv2 : Real.log ((1 - θ) / (1 - (k : ℝ) / n))
              = Real.log (1 - θ) - Real.log (1 - (k : ℝ) / n) :=
            Real.log_div (ne_of_gt h1θ0) (ne_of_gt h1phat0)
          rw [hdiv1, hdiv2] at hle
          linarith [hle]

private theorem pow_mul_pow_lt_of_ne_at_sample {n k : ℕ} (hn : 0 < n)
    (hk0 : 0 < k) (hkn : k < n)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hne : θ ≠ (k : ℝ) / n) :
    θ ^ k * (1 - θ) ^ (n - k)
      < ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) := by
  obtain ⟨h0, h1⟩ := Set.mem_Icc.mp hθ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hphat0 : (0 : ℝ) < (k : ℝ) / n := div_pos hkR hnR
  have hphat1 : (k : ℝ) / n < 1 := (div_lt_one hnR).mpr hknR
  have h1phat0 : (0 : ℝ) < 1 - (k : ℝ) / n := sub_pos.mpr hphat1
  have hRHS : (0 : ℝ) < ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) :=
    mul_pos (pow_pos hphat0 k) (pow_pos h1phat0 _)
  have hnk : 0 < n - k := by omega
  by_cases hθ0 : θ = 0
  · rw [hθ0, zero_pow (ne_of_gt hk0), zero_mul]
    exact hRHS
  · by_cases hθ1 : θ = 1
    · rw [hθ1, sub_self, zero_pow (ne_of_gt hnk), mul_zero]
      exact hRHS
    · have hθ0' : (0 : ℝ) < θ := lt_of_le_of_ne h0 (Ne.symm hθ0)
      have hθ1' : θ < 1 := lt_of_le_of_ne h1 hθ1
      have h1θ0 : (0 : ℝ) < 1 - θ := sub_pos.mpr hθ1'
      have hLHS : (0 : ℝ) < θ ^ k * (1 - θ) ^ (n - k) :=
        mul_pos (pow_pos hθ0' k) (pow_pos h1θ0 _)
      rw [← Real.log_lt_log_iff hLHS hRHS]
      have e1 := log_likelihood_eq (le_of_lt hkn) θ (ne_of_gt hθ0')
        (ne_of_gt h1θ0)
      have e2 := log_likelihood_eq (le_of_lt hkn) ((k : ℝ) / n)
        (ne_of_gt hphat0) (ne_of_gt h1phat0)
      have htp1 : θ / ((k : ℝ) / n) ≠ 1 := by
        intro hcon
        apply hne
        exact (div_eq_one_iff_eq (ne_of_gt hphat0)).mp hcon
      have b1 : Real.log (θ / ((k : ℝ) / n)) < θ / ((k : ℝ) / n) - 1 :=
        Real.log_lt_sub_one_of_pos (div_pos hθ0' hphat0) htp1
      have b2 : Real.log ((1 - θ) / (1 - (k : ℝ) / n))
          ≤ (1 - θ) / (1 - (k : ℝ) / n) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos h1θ0 h1phat0)
      have g1 : (k : ℝ) * Real.log (θ / ((k : ℝ) / n))
          < (k : ℝ) * (θ / ((k : ℝ) / n) - 1) :=
        mul_lt_mul_of_pos_left b1 hkR
      have g2 : ((n : ℝ) - k) * Real.log ((1 - θ) / (1 - (k : ℝ) / n))
          ≤ ((n : ℝ) - k) * ((1 - θ) / (1 - (k : ℝ) / n) - 1) :=
        mul_le_mul_of_nonneg_left b2 (le_of_lt (sub_pos.mpr hknR))
      have hsum := mle_key_identity hn hk0 hkn θ
      have hlt : (k : ℝ) * Real.log (θ / ((k : ℝ) / n))
          + ((n : ℝ) - k) * Real.log ((1 - θ) / (1 - (k : ℝ) / n)) < 0 :=
        calc (k : ℝ) * Real.log (θ / ((k : ℝ) / n))
              + ((n : ℝ) - k) * Real.log ((1 - θ) / (1 - (k : ℝ) / n))
            < (k : ℝ) * (θ / ((k : ℝ) / n) - 1)
              + ((n : ℝ) - k) * ((1 - θ) / (1 - (k : ℝ) / n) - 1) :=
              add_lt_add_of_lt_of_le g1 g2
          _ = 0 := hsum
      rw [e1, e2]
      have hdiv1 : Real.log (θ / ((k : ℝ) / n))
          = Real.log θ - Real.log ((k : ℝ) / n) :=
        Real.log_div (ne_of_gt hθ0') (ne_of_gt hphat0)
      have hdiv2 : Real.log ((1 - θ) / (1 - (k : ℝ) / n))
          = Real.log (1 - θ) - Real.log (1 - (k : ℝ) / n) :=
        Real.log_div (ne_of_gt h1θ0) (ne_of_gt h1phat0)
      rw [hdiv1, hdiv2] at hlt
      linarith [hlt]

/-- **Bernoulli MLE (ST09.T01).** For a nonempty sample, the Bernoulli
likelihood at any `θ ∈ [0, 1]` is at most the likelihood at the sample
proportion: the sample proportion maximizes the likelihood. Boundary
cases are included: if there are no successes the proportion is `0`,
and if all observations succeed it is `1`. -/
theorem bernoulliLikelihood_le {n : ℕ} (x : Fin n → Bool) (hn : 0 < n)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    bernoulliLikelihood x θ ≤ bernoulliLikelihood x (sampleProportion x) := by
  have hkn : (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ n := by
    calc (Finset.univ.filter (fun i : Fin n => x i = true)).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  rw [bernoulliLikelihood_eq_pow x θ, bernoulliLikelihood_eq_pow x (sampleProportion x)]
  exact pow_mul_pow_le_at_sample hn hkn hθ

/-- **Uniqueness of the Bernoulli MLE (ST09.T01).** When the sample
contains both successes and failures, the sample proportion is the
unique maximizer of the likelihood on `[0, 1]`. -/
theorem bernoulliLikelihood_lt_of_ne {n : ℕ} (x : Fin n → Bool) (hn : 0 < n)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hk0 : 0 < (Finset.univ.filter (fun i => x i = true)).card)
    (hkn : (Finset.univ.filter (fun i => x i = true)).card < n)
    (hne : θ ≠ sampleProportion x) :
    bernoulliLikelihood x θ < bernoulliLikelihood x (sampleProportion x) := by
  rw [bernoulliLikelihood_eq_pow x θ, bernoulliLikelihood_eq_pow x (sampleProportion x)]
  exact pow_mul_pow_lt_of_ne_at_sample hn hk0 hkn hθ hne

end MathlibExt.Probability.Statistics.BernoulliMLE
