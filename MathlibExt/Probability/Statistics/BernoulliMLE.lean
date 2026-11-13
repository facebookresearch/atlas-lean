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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import MathlibExt.InformationTheory.FiniteEntropy
public import MathlibExt.Probability.Statistics.Sufficiency.BernoulliSample

/-!
# Bernoulli likelihood is maximized at the sample proportion

For a nonempty binary sample, the Bernoulli likelihood at any
`θ ∈ [0, 1]` is at most the likelihood at the sample proportion, with
explicit boundary cases (all successes: likelihood `θ ^ n`,
proportion `1`; no successes: likelihood `(1 - θ) ^ n`, proportion
`0`). With both outcomes present the sample proportion is the unique
maximizer. The proof goes through a Bernoulli bridge to the Atlas
Gibbs inequality (`shannonEntropy_le_crossEntropy`) for the empirical
PMF on `Bool` against the Bernoulli(θ) PMF: the log-likelihood is
`-(n log 2)` times the cross-entropy, so Gibbs gives the comparison,
and the equality case (`crossEntropy_eq_shannonEntropy_iff`) gives
uniqueness. Boundary cases (all successes / no successes, `θ ∈ {0, 1}`)
are by direct computation. (Atlas roadmap ST09.T01.)

The same results hold for the Atlas Bernoulli model `Sufficiency.bernoulliFamily n`, the
normalized density family on `Fin n → Bool` indexed by `Set.Icc (0 : ℝ) 1`: its density at
a sample is the likelihood above (`bernoulliFamily_dens_eq`), so the sample proportion
maximizes it (`bernoulliFamily_dens_isMaxOn`), strictly when both outcomes are present
(`bernoulliFamily_dens_lt_of_ne`, `bernoulliFamily_dens_isMaxOn_iff`).
-/

@[expose] public section

open Finset

open scoped ENNReal

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

private theorem div_card_le_one {k n : ℕ} (hkn : k ≤ n) : (k : ℝ) / n ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn0)]
    exact_mod_cast hkn

private noncomputable def empPMF (k n : ℕ) (hkn : k ≤ n) : PMF Bool :=
  PMF.ofFintype (fun b =>
    bif b then ENNReal.ofReal ((k : ℝ) / n) else ENNReal.ofReal (1 - (k : ℝ) / n)) (by
    have h0 : (0 : ℝ) ≤ (k : ℝ) / n :=
      div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg n)
    have h1 : (k : ℝ) / n ≤ 1 := div_card_le_one hkn
    calc (∑ b, bif b then ENNReal.ofReal ((k : ℝ) / n)
            else ENNReal.ofReal (1 - (k : ℝ) / n))
        = ENNReal.ofReal ((k : ℝ) / n) + ENNReal.ofReal (1 - (k : ℝ) / n) :=
          Fintype.sum_bool _
      _ = ENNReal.ofReal (((k : ℝ) / n) + (1 - (k : ℝ) / n)) :=
          (ENNReal.ofReal_add h0 (sub_nonneg.mpr h1)).symm
      _ = 1 := by rw [add_sub_cancel]; exact ENNReal.ofReal_one)

private theorem empPMF_true {k n : ℕ} (hkn : k ≤ n) :
    empPMF k n hkn true = ENNReal.ofReal ((k : ℝ) / n) := rfl

private theorem empPMF_false {k n : ℕ} (hkn : k ≤ n) :
    empPMF k n hkn false = ENNReal.ofReal (1 - (k : ℝ) / n) := rfl

private theorem bernoulli_true_eq (q : NNReal) (h : q ≤ 1) :
    PMF.bernoulli q h true = ENNReal.ofReal (q : ℝ) := by
  have hb : (bif true then q else 1 - q) = q := by simp
  rw [PMF.bernoulli_apply, hb, ← ENNReal.ofReal_coe_nnreal]

private theorem bernoulli_false_eq (q : NNReal) (h : q ≤ 1) :
    PMF.bernoulli q h false = ENNReal.ofReal (1 - (q : ℝ)) := by
  have hb : (bif false then q else 1 - q) = 1 - q := by simp
  rw [PMF.bernoulli_apply, hb, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub h]
  simp

private theorem surprisal_ofReal_of_pos {t : ℝ} (ht0 : 0 < t) :
    InformationTheory.surprisal (ENNReal.ofReal t) = ENNReal.ofReal (-Real.logb 2 t) := by
  have hne : ENNReal.ofReal t ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr ht0
  unfold InformationTheory.surprisal
  rw [ite_eq_right hne, ENNReal.toReal_ofReal ht0.le]

private theorem empPMF_eq_bernoulli {k n : ℕ} (hkn : k ≤ n) (q : NNReal) (h : q ≤ 1)
    (hq : (q : ℝ) = (k : ℝ) / n) : empPMF k n hkn = PMF.bernoulli q h := by
  apply PMF.ext
  intro b
  cases b
  · rw [empPMF_false, bernoulli_false_eq, hq]
  · rw [empPMF_true, bernoulli_true_eq, hq]

private theorem crossEntropy_emp_bernoulli_eq {k n : ℕ} (hkn : k ≤ n)
    (q : NNReal) (h : q ≤ 1) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    InformationTheory.crossEntropy (empPMF k n hkn) (PMF.bernoulli q h)
      = ENNReal.ofReal ((k : ℝ) / n) * ENNReal.ofReal (-Real.logb 2 (q : ℝ))
        + ENNReal.ofReal (1 - (k : ℝ) / n) * ENNReal.ofReal (-Real.logb 2 (1 - (q : ℝ))) := by
  unfold InformationTheory.crossEntropy
  rw [Fintype.sum_bool, empPMF_true, empPMF_false, bernoulli_true_eq,
    bernoulli_false_eq, surprisal_ofReal_of_pos hq0,
    surprisal_ofReal_of_pos (sub_pos.mpr hq1)]

private theorem crossEntropy_emp_bernoulli_ne_top {k n : ℕ} (hkn : k ≤ n)
    (q : NNReal) (h : q ≤ 1) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    InformationTheory.crossEntropy (empPMF k n hkn) (PMF.bernoulli q h) ≠ ∞ := by
  have hCE := crossEntropy_emp_bernoulli_eq hkn q h hq0 hq1
  rw [hCE, ne_eq, ENNReal.add_eq_top, not_or]
  exact ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩

private theorem crossEntropy_toReal_emp_bernoulli {k n : ℕ} (hkn : k ≤ n)
    (q : NNReal) (h : q ≤ 1) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    (InformationTheory.crossEntropy (empPMF k n hkn) (PMF.bernoulli q h)).toReal
      = ((k : ℝ) / n) * (-Real.logb 2 (q : ℝ))
        + (1 - (k : ℝ) / n) * (-Real.logb 2 (1 - (q : ℝ))) := by
  have hCE := crossEntropy_emp_bernoulli_eq hkn q h hq0 hq1
  have hA : ENNReal.ofReal ((k : ℝ) / n) * ENNReal.ofReal (-Real.logb 2 (q : ℝ)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hB : ENNReal.ofReal (1 - (k : ℝ) / n) * ENNReal.ofReal (-Real.logb 2 (1 - (q : ℝ))) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hnn1 : (0 : ℝ) ≤ (k : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg n)
  have hnn2 : (0 : ℝ) ≤ 1 - (k : ℝ) / n := sub_nonneg.mpr (div_card_le_one hkn)
  have hnn3 : (0 : ℝ) ≤ -Real.logb 2 (q : ℝ) :=
    neg_nonneg.mpr (Real.logb_nonpos one_lt_two hq0.le hq1.le)
  have hnn4 : (0 : ℝ) ≤ -Real.logb 2 (1 - (q : ℝ)) :=
    neg_nonneg.mpr (Real.logb_nonpos one_lt_two (sub_pos.mpr hq1).le (by linarith [hq0.le]))
  rw [hCE, ENNReal.toReal_add hA hB, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hnn1, ENNReal.toReal_ofReal hnn3,
    ENNReal.toReal_ofReal hnn2, ENNReal.toReal_ofReal hnn4]

private theorem crossEntropy_emp_bernoulli_self {k n : ℕ} (hkn : k ≤ n)
    (q : NNReal) (h : q ≤ 1) (hq : (q : ℝ) = (k : ℝ) / n) :
    InformationTheory.crossEntropy (empPMF k n hkn) (PMF.bernoulli q h)
      = ENNReal.ofReal (InformationTheory.shannonEntropy (empPMF k n hkn)) := by
  rw [empPMF_eq_bernoulli hkn q h hq]
  exact (InformationTheory.crossEntropy_eq_shannonEntropy_iff _ _).mpr rfl

private theorem log_likelihood_bridge {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    (q : NNReal) (h : q ≤ 1) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    Real.log ((q : ℝ) ^ k * (1 - (q : ℝ)) ^ (n - k))
      = -((n : ℝ) * Real.log 2)
        * (InformationTheory.crossEntropy (empPMF k n hkn) (PMF.bernoulli q h)).toReal := by
  have h1q0 : (0 : ℝ) < 1 - (q : ℝ) := sub_pos.mpr hq1
  have e1 := log_likelihood_eq hkn _ (ne_of_gt hq0) (ne_of_gt h1q0)
  have e2 := crossEntropy_toReal_emp_bernoulli hkn q h hq0 hq1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hlb : ∀ x : ℝ, Real.logb 2 x = Real.log x / Real.log 2 := fun x => rfl
  rw [e1, e2, hlb, hlb]
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
          have hθle : (⟨θ, hθ0'.le⟩ : NNReal) ≤ 1 := by exact_mod_cast hθ1'.le
          have hphatle : (⟨(k : ℝ) / n, hphat0.le⟩ : NNReal) ≤ 1 := by
            exact_mod_cast hphat1.le
          have hq0θ : (0 : ℝ) < ((⟨θ, hθ0'.le⟩ : NNReal) : ℝ) := hθ0'
          have hq1θ : ((⟨θ, hθ0'.le⟩ : NNReal) : ℝ) < 1 := hθ1'
          have hq0p : (0 : ℝ) < ((⟨(k : ℝ) / n, hphat0.le⟩ : NNReal) : ℝ) := hphat0
          have hq1p : ((⟨(k : ℝ) / n, hphat0.le⟩ : NNReal) : ℝ) < 1 := hphat1
          have eθ : Real.log (θ ^ k * (1 - θ) ^ (n - k)) = -((n : ℝ) * Real.log 2)
              * (InformationTheory.crossEntropy (empPMF k n hkn)
                (PMF.bernoulli ⟨θ, hθ0'.le⟩ hθle)).toReal :=
            log_likelihood_bridge hn hkn _ hθle hq0θ hq1θ
          have ephat : Real.log (((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k))
              = -((n : ℝ) * Real.log 2)
              * (InformationTheory.crossEntropy (empPMF k n hkn)
                (PMF.bernoulli ⟨(k : ℝ) / n, hphat0.le⟩ hphatle)).toReal :=
            log_likelihood_bridge hn hkn _ hphatle hq0p hq1p
          have hGibbs := InformationTheory.shannonEntropy_le_crossEntropy
            (empPMF k n hkn) (PMF.bernoulli ⟨θ, hθ0'.le⟩ hθle)
          have hCEeq := crossEntropy_emp_bernoulli_self hkn _ hphatle rfl
          rw [← hCEeq] at hGibbs
          have hneθ := crossEntropy_emp_bernoulli_ne_top hkn _ hθle hq0θ hq1θ
          have hmono := ENNReal.toReal_mono hneθ hGibbs
          have hCneg : -((n : ℝ) * Real.log 2) < 0 :=
            neg_lt_zero.mpr (mul_pos hnR (Real.log_pos one_lt_two))
          rw [← Real.log_le_log_iff hLHS hRHS, eθ, ephat]
          exact mul_le_mul_of_nonpos_left hmono hCneg.le

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
      have hle : θ ^ k * (1 - θ) ^ (n - k)
          ≤ ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) :=
        pow_mul_pow_le_at_sample hn (le_of_lt hkn) hθ
      have hne' : θ ^ k * (1 - θ) ^ (n - k)
          ≠ ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) := by
        intro hcon
        have hθle : (⟨θ, hθ0'.le⟩ : NNReal) ≤ 1 := by exact_mod_cast hθ1'.le
        have hphatle : (⟨(k : ℝ) / n, hphat0.le⟩ : NNReal) ≤ 1 := by
          exact_mod_cast hphat1.le
        have hq0θ : (0 : ℝ) < ((⟨θ, hθ0'.le⟩ : NNReal) : ℝ) := hθ0'
        have hq1θ : ((⟨θ, hθ0'.le⟩ : NNReal) : ℝ) < 1 := hθ1'
        have hq0p : (0 : ℝ) < ((⟨(k : ℝ) / n, hphat0.le⟩ : NNReal) : ℝ) := hphat0
        have hq1p : ((⟨(k : ℝ) / n, hphat0.le⟩ : NNReal) : ℝ) < 1 := hphat1
        have eθ : Real.log (θ ^ k * (1 - θ) ^ (n - k)) = -((n : ℝ) * Real.log 2)
            * (InformationTheory.crossEntropy (empPMF k n (le_of_lt hkn))
              (PMF.bernoulli ⟨θ, hθ0'.le⟩ hθle)).toReal :=
          log_likelihood_bridge hn (le_of_lt hkn) _ hθle hq0θ hq1θ
        have ephat : Real.log (((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k))
            = -((n : ℝ) * Real.log 2)
            * (InformationTheory.crossEntropy (empPMF k n (le_of_lt hkn))
              (PMF.bernoulli ⟨(k : ℝ) / n, hphat0.le⟩ hphatle)).toReal :=
          log_likelihood_bridge hn (le_of_lt hkn) _ hphatle hq0p hq1p
        have hlogeq : Real.log (θ ^ k * (1 - θ) ^ (n - k))
            = Real.log (((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k)) := by
          rw [hcon]
        rw [eθ, ephat] at hlogeq
        have hCne : -((n : ℝ) * Real.log 2) ≠ 0 :=
          ne_of_lt (neg_lt_zero.mpr (mul_pos hnR (Real.log_pos one_lt_two)))
        have hToRealEq : (InformationTheory.crossEntropy (empPMF k n (le_of_lt hkn))
              (PMF.bernoulli ⟨θ, hθ0'.le⟩ hθle)).toReal
            = (InformationTheory.crossEntropy (empPMF k n (le_of_lt hkn))
              (PMF.bernoulli ⟨(k : ℝ) / n, hphat0.le⟩ hphatle)).toReal :=
          mul_left_cancel₀ hCne hlogeq
        have hneθ :=
          crossEntropy_emp_bernoulli_ne_top (le_of_lt hkn) _ hθle hq0θ hq1θ
        have hnep :=
          crossEntropy_emp_bernoulli_ne_top (le_of_lt hkn) _ hphatle hq0p hq1p
        have hCEθ := (ENNReal.ofReal_toReal hneθ).symm
        have hCEp := (ENNReal.ofReal_toReal hnep).symm
        have hCECE : InformationTheory.crossEntropy (empPMF k n (le_of_lt hkn))
              (PMF.bernoulli ⟨θ, hθ0'.le⟩ hθle)
            = InformationTheory.crossEntropy (empPMF k n (le_of_lt hkn))
              (PMF.bernoulli ⟨(k : ℝ) / n, hphat0.le⟩ hphatle) := by
          rw [hCEθ, hCEp, hToRealEq]
        have hCEeq := crossEntropy_emp_bernoulli_self (le_of_lt hkn) _ hphatle rfl
        have hGibbsEq : InformationTheory.crossEntropy (empPMF k n (le_of_lt hkn))
              (PMF.bernoulli ⟨θ, hθ0'.le⟩ hθle)
            = ENNReal.ofReal
              (InformationTheory.shannonEntropy (empPMF k n (le_of_lt hkn))) := by
          rw [hCECE]; exact hCEeq
        have hbern :=
          (InformationTheory.crossEntropy_eq_shannonEntropy_iff _ _).mp hGibbsEq
        have hemp := empPMF_eq_bernoulli (le_of_lt hkn) _ hphatle rfl
        have hbb : PMF.bernoulli ⟨θ, hθ0'.le⟩ hθle
            = PMF.bernoulli ⟨(k : ℝ) / n, hphat0.le⟩ hphatle :=
          hbern.trans hemp
        have htrue : PMF.bernoulli ⟨θ, hθ0'.le⟩ hθle true
            = PMF.bernoulli ⟨(k : ℝ) / n, hphat0.le⟩ hphatle true :=
          congrArg (fun P : PMF Bool => P true) hbb
        have h1 : PMF.bernoulli ⟨θ, hθ0'.le⟩ hθle true = ENNReal.ofReal θ :=
          bernoulli_true_eq _ _
        have h2 : PMF.bernoulli ⟨(k : ℝ) / n, hphat0.le⟩ hphatle true
            = ENNReal.ofReal ((k : ℝ) / n) :=
          bernoulli_true_eq _ _
        have hOfReal : ENNReal.ofReal θ = ENNReal.ofReal ((k : ℝ) / n) :=
          h1.symm.trans (htrue.trans h2)
        have hθeq : θ = (k : ℝ) / n :=
          (ENNReal.ofReal_eq_ofReal_iff hθ0'.le hphat0.le).mp hOfReal
        exact hne hθeq
      exact lt_of_le_of_ne hle hne'

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

/-! ### The Atlas Bernoulli model -/

/-- The sample proportion lies in `[0, 1]`. -/
theorem sampleProportion_mem_Icc {n : ℕ} (x : Fin n → Bool) :
    sampleProportion x ∈ Set.Icc (0 : ℝ) 1 := by
  have hkn : (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ n := by
    calc (Finset.univ.filter (fun i : Fin n => x i = true)).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), div_card_le_one hkn⟩

/-- The sample proportion as a parameter of `Sufficiency.bernoulliFamily`. -/
noncomputable def sampleProportionParam {n : ℕ} (x : Fin n → Bool) : Set.Icc (0 : ℝ) 1 :=
  ⟨sampleProportion x, sampleProportion_mem_Icc x⟩

/-- **Bridge to the Bernoulli model.** The density of `Sufficiency.bernoulliFamily n` at the
parameter `p` and the sample `x` is the likelihood `bernoulliLikelihood x p`. -/
theorem bernoulliFamily_dens_eq {n : ℕ} (p : Set.Icc (0 : ℝ) 1) (x : Fin n → Bool) :
    (Sufficiency.bernoulliFamily n).dens p x = ENNReal.ofReal (bernoulliLikelihood x p.1) := by
  have hcard : (Finset.univ.filter fun i : Fin n => x i = false).card =
      n - (Finset.univ.filter fun i : Fin n => x i = true).card := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => x i = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [bernoulliLikelihood_eq_pow, ← hcard]
  rfl

/-- **Bernoulli MLE in the model (ST09.T01).** For a nonempty sample `x`, the density of
`Sufficiency.bernoulliFamily n` at `x` is maximized over the parameter interval at the
sample proportion. -/
theorem bernoulliFamily_dens_isMaxOn {n : ℕ} (x : Fin n → Bool) (hn : 0 < n) :
    IsMaxOn (fun p => (Sufficiency.bernoulliFamily n).dens p x) Set.univ
      (sampleProportionParam x) :=
  isMaxOn_univ_iff.mpr fun p => by
    rw [bernoulliFamily_dens_eq, bernoulliFamily_dens_eq]
    exact ENNReal.ofReal_le_ofReal (bernoulliLikelihood_le x hn p.2)

/-- **Strict uniqueness in the model (ST09.T01).** When the sample contains both successes and
failures, every parameter other than the sample proportion has strictly smaller density at the
sample. -/
theorem bernoulliFamily_dens_lt_of_ne {n : ℕ} (x : Fin n → Bool) (hn : 0 < n)
    (hk0 : 0 < (Finset.univ.filter (fun i => x i = true)).card)
    (hkn : (Finset.univ.filter (fun i => x i = true)).card < n)
    {p : Set.Icc (0 : ℝ) 1} (hp : p ≠ sampleProportionParam x) :
    (Sufficiency.bernoulliFamily n).dens p x <
      (Sufficiency.bernoulliFamily n).dens (sampleProportionParam x) x := by
  rw [bernoulliFamily_dens_eq, bernoulliFamily_dens_eq]
  have hne : p.1 ≠ sampleProportion x := fun h => hp (Subtype.ext h)
  have hlt := bernoulliLikelihood_lt_of_ne x hn p.2 hk0 hkn hne
  have hnonneg : 0 ≤ bernoulliLikelihood x p.1 := by
    obtain ⟨h0, h1⟩ := p.2
    exact Finset.prod_nonneg fun i _ => by split_ifs <;> linarith
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hnonneg hlt)).mpr hlt

/-- When the sample contains both successes and failures, the sample proportion is the only
maximizer of the density of `Sufficiency.bernoulliFamily n` at the sample. -/
theorem bernoulliFamily_dens_isMaxOn_iff {n : ℕ} (x : Fin n → Bool) (hn : 0 < n)
    (hk0 : 0 < (Finset.univ.filter (fun i => x i = true)).card)
    (hkn : (Finset.univ.filter (fun i => x i = true)).card < n) (p : Set.Icc (0 : ℝ) 1) :
    IsMaxOn (fun q => (Sufficiency.bernoulliFamily n).dens q x) Set.univ p ↔
      p = sampleProportionParam x := by
  constructor
  · intro hmax
    by_contra hne
    exact absurd (isMaxOn_univ_iff.mp hmax (sampleProportionParam x))
      (not_le.mpr (bernoulliFamily_dens_lt_of_ne x hn hk0 hkn hne))
  · rintro rfl
    exact bernoulliFamily_dens_isMaxOn x hn

end MathlibExt.Probability.Statistics.BernoulliMLE
