/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsup
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Bounds for Euler's totient and the sum of divisors
-/

namespace MetaMathlibExt

@[expose] public section

open Filter Finset

private lemma sum_inv_sq_le (s : Finset ℕ) (y : ℕ) (hy : 0 < y)
    (hs : ∀ n ∈ s, y < n) : ∑ n ∈ s, (n : ℝ)⁻¹ ^ 2 ≤ (y : ℝ)⁻¹ := by
  let b := max y (s.sup id)
  have hyb : y ≤ b := le_max_left ..
  have htel : ∀ b : ℕ, y ≤ b →
      ∑ n ∈ Ioc y b, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) = (y : ℝ)⁻¹ - (b : ℝ)⁻¹ := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [← insert_Ioc_right_eq_Ioc_add_one hb, sum_insert (by simp), ih]
      push_cast
      ring
  calc
    _ ≤ ∑ n ∈ s, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) := by
      refine sum_le_sum fun n hn ↦ ?_
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by linarith [hs n hn])
      have h : 0 < (n : ℝ) - 1 := by linarith
      have h' : 0 < (n : ℝ) := by linarith
      field_simp
      linarith
    _ ≤ ∑ n ∈ Ioc y b, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) := by
      refine sum_le_sum_of_subset_of_nonneg (fun n hn ↦ mem_Ioc.mpr
        ⟨hs n hn, (le_sup (f := id) hn).trans (le_max_right ..)⟩) ?_
      intro n hn _
      have hn1 : (1 : ℝ) < n := by
        exact_mod_cast (show 1 < n by linarith [(mem_Ioc.mp hn).1])
      exact sub_nonneg.mpr (inv_anti₀ (by linarith) (by linarith))
    _ ≤ _ := by rw [htel b hyb]; exact sub_le_self _ (by positivity)

private lemma prod_one_sub_inv_sq_ge (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (1 / 4 : ℝ) ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹ ^ 2) := by
  have hprod : ∀ t : Finset ℕ, (∀ p ∈ t, 2 ≤ p) →
      1 - ∑ p ∈ t, (p : ℝ)⁻¹ ^ 2 ≤ ∏ p ∈ t, (1 - (p : ℝ)⁻¹ ^ 2) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert p t hp ih =>
      intro h
      have ht : ∀ q ∈ t, 2 ≤ q := fun q hq ↦ h q (mem_insert_of_mem hq)
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast h p (mem_insert_self ..)
      have hpi : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
      have hpi' : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hc : 0 ≤ 1 - (p : ℝ)⁻¹ ^ 2 := by nlinarith
      rw [sum_insert hp, prod_insert hp]
      have hi := mul_le_mul_of_nonneg_left (ih ht) hc
      have hn : 0 ≤ ∑ q ∈ t, (q : ℝ)⁻¹ ^ 2 := sum_nonneg fun _ _ ↦ by positivity
      nlinarith [mul_nonneg (sq_nonneg (p : ℝ)⁻¹) hn]
  have hsum : ∑ p ∈ s, (p : ℝ)⁻¹ ^ 2 ≤ 3 / 4 := by
    have hbound := sum_inv_sq_le (s.erase 2) 2 (by decide)
      (fun p hp ↦ lt_of_le_of_ne (hs p (mem_erase.mp hp).2)
        (Ne.symm (mem_erase.mp hp).1))
    by_cases h : 2 ∈ s
    · rw [← sum_erase_add _ _ h]
      norm_num at hbound ⊢
      linarith
    · rw [erase_eq_of_notMem h] at hbound
      exact hbound.trans (by norm_num)
  exact (by linarith only [hsum] : (1 / 4 : ℝ) ≤ 1 - ∑ p ∈ s, (p : ℝ)⁻¹ ^ 2).trans
    (hprod s hs)

private lemma prime_power_factor_ge (p a : ℕ) (hp : 2 ≤ p) (ha : 0 < a) :
    1 - (p : ℝ)⁻¹ ^ 2 ≤
      ((p : ℝ) ^ (a - 1) * (p - 1)) * (∑ k ∈ range (a + 1), (p : ℝ) ^ k) /
        ((p : ℝ) ^ a) ^ 2 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hsum : (p : ℝ) ^ (b + 1) + (p : ℝ) ^ b ≤
      ∑ k ∈ range (b + 1 + 1), (p : ℝ) ^ k := by
    rw [sum_range_succ]
    have h := single_le_sum (fun k _ ↦ pow_nonneg hp0.le k)
      (mem_range.mpr (Nat.lt_succ_self b))
    linarith
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  calc
    _ = ((p : ℝ) ^ b * (p - 1)) * ((p : ℝ) ^ (b + 1) + (p : ℝ) ^ b) /
        ((p : ℝ) ^ (b + 1)) ^ 2 := by
      rw [pow_succ]
      field_simp
      ring
    _ ≤ _ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (mul_nonneg (pow_nonneg hp0.le b)
          (by linarith))) (sq_nonneg _)

private lemma totient_mul_sigma_ge (n : ℕ) (hn : 0 < n) :
    (1 / 4 : ℝ) ≤ (Nat.totient n : ℝ) / n * ((ArithmeticFunction.sigma 1 n : ℝ) / n) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hphi : (Nat.totient n : ℝ) =
      ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p - 1) * (p - 1) := by
    rw [Nat.totient_eq_prod_factorization hn0, Nat.prod_factorization_eq_prod_primeFactors,
      Nat.cast_prod]
    refine prod_congr rfl fun p hp ↦ ?_
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by
      linarith [(Nat.prime_of_mem_primeFactors hp).two_le])]
    norm_num
  have hsigma : (ArithmeticFunction.sigma 1 n : ℝ) =
      ∏ p ∈ n.primeFactors, ∑ k ∈ range (n.factorization p + 1), (p : ℝ) ^ k := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
    simp only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, mul_one]
  have hnorm : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn0
  have hprod := prod_one_sub_inv_sq_ge n.primeFactors
    (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le)
  calc
    _ ≤ ∏ p ∈ n.primeFactors,
        ((p : ℝ) ^ (n.factorization p - 1) * (p - 1)) *
          (∑ k ∈ range (n.factorization p + 1), (p : ℝ) ^ k) /
            ((p : ℝ) ^ n.factorization p) ^ 2 := by
      apply hprod.trans
      refine Finset.prod_le_prod₀ (fun p hp ↦ ?_) (fun p hp ↦ ?_)
      · have hp2 : (2 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hi := inv_le_one_of_one_le₀ (show (1 : ℝ) ≤ p by linarith)
        have hi0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
        nlinarith
      · apply prime_power_factor_ge p (n.factorization p)
          (Nat.prime_of_mem_primeFactors hp).two_le
        exact (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn0
          (Nat.dvd_of_mem_primeFactors hp)
    _ = _ := by
      rw [prod_div_distrib, prod_mul_distrib, prod_pow, ← hphi, ← hsigma, ← hnorm]
      ring

private lemma log_log_pos (n : ℕ) (hn : 3 ≤ n) : 0 < Real.log (Real.log n) := by
  apply Real.log_pos
  apply (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < n)).mpr
  have h := Real.exp_one_lt_three
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private lemma sigma_uniform_bound : ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 3 ≤ n →
    (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ D * Real.log (Real.log n) := by
  classical
  let F (n : ℕ) := (ArithmeticFunction.sigma 1 n : ℝ) /
    ((n : ℝ) * Real.log (Real.log n))
  let G := Real.exp Real.eulerMascheroniConstant + 1
  have hG : 0 < G := by dsimp [G]; positivity
  have hlim : limsup F atTop = Real.exp Real.eulerMascheroniConstant :=
    MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted.gronwall_sigma_limsup
  have hbd : ∃ B : ℝ, ∀ᶠ n in atTop, F n ≤ B := by
    by_contra! h
    have he : {B : ℝ | ∀ᶠ n in atTop, F n ≤ B} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun B hB ↦ h B (hB.mono fun _ hle ↦ not_lt_of_ge hle)
    rw [limsup, limsSup] at hlim
    simp only [eventually_map] at hlim
    rw [he, Real.sInf_empty] at hlim
    exact (Real.exp_ne_zero _ hlim.symm).elim
  have he := eventually_lt_of_limsup_lt (show limsup F atTop < G by
    rw [hlim]; dsimp [G]; linarith)
    (let ⟨_, h⟩ := hbd; isBoundedUnder_of_eventually_le h)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  let D := G + ∑ k ∈ range N, |F k|
  have hsum : 0 ≤ ∑ k ∈ range N, |F k| := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, fun n hn ↦ ?_⟩
  have hFn : F n ≤ D := by
    by_cases h : N ≤ n
    · exact (hN n h).le.trans (by dsimp [D]; linarith)
    · have hle := single_le_sum (fun k _ ↦ abs_nonneg (F k))
        (mem_range.mpr (lt_of_not_ge h))
      exact (le_abs_self (F n)).trans (hle.trans (by dsimp [D]; linarith))
  have hl := log_log_pos n hn
  dsimp [F] at hFn
  rw [div_mul_eq_div_div] at hFn
  exact (div_le_iff₀ hl).mp hFn

/-- **Lower bound for Euler's function and upper bound for the sum of divisors.** Let $\varphi$
be Euler's totient function and $\sigma(n)$ the sum of the positive divisors of $n$. There is a
constant $C > 0$ such that $\varphi(n)/n \ge C/\log\log n$ for every integer $n \ge 3$, and there
is a constant $C'$ such that $\sigma(n)/n \le C' \log\log n$ for every integer $n \ge 3$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 1 (`fq-2024-luca09162024rev2-lem-1`),
quoted from Hardy and Wright, Theorems 323, 328 and 329. -/
public theorem totient_div_gg_and_sigma_div_ll_log_log :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
        C / Real.log (Real.log n) ≤ (Nat.totient n : ℝ) / n) ∧
      ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
        (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ C * Real.log (Real.log n)
    := by
  obtain ⟨D, hD, hσ⟩ := sigma_uniform_bound
  refine ⟨⟨1 / (4 * D), by positivity, fun n hn ↦ ?_⟩, ⟨D, hσ⟩⟩
  have hn0 : 0 < n := by omega
  have hφ : 0 ≤ (Nat.totient n : ℝ) / n := by positivity
  have hl := log_log_pos n hn
  have hbridge := totient_mul_sigma_ge n hn0
  have hbound := mul_le_mul_of_nonneg_left (hσ n hn) hφ
  have hquarter : (1 / 4 : ℝ) ≤ (Nat.totient n : ℝ) / n *
      (D * Real.log (Real.log n)) := by
    exact hbridge.trans hbound
  apply (div_le_iff₀ hl).mpr
  apply (div_le_iff₀ (show 0 < 4 * D by positivity)).mpr
  nlinarith

end

end MetaMathlibExt
