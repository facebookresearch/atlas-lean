/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

section

namespace MetaMathlibExt

/-- Cross binomial identity for the Zagier reformulation. -/
private lemma binomial_cross (M a L1 L2 n : ℕ) (hN : L1 + L2 = M + a)
    (hn : n < M) :
    (L2.choose (M - n) : ℚ) * ((n + a).choose n : ℚ)
      = (L1.factorial * L2.factorial : ℚ) / ((a.factorial * M.factorial : ℚ))
        * ((M.choose n : ℚ) * (((n + a).choose L1 : ℚ))) := by
  by_cases h : n + a < L1
  · have h2 : L2 < M - n := by omega
    have h3 : L2.choose (M - n) = 0 := Nat.choose_eq_zero_of_lt h2
    have h4 : (n + a).choose L1 = 0 := Nat.choose_eq_zero_of_lt h
    simp only [h3, h4, Nat.cast_zero, zero_mul, mul_zero]
  · push Not at h
    have hMn : M - n ≤ L2 := by omega
    have hnM : n ≤ M := Nat.le_of_lt hn
    have hnn : n ≤ n + a := Nat.le_add_right n a
    rw [Nat.cast_choose ℚ hMn, Nat.cast_choose ℚ hnn, Nat.cast_choose ℚ hnM,
      Nat.cast_choose ℚ h]
    have e1 : L2 - (M - n) = n + a - L1 := by omega
    have e2 : n + a - n = a := by omega
    rw [e1, e2]
    field_simp

/-- Key Bernoulli identity for odd `M`. -/
private lemma key_identity (M : ℕ) (hM : Odd M) (t : ℚ) :
    ∑ n ∈ Finset.range (M + 1), (M.choose n : ℚ) * bernoulli n * t ^ n * (t - 1) ^ (M - n)
      = -∑ n ∈ Finset.range (M + 1), (M.choose n : ℚ) * bernoulli n * t ^ n := by
  by_cases ht : t = 0
  · subst ht
    have h0mem : 0 ∈ Finset.range (M + 1) :=
      Finset.mem_range.mpr (Nat.zero_lt_succ M)
    have hL : ∑ n ∈ Finset.range (M + 1),
        (M.choose n : ℚ) * bernoulli n * (0 : ℚ) ^ n * ((0 : ℚ) - 1) ^ (M - n)
        = (-1 : ℚ) ^ M := by
      rw [Finset.sum_eq_single 0]
      · simp only [Nat.choose_zero_right, Nat.cast_one, bernoulli_zero, pow_zero,
          one_mul, mul_one, zero_sub, Nat.sub_zero]
      · intro b _ hb
        have hb0 : b ≠ 0 := hb
        rw [zero_pow hb0]
        simp only [mul_zero, zero_mul]
      · intro hcon
        exact absurd h0mem hcon
    have hR : ∑ n ∈ Finset.range (M + 1),
        (M.choose n : ℚ) * bernoulli n * (0 : ℚ) ^ n = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp only [Nat.choose_zero_right, Nat.cast_one, bernoulli_zero, pow_zero,
          mul_one]
      · intro b _ hb
        rw [zero_pow hb]
        simp only [mul_zero]
      · intro hcon
        exact absurd h0mem hcon
    rw [hL, hR, hM.neg_one_pow]
  · have ht0 : t ≠ 0 := ht
    have hP : ∑ n ∈ Finset.range (M + 1), (M.choose n : ℚ) * bernoulli n * t ^ n
        = t ^ M * (Polynomial.bernoulli M).eval (1 / t) := by
      unfold Polynomial.bernoulli
      rw [Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_monomial]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiM : i ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hpow : t ^ M * (1 / t) ^ (M - i) = t ^ i := by
        have h1 : i + (M - i) = M := Nat.add_sub_cancel' hiM
        have h2 : t ^ M = t ^ i * t ^ (M - i) := by
          conv_lhs => rw [← h1]
          rw [pow_add]
        rw [h2]
        have hne : t ^ (M - i) ≠ 0 := pow_ne_zero _ ht0
        have h3 : (1 / t) ^ (M - i) = 1 / t ^ (M - i) := by
          rw [div_pow, one_pow]
        rw [h3, mul_assoc, mul_one_div_cancel hne, mul_one]
      calc (M.choose i : ℚ) * bernoulli i * t ^ i
          = t ^ M * ((bernoulli i * (M.choose i : ℚ)) * (1 / t) ^ (M - i)) := by
            rw [← hpow]
            ring
        _ = t ^ M * ((bernoulli i * (M.choose i : ℚ)) * (1 / t) ^ (M - i)) := rfl
    have hL : ∑ n ∈ Finset.range (M + 1),
        (M.choose n : ℚ) * bernoulli n * t ^ n * (t - 1) ^ (M - n)
        = t ^ M * (Polynomial.bernoulli M).eval (1 - 1 / t) := by
      unfold Polynomial.bernoulli
      rw [Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_monomial]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiM : i ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hdiv : (1 : ℚ) - 1 / t = (t - 1) / t := by
        field_simp
      have hpow2 : t ^ M * (1 - 1 / t) ^ (M - i) = t ^ i * (t - 1) ^ (M - i) := by
        rw [hdiv, div_pow]
        have h1 : i + (M - i) = M := Nat.add_sub_cancel' hiM
        have h2 : t ^ M = t ^ i * t ^ (M - i) := by
          conv_lhs => rw [← h1]
          rw [pow_add]
        rw [h2]
        have hne : t ^ (M - i) ≠ 0 := pow_ne_zero _ ht0
        field_simp
      calc (M.choose i : ℚ) * bernoulli i * t ^ i * (t - 1) ^ (M - i)
          = (bernoulli i * (M.choose i : ℚ)) * (t ^ i * (t - 1) ^ (M - i)) := by
            ring
        _ = (bernoulli i * (M.choose i : ℚ)) * (t ^ M * (1 - 1 / t) ^ (M - i)) := by
            rw [← hpow2]
        _ = t ^ M * ((bernoulli i * (M.choose i : ℚ)) * (1 - 1 / t) ^ (M - i)) := by
            ring
    have hsym : (Polynomial.bernoulli M).eval (1 - 1 / t)
        = - (Polynomial.bernoulli M).eval (1 / t) := by
      have h1 := Polynomial.bernoulli_eval_one_sub M (1 / t)
      rw [h1, hM.neg_one_pow]
      ring
    rw [hL, hP, hsym]
    ring

/-- Vanishing of the reformulated Bernoulli sum for odd `M > 1`. -/
private lemma S_new_eq_zero (M a L1 L2 : ℕ) (hM : Odd M) (hM1 : 1 < M)
    (hN : L1 + L2 = M + a) :
    ∑ n ∈ Finset.range M, (M.choose n : ℚ) * (((n + a).choose L1 : ℚ)
      + ((n + a).choose L2 : ℚ)) * bernoulli n = 0 := by
  have hB : bernoulli M = 0 := bernoulli_eq_zero_of_odd hM hM1
  set F : Polynomial ℚ :=
    ∑ n ∈ Finset.range (M + 1),
      Polynomial.C ((M.choose n : ℚ) * bernoulli n) * (1 + Polynomial.X) ^ (n + a)
    with hF
  set Q : Polynomial ℚ :=
    ∑ n ∈ Finset.range (M + 1),
      Polynomial.C ((M.choose n : ℚ) * bernoulli n)
        * ((1 + Polynomial.X) ^ n * Polynomial.X ^ (M - n))
    with hQ
  have hFQ : F + (1 + Polynomial.X) ^ a * Q = 0 := by
    apply Polynomial.funext
    intro y
    have hkey := key_identity M hM (1 + y)
    have hsub : (1 + y) - 1 = y := by ring
    rw [hsub] at hkey
    have hFeval : (F).eval y
        = ∑ n ∈ Finset.range (M + 1),
          ((M.choose n : ℚ) * bernoulli n) * (1 + y) ^ (n + a) := by
      rw [hF, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    have hQeval : Q.eval y
        = ∑ n ∈ Finset.range (M + 1),
          ((M.choose n : ℚ) * bernoulli n) * ((1 + y) ^ n * y ^ (M - n)) := by
      rw [hQ, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_X]
    have hLHS : (F + (1 + Polynomial.X) ^ a * Q).eval y = 0 := by
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X, hFeval, hQeval]
      have hFfac : ∑ n ∈ Finset.range (M + 1),
          ((M.choose n : ℚ) * bernoulli n) * (1 + y) ^ (n + a)
          = (1 + y) ^ a * ∑ n ∈ Finset.range (M + 1),
            ((M.choose n : ℚ) * bernoulli n) * (1 + y) ^ n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        have hpa : (n + a : ℕ) = a + n := by omega
        rw [hpa, pow_add]
        ring
      rw [hFfac, ← mul_add]
      have hPQ : ∑ n ∈ Finset.range (M + 1),
          ((M.choose n : ℚ) * bernoulli n) * (1 + y) ^ n
          + ∑ n ∈ Finset.range (M + 1),
            ((M.choose n : ℚ) * bernoulli n) * ((1 + y) ^ n * y ^ (M - n))
          = 0 := by
        have hkey2 : ∑ n ∈ Finset.range (M + 1),
            ((M.choose n : ℚ) * bernoulli n) * ((1 + y) ^ n * y ^ (M - n))
            = -∑ n ∈ Finset.range (M + 1),
              ((M.choose n : ℚ) * bernoulli n) * (1 + y) ^ n := by
          have htmp := hkey
          simp only [mul_assoc] at htmp ⊢
          exact htmp
        rw [hkey2, add_neg_cancel]
      rw [hPQ, mul_zero]
    rw [hLHS]
    simp only [Polynomial.eval_zero]
  have hcoeff : ∀ K : ℕ,
      (F + (1 + Polynomial.X) ^ a * Q).coeff K
        = (∑ n ∈ Finset.range (M + 1), (M.choose n : ℚ) * bernoulli n
            * (((n + a).choose K : ℚ) + ((n + a).choose (M + a - K) : ℚ))) := by
    intro K
    have hFcoeff : F.coeff K
        = ∑ n ∈ Finset.range (M + 1),
          (M.choose n : ℚ) * bernoulli n * ((n + a).choose K : ℚ) := by
      rw [hF, Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
    have hQcoeff : ((1 + Polynomial.X) ^ a * Q).coeff K
        = ∑ n ∈ Finset.range (M + 1),
          (M.choose n : ℚ) * bernoulli n * ((n + a).choose (M + a - K) : ℚ) := by
      by_cases hK : K ≤ M + a
      · have hQexp : (1 + Polynomial.X) ^ a * Q
            = ∑ n ∈ Finset.range (M + 1),
              Polynomial.C ((M.choose n : ℚ) * bernoulli n)
                * ((1 + Polynomial.X) ^ (n + a) * Polynomial.X ^ (M - n)) := by
          rw [hQ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          have hpa : (n + a : ℕ) = a + n := by omega
          rw [hpa, pow_add]
          ring
        rw [hQexp, Polynomial.finsetSum_coeff]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hnM : n ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
        by_cases hle : M - n ≤ K
        · rw [ite_eq_left hle, Polynomial.coeff_one_add_X_pow]
          have heq2 : (n + a) - (K - (M - n)) = M + a - K := by omega
          have hle2 : K - (M - n) ≤ n + a := by omega
          rw [← Nat.choose_symm hle2]
          rw [heq2]
        · rw [ite_eq_right hle]
          have hlt : M + a - K > n + a := by omega
          have hzero : (n + a).choose (M + a - K) = 0 :=
            Nat.choose_eq_zero_of_lt hlt
          rw [hzero]
          simp only [Nat.cast_zero, mul_zero]
      · push Not at hK
        have hQexp : (1 + Polynomial.X) ^ a * Q
            = ∑ n ∈ Finset.range (M + 1),
              Polynomial.C ((M.choose n : ℚ) * bernoulli n)
                * ((1 + Polynomial.X) ^ (n + a) * Polynomial.X ^ (M - n)) := by
          rw [hQ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          have hpa : (n + a : ℕ) = a + n := by omega
          rw [hpa, pow_add]
          ring
        have hLHS0 : ((1 + Polynomial.X) ^ a * Q).coeff K = 0 := by
          rw [hQexp, Polynomial.finsetSum_coeff]
          refine Finset.sum_eq_zero fun n hn => ?_
          have hnM : n ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
          have hle : M - n ≤ K := by omega
          rw [ite_eq_left hle, Polynomial.coeff_one_add_X_pow]
          have hlt : n + a < K - (M - n) := by omega
          have hzero : (n + a).choose (K - (M - n)) = 0 :=
            Nat.choose_eq_zero_of_lt hlt
          rw [hzero]
          simp only [Nat.cast_zero, mul_zero]
        have hRHS0 : ∑ n ∈ Finset.range (M + 1),
            (M.choose n : ℚ) * bernoulli n * ((n + a).choose (M + a - K) : ℚ)
            = 0 := by
          have hsub : M + a - K = 0 := by omega
          rw [hsub]
          have hsum : ∑ n ∈ Finset.range (M + 1),
              (M.choose n : ℚ) * bernoulli n * ((n + a).choose 0 : ℚ) = 0 := by
            simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
            have hMne : M ≠ 1 := ne_of_gt hM1
            have hber : ∑ k ∈ Finset.range M, (M.choose k : ℚ) * bernoulli k = 0 := by
              have hsb := sum_bernoulli M
              simp only [hMne, ite_false] at hsb
              exact hsb
            have hsplit : ∑ n ∈ Finset.range (M + 1),
                (M.choose n : ℚ) * bernoulli n
                = ∑ k ∈ Finset.range M, (M.choose k : ℚ) * bernoulli k
                  + (M.choose M : ℚ) * bernoulli M := by
              rw [Finset.sum_range_succ]
            rw [hsplit, hber, hB]
            simp only [mul_zero, add_zero]
          exact hsum
        rw [hLHS0, hRHS0]
    rw [Polynomial.coeff_add, hFcoeff, hQcoeff, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hL1 : L1 ≤ M + a := by omega
  have hL2eq : L2 = M + a - L1 := by omega
  have hmain : ∑ n ∈ Finset.range (M + 1), (M.choose n : ℚ) * bernoulli n
      * (((n + a).choose L1 : ℚ) + ((n + a).choose L2 : ℚ)) = 0 := by
    have h0 : (F + (1 + Polynomial.X) ^ a * Q).coeff L1 = 0 := by
      rw [hFQ]
      simp only [Polynomial.coeff_zero]
    rw [hcoeff L1, ← hL2eq] at h0
    exact h0
  have htail : (M.choose M : ℚ) * bernoulli M * (((M + a).choose L1 : ℚ)
      + ((M + a).choose L2 : ℚ)) = 0 := by
    rw [hB]
    simp only [mul_zero, zero_mul]
  have hsplit : ∑ n ∈ Finset.range (M + 1), (M.choose n : ℚ) * bernoulli n
      * (((n + a).choose L1 : ℚ) + ((n + a).choose L2 : ℚ))
      = ∑ n ∈ Finset.range M, (M.choose n : ℚ) * bernoulli n
        * (((n + a).choose L1 : ℚ) + ((n + a).choose L2 : ℚ)) := by
    rw [Finset.sum_range_succ]
    simp only [htail, add_zero]
  rw [hsplit] at hmain
  -- Convert to goal form (with * order: C*(...+...)*B vs C*B*(...+...))
  have hconv : ∀ n ∈ Finset.range M,
      (M.choose n : ℚ) * (((n + a).choose L1 : ℚ) + ((n + a).choose L2 : ℚ))
        * bernoulli n
      = (M.choose n : ℚ) * bernoulli n * (((n + a).choose L1 : ℚ)
        + ((n + a).choose L2 : ℚ)) := by
    intro n _
    ring
  rw [Finset.sum_congr rfl hconv]
  exact hmain

/-- Original Bernoulli sums cancel for Zagier indices. -/
private lemma S_orig_eq_zero (K i1 j1 : ℕ) (hi1 : 1 ≤ i1) (hiK : i1 < K)
    (hj1 : 1 ≤ j1) (hjK : j1 < K) :
    (∑ n ∈ Finset.range (2 * K - 2 * i1 + 1),
      ((2 * j1 - 1).choose (2 * K - 2 * i1 - n + 1) : ℚ)
        * (((n + 2 * i1 - 2).choose n : ℚ)) * bernoulli n)
    + (∑ n ∈ Finset.range (2 * K - 2 * i1 + 1),
      ((2 * K - 2 * j1).choose (2 * K - 2 * i1 - n + 1) : ℚ)
        * (((n + 2 * i1 - 2).choose n : ℚ)) * bernoulli n) = 0 := by
  set M : ℕ := 2 * K - 2 * i1 + 1 with hMdef
  set a : ℕ := 2 * i1 - 2 with hadef
  set L1 : ℕ := 2 * K - 2 * j1 with hL1def
  set L2 : ℕ := 2 * j1 - 1 with hL2def
  have hM : Odd M := ⟨K - i1, by omega⟩
  have hM1 : 1 < M := by omega
  have hN : L1 + L2 = M + a := by omega
  have hSnew := S_new_eq_zero M a L1 L2 hM hM1 hN
  have hterm : ∀ n ∈ Finset.range M,
      ((L2.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n)
        + ((L1.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n)
      = (L1.factorial * L2.factorial : ℚ) / ((a.factorial * M.factorial : ℚ))
        * ((M.choose n : ℚ) * (((n + a).choose L1 : ℚ)
          + ((n + a).choose L2 : ℚ)) * bernoulli n) := by
    intro n hn
    have hnm : n < M := Finset.mem_range.mp hn
    have hc1 := binomial_cross M a L1 L2 n hN hnm
    have hNsym : L2 + L1 = M + a := by omega
    have hc2 := binomial_cross M a L2 L1 n hNsym hnm
    have hfac_eq : (L2.factorial * L1.factorial : ℚ)
        / ((a.factorial * M.factorial : ℚ))
        = (L1.factorial * L2.factorial : ℚ)
          / ((a.factorial * M.factorial : ℚ)) := by
      ring
    rw [hfac_eq] at hc2
    calc ((L2.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n)
          + ((L1.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n)
        = ((L2.choose (M - n) : ℚ) * (((n + a).choose n : ℚ))) * bernoulli n
          + ((L1.choose (M - n) : ℚ) * (((n + a).choose n : ℚ))) * bernoulli n := by
            ring
      _ = ((L1.factorial * L2.factorial : ℚ) / ((a.factorial * M.factorial : ℚ))
            * ((M.choose n : ℚ) * (((n + a).choose L1 : ℚ)))) * bernoulli n
          + ((L1.factorial * L2.factorial : ℚ) / ((a.factorial * M.factorial : ℚ))
            * ((M.choose n : ℚ) * (((n + a).choose L2 : ℚ)))) * bernoulli n := by
            rw [hc1, hc2]
      _ = (L1.factorial * L2.factorial : ℚ) / ((a.factorial * M.factorial : ℚ))
          * ((M.choose n : ℚ) * (((n + a).choose L1 : ℚ)
            + ((n + a).choose L2 : ℚ)) * bernoulli n) := by
            ring
  have hsum : (∑ n ∈ Finset.range M,
        ((L2.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n))
      + (∑ n ∈ Finset.range M,
        ((L1.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n))
      = (L1.factorial * L2.factorial : ℚ) / ((a.factorial * M.factorial : ℚ))
        * (∑ n ∈ Finset.range M, (M.choose n : ℚ)
          * (((n + a).choose L1 : ℚ) + ((n + a).choose L2 : ℚ)) * bernoulli n) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hterm n hn]
  rw [hSnew, mul_zero] at hsum
  have hconv1 : ∀ n ∈ Finset.range M,
      ((2 * j1 - 1).choose (2 * K - 2 * i1 - n + 1) : ℚ)
        * (((n + 2 * i1 - 2).choose n : ℚ)) * bernoulli n
      = ((L2.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n) := by
    intro n hn
    have hnm : n < M := Finset.mem_range.mp hn
    have e1 : 2 * K - 2 * i1 - n + 1 = M - n := by omega
    have e2 : n + 2 * i1 - 2 = n + a := by omega
    rw [e1, e2]
  have hconv2 : ∀ n ∈ Finset.range M,
      ((2 * K - 2 * j1).choose (2 * K - 2 * i1 - n + 1) : ℚ)
        * (((n + 2 * i1 - 2).choose n : ℚ)) * bernoulli n
      = ((L1.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n) := by
    intro n hn
    have hnm : n < M := Finset.mem_range.mp hn
    have e1 : 2 * K - 2 * i1 - n + 1 = M - n := by omega
    have e2 : n + 2 * i1 - 2 = n + a := by omega
    rw [e1, e2]
  have hrw : (∑ n ∈ Finset.range (2 * K - 2 * i1 + 1),
        ((2 * j1 - 1).choose (2 * K - 2 * i1 - n + 1) : ℚ)
          * (((n + 2 * i1 - 2).choose n : ℚ)) * bernoulli n)
      + (∑ n ∈ Finset.range (2 * K - 2 * i1 + 1),
        ((2 * K - 2 * j1).choose (2 * K - 2 * i1 - n + 1) : ℚ)
          * (((n + 2 * i1 - 2).choose n : ℚ)) * bernoulli n)
      = (∑ n ∈ Finset.range M,
          ((L2.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n))
        + (∑ n ∈ Finset.range M,
          ((L1.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n)) := by
    have hMeq : 2 * K - 2 * i1 + 1 = M := rfl
    rw [hMeq]
    have h1 : (∑ n ∈ Finset.range M,
          ((2 * j1 - 1).choose (2 * K - 2 * i1 - n + 1) : ℚ)
            * (((n + 2 * i1 - 2).choose n : ℚ)) * bernoulli n)
        = ∑ n ∈ Finset.range M,
          ((L2.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      exact hconv1 n hn
    have h2 : (∑ n ∈ Finset.range M,
          ((2 * K - 2 * j1).choose (2 * K - 2 * i1 - n + 1) : ℚ)
            * (((n + 2 * i1 - 2).choose n : ℚ)) * bernoulli n)
        = ∑ n ∈ Finset.range M,
          ((L1.choose (M - n) : ℚ) * (((n + a).choose n : ℚ)) * bernoulli n) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      exact hconv2 n hn
    rw [h1, h2]
  rw [hrw, hsum]

/-- Alternating binomial sum over `ℚ`. -/
private lemma alt_sum_choose (M : ℕ) :
    ∑ u ∈ Finset.range (M + 1), (-1 : ℚ) ^ u * ((M.choose u : ℚ))
      = if M = 0 then 1 else 0 := by
  have h := add_pow (-1 : ℚ) 1 M
  have h0 : (-1 : ℚ) + 1 = 0 := by ring
  rw [h0] at h
  have hsum : ∑ m ∈ Finset.range (M + 1), (-1 : ℚ) ^ m * (1 : ℚ) ^ (M - m)
      * ((M.choose m : ℚ))
      = ∑ u ∈ Finset.range (M + 1), (-1 : ℚ) ^ u * ((M.choose u : ℚ)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [one_pow, mul_one]
  rw [hsum] at h
  by_cases hm : M = 0
  · subst hm
    simp only [pow_zero] at h
    simp only [ite_true]
    exact h.symm
  · have hz : (0 : ℚ) ^ M = 0 := zero_pow hm
    rw [hz] at h
    simp only [hm, ite_false]
    exact h.symm

/-- Alternating convolution of two binomial coefficients. -/
private lemma zmi_alt_choose_mul (M c : ℕ) :
    ∑ k ∈ Finset.range (M + 1),
      (-1 : ℚ) ^ k * (M.choose k : ℚ) * (k.choose c : ℚ)
      = if c = M then (-1 : ℚ) ^ M else 0 := by
  by_cases hc : c ≤ M
  · have hsplit := Finset.sum_range_add
      (fun k => (-1 : ℚ) ^ k * (M.choose k : ℚ) * (k.choose c : ℚ))
      c (M - c + 1)
    have hlen : c + (M - c + 1) = M + 1 := by omega
    rw [hlen] at hsplit
    have hfirst : ∑ k ∈ Finset.range c,
        (-1 : ℚ) ^ k * (M.choose k : ℚ) * (k.choose c : ℚ) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkc : k < c := Finset.mem_range.mp hk
      rw [Nat.choose_eq_zero_of_lt hkc]
      simp only [Nat.cast_zero, mul_zero]
    have hsecond : ∑ u ∈ Finset.range (M - c + 1),
        (-1 : ℚ) ^ (c + u) * (M.choose (c + u) : ℚ) * ((c + u).choose c : ℚ)
        = (-1 : ℚ) ^ c * (M.choose c : ℚ)
          * ∑ u ∈ Finset.range (M - c + 1),
            (-1 : ℚ) ^ u * ((M - c).choose u : ℚ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hchoose : (M.choose (c + u) : ℚ) * ((c + u).choose c : ℚ)
          = (M.choose c : ℚ) * ((M - c).choose u : ℚ) := by
        have hchooseNat := Nat.choose_mul (n := M) (k := c + u) (s := c) (by omega)
        have hsub : c + u - c = u := by omega
        rw [hsub] at hchooseNat
        exact_mod_cast hchooseNat
      rw [pow_add]
      calc
        (-1 : ℚ) ^ c * (-1 : ℚ) ^ u * (M.choose (c + u) : ℚ)
            * ((c + u).choose c : ℚ)
            = (-1 : ℚ) ^ c * (-1 : ℚ) ^ u
              * ((M.choose (c + u) : ℚ) * ((c + u).choose c : ℚ)) := by ring
        _ = (-1 : ℚ) ^ c * (M.choose c : ℚ)
              * ((-1 : ℚ) ^ u * ((M - c).choose u : ℚ)) := by rw [hchoose]; ring
    rw [hfirst, hsecond, alt_sum_choose] at hsplit
    rw [hsplit]
    by_cases heq : c = M
    · subst c
      simp
    · have hsub : M - c ≠ 0 := by omega
      simp [heq, hsub]
  · have hlt : M < c := by omega
    have hne : c ≠ M := by omega
    simp only [hne, ite_false]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hklt : k < M + 1 := Finset.mem_range.mp hk
    have hkM : k ≤ M := by omega
    have hkc : k < c := by omega
    rw [Nat.choose_eq_zero_of_lt hkc]
    simp only [Nat.cast_zero, mul_zero]

/-- Pairing odd and even indices gives a finite alternating sum. -/
private lemma zmi_pair_sum (N : ℕ) (f : ℕ → ℚ) :
    ∑ r ∈ Finset.range N, (f (2 * r + 1) - f (2 * r + 2))
      = f 0 - ∑ k ∈ Finset.range (2 * N + 1), (-1 : ℚ) ^ k * f k := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hsum : ∑ k ∈ Finset.range (2 * (N + 1) + 1), (-1 : ℚ) ^ k * f k
          = (∑ k ∈ Finset.range (2 * N + 1), (-1 : ℚ) ^ k * f k)
            + (-1 : ℚ) ^ (2 * N + 1) * f (2 * N + 1)
            + (-1 : ℚ) ^ (2 * N + 2) * f (2 * N + 2) := by
        rw [show 2 * (N + 1) + 1 = (2 * N + 2) + 1 by omega,
          Finset.sum_range_succ,
          show 2 * N + 2 = (2 * N + 1) + 1 by omega,
          Finset.sum_range_succ]
      have hodd : Odd (2 * N + 1) := ⟨N, by omega⟩
      have heven : Even (2 * N + 2) := ⟨N + 1, by omega⟩
      rw [hsum, hodd.neg_one_pow, heven.neg_one_pow]
      ring

/-- The inner sum in the product `P * A` is a Kronecker delta. -/
private lemma zmi_inner_sum (N M c : ℕ) (hM : M ≤ 2 * N) (hc : 1 ≤ c)
    (hMeven : Even M) :
    ∑ r ∈ Finset.range N,
      ((M.choose (2 * r + 1) : ℚ) * ((2 * r + 1).choose c : ℚ)
        - (M.choose (2 * (N - r)) : ℚ) * ((2 * (N - r)).choose c : ℚ))
      = if c = M then -1 else 0 := by
  let f : ℕ → ℚ := fun k => (M.choose k : ℚ) * (k.choose c : ℚ)
  change ∑ r ∈ Finset.range N, (f (2 * r + 1) - f (2 * (N - r)))
    = if c = M then -1 else 0
  have hreflect : ∑ r ∈ Finset.range N, f (2 * (N - r))
      = ∑ r ∈ Finset.range N, f (2 * r + 2) := by
    calc
      ∑ r ∈ Finset.range N, f (2 * (N - r))
          = ∑ r ∈ Finset.range N, f (2 * (N - (N - 1 - r))) := by
            symm
            exact Finset.sum_range_reflect (fun r => f (2 * (N - r))) N
      _ = ∑ r ∈ Finset.range N, f (2 * r + 2) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hrN : r < N := Finset.mem_range.mp hr
        congr 1
        omega
  rw [Finset.sum_sub_distrib, hreflect, ← Finset.sum_sub_distrib, zmi_pair_sum]
  have hf0 : f 0 = 0 := by
    have h0c : 0 < c := by omega
    simp [f, Nat.choose_eq_zero_of_lt h0c]
  have halt : ∑ k ∈ Finset.range (2 * N + 1), (-1 : ℚ) ^ k * f k
      = ∑ k ∈ Finset.range (M + 1), (-1 : ℚ) ^ k * f k := by
    have hsplit := Finset.sum_range_add (fun k => (-1 : ℚ) ^ k * f k)
      (M + 1) (2 * N - M)
    have hlen : M + 1 + (2 * N - M) = 2 * N + 1 := by omega
    rw [hlen] at hsplit
    have htail : ∑ k ∈ Finset.range (2 * N - M),
        (-1 : ℚ) ^ (M + 1 + k) * f (M + 1 + k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hlt : M < M + 1 + k := by omega
      simp [f, Nat.choose_eq_zero_of_lt hlt]
    rw [htail, add_zero] at hsplit
    exact hsplit
  rw [hf0, halt]
  simp only [zero_sub, f]
  have hAlt : ∑ k ∈ Finset.range (M + 1),
      (-1 : ℚ) ^ k * ((M.choose k : ℚ) * (k.choose c : ℚ))
      = if c = M then (-1 : ℚ) ^ M else 0 := by
    simpa only [mul_assoc] using zmi_alt_choose_mul M c
  rw [hAlt]
  by_cases heq : c = M
  · simp [heq, hMeven.neg_one_pow]
  · simp [heq]

/-- The outer Bernoulli sum leaves only the diagonal `B₁` term. -/
private lemma zmi_bernoulli_delta (K s t : ℕ) (hs1 : 1 ≤ s) (hsK : s < K)
    (ht1 : 1 ≤ t) (htK : t < K) :
    (2 : ℚ) / (2 * (s : ℚ) - 1)
      * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
        ((n + 2 * s - 2).choose n : ℚ) * bernoulli n
          * (if 2 * K - 2 * s - n + 1 = 2 * K - 2 * t then (-1 : ℚ) else 0)
      = if s = t then 1 else 0 := by
  rcases lt_trichotomy s t with hst | rfl | hts
  · have hsum : ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
        ((n + 2 * s - 2).choose n : ℚ) * bernoulli n
          * (if 2 * K - 2 * s - n + 1 = 2 * K - 2 * t then (-1 : ℚ) else 0)
        = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      by_cases hdelta : 2 * K - 2 * s - n + 1 = 2 * K - 2 * t
      · have hnodd : Odd n := ⟨t - s, by omega⟩
        have hn1 : 1 < n := by omega
        rw [bernoulli_eq_zero_of_odd hnodd hn1]
        simp
      · simp [hdelta]
    rw [hsum, mul_zero]
    simp [ne_of_lt hst]
  · have hmem : 1 ∈ Finset.range (2 * K - 2 * s + 1) := by
      rw [Finset.mem_range]
      omega
    have harg : 1 + 2 * s - 2 = 2 * s - 1 := by omega
    have hdelta : 2 * K - 2 * s - 1 + 1 = 2 * K - 2 * s := by omega
    have hcast : ((2 * s - 1 : ℕ) : ℚ) = 2 * (s : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul]
      norm_num
    have hsum : ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
        ((n + 2 * s - 2).choose n : ℚ) * bernoulli n
          * (if 2 * K - 2 * s - n + 1 = 2 * K - 2 * s then (-1 : ℚ) else 0)
        = (2 * (s : ℚ) - 1) / 2 := by
      rw [Finset.sum_eq_single 1]
      · have hif : (if 2 * K - 2 * s = 2 * K - 2 * s then (-1 : ℚ) else 0)
            = -1 := by simp
        rw [harg, hdelta, hif, Nat.choose_one_right, bernoulli_one, hcast]
        ring
      · intro n hn hn1
        have hne : 2 * K - 2 * s - n + 1 ≠ 2 * K - 2 * s := by omega
        simp [hne]
      · intro hnot
        exact (hnot hmem).elim
    rw [hsum]
    have hd : (2 : ℚ) * (s : ℚ) - 1 ≠ 0 := by
      have hsQ : (1 : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs1
      linarith
    field_simp
    simp
  · have hsum : ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
        ((n + 2 * s - 2).choose n : ℚ) * bernoulli n
          * (if 2 * K - 2 * s - n + 1 = 2 * K - 2 * t then (-1 : ℚ) else 0)
        = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnlt : n < 2 * K - 2 * s + 1 := Finset.mem_range.mp hn
      have hne : 2 * K - 2 * s - n + 1 ≠ 2 * K - 2 * t := by omega
      simp [hne]
    rw [hsum, mul_zero]
    simp [ne_of_gt hts]

/-- **Zagier's matrix.** For a natural number $K$, Zagier's matrix $A_K$ is the rational matrix
with rows and columns indexed by $1 \le i, j \le K - 1$ (empty when $K \le 1$) whose
$(i, j)$ entry is

$$(A_K)_{ij} = \binom{2K - 2j}{2i - 1} + \binom{2K - 2j}{2K - 2i},$$

where $\binom{m}{k} = 0$ for $k > m$. -/
public def zagierMatrix (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := fun i j =>
  (Nat.choose (2 * K - 2 * (j.val + 1)) (2 * (i.val + 1) - 1) : ℚ)
    + (Nat.choose (2 * K - 2 * (j.val + 1)) (2 * K - 2 * (i.val + 1)) : ℚ)

/-- **First Bernoulli formula for the inverse of Zagier's matrix.** For a natural number $K$,
$P_K$ is the rational matrix with rows and columns indexed by $1 \le i, j \le K - 1$ (empty
when $K \le 1$) whose $(i, j)$ entry is

$$(P_K)_{ij} = \frac{2}{2i-1} \sum_{n=0}^{2K-2i} \binom{2j-1}{2K-2i-n+1} \binom{n+2i-2}{n} B_n,$$

where $B_n$ is the $n$-th Bernoulli number with $B_1 = -\frac{1}{2}$ and $\binom{m}{k} = 0$
for $k > m$. -/
public def zagierInverseP (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := fun i j =>
  (2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1)
    * ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
      (Nat.choose (2 * (j.val + 1) - 1) (2 * K - 2 * (i.val + 1) - n + 1) : ℚ)
        * (Nat.choose (n + 2 * (i.val + 1) - 2) n : ℚ) * bernoulli n

/-- **Second Bernoulli formula for the inverse of Zagier's matrix.** For a natural number $K$,
$Q_K$ is the rational matrix with rows and columns indexed by $1 \le i, j \le K - 1$ (empty
when $K \le 1$) whose $(i, j)$ entry is

$$(Q_K)_{ij} = -\frac{2}{2i-1} \sum_{n=0}^{2K-2i} \binom{2K-2j}{2K-2i-n+1} \binom{n+2i-2}{n} B_n,$$

where $B_n$ is the $n$-th Bernoulli number with $B_1 = -\frac{1}{2}$ and $\binom{m}{k} = 0$
for $k > m$. -/
public def zagierInverseQ (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := fun i j =>
  (-2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1)
    * ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
      (Nat.choose (2 * K - 2 * (j.val + 1)) (2 * K - 2 * (i.val + 1) - n + 1) : ℚ)
        * (Nat.choose (n + 2 * (i.val + 1) - 2) n : ℚ) * bernoulli n

/-- **The two Bernoulli formulas for the inverse of Zagier's matrix agree.** For every natural
number $K \ge 2$, the matrices $P_K$ and $Q_K$ given by the first and second Bernoulli formulas
for the inverse of Zagier's matrix are equal: $P_K = Q_K$. -/
public lemma zagierInverseP_eq_zagierInverseQ (K : ℕ) (hK : 1 < K) :
    zagierInverseP K = zagierInverseQ K := by
  ext i j
  simp only [zagierInverseP, zagierInverseQ]
  set i1 : ℕ := i.val + 1 with hi1def
  set j1 : ℕ := j.val + 1 with hj1def
  have hi1 : 1 ≤ i1 := by omega
  have hiK : i1 < K := by
    have hi : i.val < K - 1 := i.isLt
    omega
  have hj1 : 1 ≤ j1 := by omega
  have hjK : j1 < K := by
    have hj : j.val < K - 1 := j.isLt
    omega
  have hS := S_orig_eq_zero K i1 j1 hi1 hiK hj1 hjK
  have hi1q : (1 : ℚ) ≤ (i1 : ℚ) := by exact_mod_cast hi1
  have hd : (2 : ℚ) * (i1 : ℚ) - 1 ≠ 0 := by
    have hpos : (0 : ℚ) < 2 * (i1 : ℚ) - 1 := by linarith
    exact ne_of_gt hpos
  field_simp
  linarith [hS]

/-- Entrywise evaluation of `P * A`, using the first formula on `B` and the second on `C`. -/
private lemma zmi_product_sum (K s t : ℕ) (hs1 : 1 ≤ s) (hsK : s < K)
    (ht1 : 1 ≤ t) (htK : t < K) :
    (∑ r : Fin (K - 1), (
      ((2 : ℚ) / (2 * (s : ℚ) - 1)
          * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
            (Nat.choose (2 * (r.val + 1) - 1) (2 * K - 2 * s - n + 1) : ℚ)
              * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
        * (Nat.choose (2 * K - 2 * t) (2 * (r.val + 1) - 1) : ℚ)
      + ((-2 : ℚ) / (2 * (s : ℚ) - 1)
          * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
            (Nat.choose (2 * K - 2 * (r.val + 1)) (2 * K - 2 * s - n + 1) : ℚ)
              * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
        * (Nat.choose (2 * K - 2 * t) (2 * K - 2 * (r.val + 1)) : ℚ)))
      = if s = t then 1 else 0 := by
  let d : ℚ := (2 : ℚ) / (2 * (s : ℚ) - 1)
  let common : ℕ → ℚ := fun n =>
    (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n
  let inner : ℕ → ℕ → ℚ := fun n r =>
    (Nat.choose (2 * K - 2 * t) (2 * (r + 1) - 1) : ℚ)
        * (Nat.choose (2 * (r + 1) - 1) (2 * K - 2 * s - n + 1) : ℚ)
      - (Nat.choose (2 * K - 2 * t) (2 * K - 2 * (r + 1)) : ℚ)
        * (Nat.choose (2 * K - 2 * (r + 1)) (2 * K - 2 * s - n + 1) : ℚ)
  have hterm : ∀ r : Fin (K - 1),
      ((2 : ℚ) / (2 * (s : ℚ) - 1)
          * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
            (Nat.choose (2 * (r.val + 1) - 1) (2 * K - 2 * s - n + 1) : ℚ)
              * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
        * (Nat.choose (2 * K - 2 * t) (2 * (r.val + 1) - 1) : ℚ)
      + ((-2 : ℚ) / (2 * (s : ℚ) - 1)
          * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
            (Nat.choose (2 * K - 2 * (r.val + 1)) (2 * K - 2 * s - n + 1) : ℚ)
              * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
        * (Nat.choose (2 * K - 2 * t) (2 * K - 2 * (r.val + 1)) : ℚ)
      = d * ∑ n ∈ Finset.range (2 * K - 2 * s + 1), common n * inner n r.val := by
    intro r
    dsimp only [d, common, inner]
    calc
      ((2 : ℚ) / (2 * (s : ℚ) - 1)
            * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
              (Nat.choose (2 * (r.val + 1) - 1) (2 * K - 2 * s - n + 1) : ℚ)
                * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
          * (Nat.choose (2 * K - 2 * t) (2 * (r.val + 1) - 1) : ℚ)
        + ((-2 : ℚ) / (2 * (s : ℚ) - 1)
            * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
              (Nat.choose (2 * K - 2 * (r.val + 1)) (2 * K - 2 * s - n + 1) : ℚ)
                * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
          * (Nat.choose (2 * K - 2 * t) (2 * K - 2 * (r.val + 1)) : ℚ)
          = (2 : ℚ) / (2 * (s : ℚ) - 1)
            * ((∑ n ∈ Finset.range (2 * K - 2 * s + 1),
                (Nat.choose (2 * (r.val + 1) - 1) (2 * K - 2 * s - n + 1) : ℚ)
                  * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
                * (Nat.choose (2 * K - 2 * t) (2 * (r.val + 1) - 1) : ℚ)
              - (∑ n ∈ Finset.range (2 * K - 2 * s + 1),
                (Nat.choose (2 * K - 2 * (r.val + 1))
                    (2 * K - 2 * s - n + 1) : ℚ)
                  * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
                * (Nat.choose (2 * K - 2 * t) (2 * K - 2 * (r.val + 1)) : ℚ)) := by
              ring
      _ = (2 : ℚ) / (2 * (s : ℚ) - 1)
            * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
              ((Nat.choose (2 * (r.val + 1) - 1) (2 * K - 2 * s - n + 1) : ℚ)
                  * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n
                  * (Nat.choose (2 * K - 2 * t) (2 * (r.val + 1) - 1) : ℚ)
                - (Nat.choose (2 * K - 2 * (r.val + 1))
                    (2 * K - 2 * s - n + 1) : ℚ)
                  * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n
                  * (Nat.choose (2 * K - 2 * t) (2 * K - 2 * (r.val + 1)) : ℚ)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
      _ = (2 : ℚ) / (2 * (s : ℚ) - 1)
            * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
              ((Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
                * ((Nat.choose (2 * K - 2 * t) (2 * (r.val + 1) - 1) : ℚ)
                    * (Nat.choose (2 * (r.val + 1) - 1)
                      (2 * K - 2 * s - n + 1) : ℚ)
                  - (Nat.choose (2 * K - 2 * t) (2 * K - 2 * (r.val + 1)) : ℚ)
                    * (Nat.choose (2 * K - 2 * (r.val + 1))
                      (2 * K - 2 * s - n + 1) : ℚ)) := by
              congr 1
              refine Finset.sum_congr rfl fun n _ => ?_
              ring
  calc
    (∑ r : Fin (K - 1), (
        ((2 : ℚ) / (2 * (s : ℚ) - 1)
            * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
              (Nat.choose (2 * (r.val + 1) - 1) (2 * K - 2 * s - n + 1) : ℚ)
                * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
          * (Nat.choose (2 * K - 2 * t) (2 * (r.val + 1) - 1) : ℚ)
        + ((-2 : ℚ) / (2 * (s : ℚ) - 1)
            * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
              (Nat.choose (2 * K - 2 * (r.val + 1)) (2 * K - 2 * s - n + 1) : ℚ)
                * (Nat.choose (n + 2 * s - 2) n : ℚ) * bernoulli n)
          * (Nat.choose (2 * K - 2 * t) (2 * K - 2 * (r.val + 1)) : ℚ)))
        = d * ∑ r : Fin (K - 1),
            ∑ n ∈ Finset.range (2 * K - 2 * s + 1), common n * inner n r.val := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun r _ => hterm r
    _ = d * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
          ∑ r : Fin (K - 1), common n * inner n r.val := by
            congr 1
            rw [Finset.sum_comm]
    _ = d * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
          common n * ∑ r : Fin (K - 1), inner n r.val := by
            congr 1
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
    _ = d * ∑ n ∈ Finset.range (2 * K - 2 * s + 1),
          common n * (if 2 * K - 2 * s - n + 1 = 2 * K - 2 * t then -1 else 0) := by
            congr 1
            refine Finset.sum_congr rfl fun n hn => ?_
            congr 1
            rw [Fin.sum_univ_eq_sum_range]
            dsimp only [inner]
            have hnlt : n < 2 * K - 2 * s + 1 := Finset.mem_range.mp hn
            have hbound : 2 * K - 2 * t ≤ 2 * (K - 1) := by omega
            have hc : 1 ≤ 2 * K - 2 * s - n + 1 := by omega
            have heven : Even (2 * K - 2 * t) := ⟨K - t, by omega⟩
            have hinner := zmi_inner_sum (K - 1) (2 * K - 2 * t)
              (2 * K - 2 * s - n + 1) hbound hc heven
            rw [← hinner]
            refine Finset.sum_congr rfl fun r hr => ?_
            have hrK : r < K - 1 := Finset.mem_range.mp hr
            have hodd : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
            have hevenIndex : 2 * K - 2 * (r + 1) = 2 * (K - 1 - r) := by omega
            rw [hodd, hevenIndex]
    _ = if s = t then 1 else 0 := by
      dsimp only [d, common]
      exact zmi_bernoulli_delta K s t hs1 hsK ht1 htK

/-- **Left inverse of Zagier's matrix.** For every natural number $K \ge 2$, the matrix $P_K$
given by the first Bernoulli formula is a left inverse of Zagier's matrix $A_K$:
$P_K A_K = I$, where $I$ is the $(K - 1) \times (K - 1)$ identity matrix. -/
public lemma zagierInverseP_mul_zagierMatrix (K : ℕ) (hK : 1 < K) :
    zagierInverseP K * zagierMatrix K = 1 := by
  have hPQ : zagierInverseP K = zagierInverseQ K := zagierInverseP_eq_zagierInverseQ K hK
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi1 : 1 ≤ i.val + 1 := by omega
  have hiK : i.val + 1 < K := by
    have hi := i.isLt
    omega
  have hj1 : 1 ≤ j.val + 1 := by omega
  have hjK : j.val + 1 < K := by
    have hj := j.isLt
    omega
  have hproduct := zmi_product_sum K (i.val + 1) (j.val + 1) hi1 hiK hj1 hjK
  calc
    (∑ r, zagierInverseP K i r * zagierMatrix K r j)
        = ∑ r, (zagierInverseP K i r
            * (Nat.choose (2 * K - 2 * (j.val + 1)) (2 * (r.val + 1) - 1) : ℚ)
          + zagierInverseQ K i r
            * (Nat.choose (2 * K - 2 * (j.val + 1))
              (2 * K - 2 * (r.val + 1)) : ℚ)) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            have hpq : zagierInverseP K i r = zagierInverseQ K i r := by rw [hPQ]
            simp only [zagierMatrix]
            rw [← hpq]
            ring
    _ = if i.val + 1 = j.val + 1 then 1 else 0 := by
      simpa only [zagierInverseP, zagierInverseQ] using hproduct
    _ = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst j
        simp
      · have hval : i.val ≠ j.val := by
          intro h
          apply hij
          exact Fin.ext h
        simp [hij, hval]

/-- **Right inverse of Zagier's matrix.** For every natural number $K \ge 2$, the matrix $P_K$
given by the first Bernoulli formula is a right inverse of Zagier's matrix $A_K$:
$A_K P_K = I$, where $I$ is the $(K - 1) \times (K - 1)$ identity matrix. -/
public lemma zagierMatrix_mul_zagierInverseP (K : ℕ) (hK : 1 < K) :
    zagierMatrix K * zagierInverseP K = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mpr (zagierInverseP_mul_zagierMatrix K hK)

/-- **Zagier's matrix conjecture.** Let $K \ge 2$ be a natural number, let $B_n$ be the $n$-th
Bernoulli number with $B_1 = -\frac{1}{2}$, and let $\binom{m}{k} = 0$ for $k > m$. Let $A$,
$P$ and $Q$ be the $(K - 1) \times (K - 1)$ rational matrices, with rows and columns indexed
by $1 \le i, j \le K - 1$, whose entries are

$$A_{ij} = \binom{2K - 2j}{2i - 1} + \binom{2K - 2j}{2K - 2i},$$

$$P_{ij} = \frac{2}{2i-1} \sum_{n=0}^{2K-2i} \binom{2j-1}{2K-2i-n+1} \binom{n+2i-2}{n} B_n,$$

$$Q_{ij} = -\frac{2}{2i-1} \sum_{n=0}^{2K-2i} \binom{2K-2j}{2K-2i-n+1} \binom{n+2i-2}{n} B_n.$$

Then $P = Q$, $AP = I$ and $PA = I$, where $I$ is the identity matrix; that is, the two
Bernoulli formulas agree and give the two-sided inverse of $A$.

Proves `Wanted` entry `zagier_matrix_inverse`.

Source: Yawen Ma and Lee-Peng Teo, "Another Proof of Zagier's Matrix
Conjecture," Journal of Integer Sequences 25 (2022), Article 22.6.4,
Theorem [Zagier's conjecture], equations (eq12) and (eq13), lines 279–285,
https://cs.uwaterloo.ca/journals/JIS/VOL25/Teo/teo4.tex
-/
public theorem zagier_matrix_inverse (K : ℕ) (hK : 1 < K) :
    (Matrix.of (fun i j : Fin (K - 1) =>
        (2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1) *
          ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
            (↑(Nat.choose (2 * (j.val + 1) - 1)
              (2 * K - 2 * (i.val + 1) - n + 1)) : ℚ) *
              (↑(Nat.choose (n + 2 * (i.val + 1) - 2) n) : ℚ) * bernoulli n) :
      Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    =
    (Matrix.of (fun i j : Fin (K - 1) =>
        (-2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1) *
          ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
            (↑(Nat.choose (2 * K - 2 * (j.val + 1))
              (2 * K - 2 * (i.val + 1) - n + 1)) : ℚ) *
              (↑(Nat.choose (n + 2 * (i.val + 1) - 2) n) : ℚ) * bernoulli n) :
      Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    ∧ (Matrix.of (fun i j : Fin (K - 1) =>
        (↑(Nat.choose (2 * K - 2 * (j.val + 1)) (2 * (i.val + 1) - 1)) : ℚ) +
          (↑(Nat.choose (2 * K - 2 * (j.val + 1)) (2 * K - 2 * (i.val + 1))) : ℚ)) :
      Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    * (Matrix.of (fun i j : Fin (K - 1) =>
        (2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1) *
          ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
            (↑(Nat.choose (2 * (j.val + 1) - 1)
              (2 * K - 2 * (i.val + 1) - n + 1)) : ℚ) *
              (↑(Nat.choose (n + 2 * (i.val + 1) - 2) n) : ℚ) * bernoulli n) :
      Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    = 1
    ∧ (Matrix.of (fun i j : Fin (K - 1) =>
        (2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1) *
          ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
            (↑(Nat.choose (2 * (j.val + 1) - 1)
              (2 * K - 2 * (i.val + 1) - n + 1)) : ℚ) *
              (↑(Nat.choose (n + 2 * (i.val + 1) - 2) n) : ℚ) * bernoulli n) :
      Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    * (Matrix.of (fun i j : Fin (K - 1) =>
        (↑(Nat.choose (2 * K - 2 * (j.val + 1)) (2 * (i.val + 1) - 1)) : ℚ) +
          (↑(Nat.choose (2 * K - 2 * (j.val + 1)) (2 * K - 2 * (i.val + 1))) : ℚ)) :
      Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    = 1 := by
  have hPQ := zagierInverseP_eq_zagierInverseQ K hK
  have hPA := zagierInverseP_mul_zagierMatrix K hK
  have hAP := zagierMatrix_mul_zagierInverseP K hK
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simpa only [Matrix.of_apply, zagierInverseP, zagierInverseQ] using congrFun (congrFun hPQ i) j
  · ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hAPij := congrFun (congrFun hAP i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at hAPij
    simpa only [Matrix.of_apply, zagierMatrix, zagierInverseP] using hAPij
  · ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hPAij := congrFun (congrFun hPA i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at hPAij
    simpa only [Matrix.of_apply, zagierInverseP, zagierMatrix] using hPAij

end MetaMathlibExt
end
