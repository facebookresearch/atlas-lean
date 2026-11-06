/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

private lemma conv_symm (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), k * (Nat.centralBinom k * Nat.centralBinom (N - k)) =
    ∑ k ∈ Finset.range (N + 1), (N - k) * (Nat.centralBinom k * Nat.centralBinom (N - k)) := by
  rw [← Finset.sum_range_reflect (fun k => k * (Nat.centralBinom k * Nat.centralBinom (N - k))) (N + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have e1 : N + 1 - 1 - j = N - j := by omega
  have e3 : N - (N - j) = j := Nat.sub_sub_self (by omega)
  rw [e1, e3, mul_comm (Nat.centralBinom (N - j)) (Nat.centralBinom j)]

private lemma conv_symm_succ (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), ((N - k) + 1) * (Nat.centralBinom k * Nat.centralBinom (N - k)) =
    ∑ k ∈ Finset.range (N + 1), (k + 1) * (Nat.centralBinom k * Nat.centralBinom (N - k)) := by
  rw [← Finset.sum_range_reflect (fun k => (k + 1) * (Nat.centralBinom k * Nat.centralBinom (N - k))) (N + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have e1 : N + 1 - 1 - j = N - j := by omega
  have e3 : N - (N - j) = j := Nat.sub_sub_self (by omega)
  rw [e1, e3, mul_comm (Nat.centralBinom (N - j)) (Nat.centralBinom j)]

/-- Convolution of central binomial coefficients equals `4 ^ n`. -/
private lemma conv_centralBinom (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.centralBinom k * Nat.centralBinom (n - k) = 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have step1 : (n + 1) * ∑ k ∈ Finset.range (n + 1 + 1),
            Nat.centralBinom k * Nat.centralBinom (n + 1 - k)
          = 2 * ∑ k ∈ Finset.range (n + 1 + 1),
            (n + 1 - k) * (Nat.centralBinom k * Nat.centralBinom (n + 1 - k)) := by
      have hpt : ∀ k ∈ Finset.range (n + 1 + 1),
          (n + 1) * (Nat.centralBinom k * Nat.centralBinom (n + 1 - k))
          = (n + 1 - k) * (Nat.centralBinom k * Nat.centralBinom (n + 1 - k))
            + k * (Nat.centralBinom k * Nat.centralBinom (n + 1 - k)) := by
        intro k hk
        simp only [Finset.mem_range] at hk
        have hkn : k ≤ n + 1 := by omega
        have e : (n + 1) * (Nat.centralBinom k * Nat.centralBinom (n + 1 - k))
            = ((n + 1 - k) + k) * (Nat.centralBinom k * Nat.centralBinom (n + 1 - k)) := by
          rw [Nat.sub_add_cancel hkn]
        rw [e, add_mul]
      have e1 : (∑ i ∈ Finset.range (n + 1 + 1),
            (n + 1) * (Nat.centralBinom i * Nat.centralBinom (n + 1 - i)))
          = ∑ i ∈ Finset.range (n + 1 + 1),
            ((n + 1 - i) * (Nat.centralBinom i * Nat.centralBinom (n + 1 - i))
              + i * (Nat.centralBinom i * Nat.centralBinom (n + 1 - i))) :=
        Finset.sum_congr rfl hpt
      rw [Finset.mul_sum, e1, Finset.sum_add_distrib, conv_symm (n + 1), two_mul]
    have step2 : (∑ k ∈ Finset.range (n + 1 + 1),
            (n + 1 - k) * (Nat.centralBinom k * Nat.centralBinom (n + 1 - k)))
          = 2 * ∑ k ∈ Finset.range (n + 1),
            (2 * (n - k) + 1) * (Nat.centralBinom k * Nat.centralBinom (n - k)) := by
      rw [Finset.sum_range_succ]
      have hlast : (n + 1 - (n + 1)) * (Nat.centralBinom (n + 1) * Nat.centralBinom (n + 1 - (n + 1))) = 0 := by simp
      rw [hlast, add_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      have hkn : k ≤ n := by omega
      have h3 : n + 1 - k = (n - k) + 1 := by omega
      have hcb : ((n - k) + 1) * Nat.centralBinom ((n - k) + 1)
          = 2 * (2 * (n - k) + 1) * Nat.centralBinom (n - k) :=
        Nat.succ_mul_centralBinom_succ (n - k)
      rw [h3]
      calc ((n - k) + 1) * (Nat.centralBinom k * Nat.centralBinom ((n - k) + 1))
          = Nat.centralBinom k * (((n - k) + 1) * Nat.centralBinom ((n - k) + 1)) := by ring
        _ = Nat.centralBinom k * (2 * (2 * (n - k) + 1) * Nat.centralBinom (n - k)) := by rw [hcb]
        _ = 2 * ((2 * (n - k) + 1) * (Nat.centralBinom k * Nat.centralBinom (n - k))) := by ring
    have step3 : (∑ k ∈ Finset.range (n + 1), (2 * (n - k) + 1) *
            (Nat.centralBinom k * Nat.centralBinom (n - k)))
          = (n + 1) * ∑ k ∈ Finset.range (n + 1),
            Nat.centralBinom k * Nat.centralBinom (n - k) := by
      have hpt : ∀ k ∈ Finset.range (n + 1),
          (2 * (n - k) + 1) * (Nat.centralBinom k * Nat.centralBinom (n - k))
          = (n - k) * (Nat.centralBinom k * Nat.centralBinom (n - k))
            + ((n - k) + 1) * (Nat.centralBinom k * Nat.centralBinom (n - k)) := by
        intro k hk
        have e : 2 * (n - k) + 1 = (n - k) + ((n - k) + 1) := by omega
        rw [e, add_mul]
      have e1 : (∑ k ∈ Finset.range (n + 1), (2 * (n - k) + 1) *
            (Nat.centralBinom k * Nat.centralBinom (n - k)))
          = ∑ k ∈ Finset.range (n + 1), ((n - k) * (Nat.centralBinom k * Nat.centralBinom (n - k))
            + ((n - k) + 1) * (Nat.centralBinom k * Nat.centralBinom (n - k))) :=
        Finset.sum_congr rfl hpt
      rw [e1, Finset.sum_add_distrib, conv_symm_succ n, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      have e : (n - k) + (k + 1) = n + 1 := by omega
      rw [← add_mul, e]
    have key : (n + 1) * ∑ k ∈ Finset.range (n + 1 + 1),
          Nat.centralBinom k * Nat.centralBinom (n + 1 - k)
        = (n + 1) * 4 ^ (n + 1) := by
      rw [step1, step2, step3, ih]
      ring
    exact mul_left_cancel₀ (by omega : (n : ℕ) + 1 ≠ 0) key

private lemma norm_centralBinom_le (n : ℕ) : ‖(Nat.centralBinom n : ℝ)‖ ≤ (4 : ℝ) ^ n := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast Nat.centralBinom_le_four_pow n

private lemma norm4x_lt_one (x : ℝ) (hx : |x| < 1 / 4) : ‖(4 * |x| : ℝ)‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := abs_nonneg x
  linarith

private lemma summable_centralBinom_mul (x : ℝ) (hx : |x| < 1 / 4) :
    Summable (fun n : ℕ => (Nat.centralBinom n : ℝ) * x ^ n) := by
  have hgeo := summable_geometric_of_norm_lt_one (norm4x_lt_one x hx)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hgeo
  intro n
  rw [norm_mul]
  have hC := norm_centralBinom_le n
  have hxp : ‖x ^ n‖ ≤ |x| ^ n := by
    rw [norm_pow, Real.norm_eq_abs]
  calc ‖(Nat.centralBinom n : ℝ)‖ * ‖x ^ n‖
      ≤ 4 ^ n * |x| ^ n := mul_le_mul hC hxp (norm_nonneg _) (by positivity)
    _ = (4 * |x|) ^ n := by rw [mul_pow]

private lemma summable_centralBinom_pow_mul (m : ℕ) (x : ℝ) (hx : |x| < 1 / 4) :
    Summable (fun n : ℕ => (Nat.centralBinom n : ℝ) * (n : ℝ) ^ m * x ^ n) := by
  have hgeo := summable_pow_mul_geometric_of_norm_lt_one m (norm4x_lt_one x hx)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hgeo
  intro n
  rw [norm_mul, norm_mul]
  have hC := norm_centralBinom_le n
  have hxp : ‖x ^ n‖ ≤ |x| ^ n := by
    rw [norm_pow, Real.norm_eq_abs]
  have hnp : ‖(n : ℝ) ^ m‖ ≤ (n : ℝ) ^ m := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : ‖(Nat.centralBinom n : ℝ)‖ * ‖(n : ℝ) ^ m‖ ≤ 4 ^ n * (n : ℝ) ^ m :=
    mul_le_mul hC hnp (norm_nonneg _) (by positivity)
  calc ‖(Nat.centralBinom n : ℝ)‖ * ‖(n : ℝ) ^ m‖ * ‖x ^ n‖
      ≤ (4 ^ n * (n : ℝ) ^ m) * |x| ^ n :=
        mul_le_mul h1 hxp (norm_nonneg _) (by positivity)
    _ = (n : ℝ) ^ m * (4 * |x|) ^ n := by ring

private lemma summable_centralBinom_desc (k : ℕ) (x : ℝ) (hx : |x| < 1 / 4) :
    Summable (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n) := by
  have hgeo := summable_pow_mul_geometric_of_norm_lt_one k (norm4x_lt_one x hx)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hgeo
  intro n
  rw [norm_mul, norm_mul]
  have hC := norm_centralBinom_le n
  have hxp : ‖x ^ n‖ ≤ |x| ^ n := by
    rw [norm_pow, Real.norm_eq_abs]
  have hdk : ‖(((n.descFactorial k : ℕ)) : ℝ)‖ ≤ (n : ℝ) ^ k := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.descFactorial_le_pow n k
  have h1 : ‖(Nat.centralBinom n : ℝ)‖ * ‖(((n.descFactorial k : ℕ)) : ℝ)‖
      ≤ 4 ^ n * (n : ℝ) ^ k :=
    mul_le_mul hC hdk (norm_nonneg _) (by positivity)
  calc ‖(Nat.centralBinom n : ℝ)‖ * ‖(((n.descFactorial k : ℕ)) : ℝ)‖ * ‖x ^ n‖
      ≤ (4 ^ n * (n : ℝ) ^ k) * |x| ^ n :=
        mul_le_mul h1 hxp (norm_nonneg _) (by positivity)
    _ = (n : ℝ) ^ k * (4 * |x|) ^ n := by ring

/-- Norm-summability for the Cauchy product. -/
private lemma summable_norm_centralBinom_mul (x : ℝ) (hx : |x| < 1 / 4) :
    Summable (fun n : ℕ => ‖(Nat.centralBinom n : ℝ) * x ^ n‖) := by
  have hgeo := summable_geometric_of_norm_lt_one (norm4x_lt_one x hx)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hgeo
  intro n
  rw [norm_mul]
  have hC := norm_centralBinom_le n
  have hxp : ‖x ^ n‖ ≤ |x| ^ n := by
    rw [norm_pow, Real.norm_eq_abs]
  calc ‖(Nat.centralBinom n : ℝ)‖ * ‖x ^ n‖
      ≤ 4 ^ n * |x| ^ n := mul_le_mul hC hxp (norm_nonneg _) (by positivity)
    _ = (4 * |x|) ^ n := by rw [mul_pow]

private lemma norm4x'_lt_one (x : ℝ) (hx : |x| < 1 / 4) : ‖(4 * x : ℝ)‖ < 1 := by
  have h4 : ‖(4 : ℝ)‖ = 4 := by rw [Real.norm_eq_abs]; norm_num
  rw [norm_mul, h4, Real.norm_eq_abs]
  have := abs_nonneg x
  linarith

/-- Square of the central binomial series via Cauchy product. -/
private lemma base_sq (x : ℝ) (hx : |x| < 1 / 4) :
    (∑' n : ℕ, (Nat.centralBinom n : ℝ) * x ^ n)
      * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * x ^ n) = (1 - 4 * x)⁻¹ := by
  have hSnorm := summable_norm_centralBinom_mul x hx
  have hCS := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hSnorm hSnorm
  have hanti : ∀ n : ℕ, (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((Nat.centralBinom kl.1 : ℝ) * x ^ kl.1 * ((Nat.centralBinom kl.2 : ℝ) * x ^ kl.2)))
      = (4 * x) ^ n := by
    intro n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (Nat.centralBinom i : ℝ) * x ^ i * ((Nat.centralBinom j : ℝ) * x ^ j)) n]
    have hpt : ∀ k ∈ Finset.range (n + 1),
        (Nat.centralBinom k : ℝ) * x ^ k * ((Nat.centralBinom (n - k) : ℝ) * x ^ (n - k))
        = ((Nat.centralBinom k * Nat.centralBinom (n - k) : ℕ) : ℝ) * x ^ n := by
      intro k hk
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
      rw [Nat.cast_mul, mul_mul_mul_comm, ← pow_add, Nat.add_sub_cancel' hk]
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_mul, ← Nat.cast_sum, conv_centralBinom n]
    push_cast
    ring
  rw [hCS, tsum_congr (fun n => hanti n),
    tsum_geometric_of_norm_lt_one (norm4x'_lt_one x hx)]

/-- Finite partial sums split into the first two terms plus consecutive pairs. -/
private lemma partial_pair (a : ℕ → ℝ) (J : ℕ) :
    ∑ n ∈ Finset.range (2 * J + 2), a n
      = a 0 + a 1 + ∑ j ∈ Finset.range J, (a (2 * j + 2) + a (2 * j + 3)) := by
  induction J with
  | zero => simp [Finset.sum_range_succ]
  | succ J ih =>
    rw [show 2 * (J + 1) + 2 = (2 * J + 2 + 1) + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- Each consecutive even-odd pair is nonnegative for negative `x`. -/
private lemma pair_nonneg (x : ℝ) (hx : |x| < 1 / 4) (hxn : x < 0) (j : ℕ) :
    0 ≤ (Nat.centralBinom (2 * j + 2) : ℝ) * x ^ (2 * j + 2)
      + (Nat.centralBinom (2 * j + 3) : ℝ) * x ^ (2 * j + 3) := by
  have hxabs : |x| = -x := abs_of_neg hxn
  have hxx : x = -|x| := by rw [hxabs, neg_neg]
  have heven : Even (2 * j + 2) := ⟨j + 1, by ring⟩
  have hodd : Odd (2 * j + 3) := ⟨j + 1, by ring⟩
  have e1 : x ^ (2 * j + 2) = |x| ^ (2 * j + 2) := by
    conv_lhs => rw [hxx]
    exact heven.neg_pow _
  have e2 : x ^ (2 * j + 3) = -|x| ^ (2 * j + 3) := by
    conv_lhs => rw [hxx]
    exact hodd.neg_pow _
  have hC : ((2 * j + 3 : ℕ) : ℝ) * (Nat.centralBinom (2 * j + 3) : ℝ)
      = 2 * (2 * (2 * j + 2) + 1) * (Nat.centralBinom (2 * j + 2) : ℝ) := by
    have h := Nat.succ_mul_centralBinom_succ (2 * j + 2)
    have e : 2 * j + 2 + 1 = 2 * j + 3 := by omega
    rw [e] at h
    exact_mod_cast h
  have hcast : ((2 * j + 3 : ℕ) : ℝ) = 2 * (j : ℝ) + 3 := by push_cast; ring
  rw [hcast] at hC
  rw [e1, e2]
  have hCnn : (0 : ℝ) ≤ (Nat.centralBinom (2 * j + 2) : ℝ) := Nat.cast_nonneg _
  have h14 : (0 : ℝ) ≤ 1 / 4 - |x| := by
    have := abs_nonneg x
    linarith
  have h812 : (0 : ℝ) ≤ 8 * (j : ℝ) + 12 := by positivity
  have hprod1 : (0 : ℝ) ≤ (1 / 4 - |x|) * ((8 * (j : ℝ) + 12) * (Nat.centralBinom (2 * j + 2) : ℝ)) :=
    mul_nonneg h14 (mul_nonneg h812 hCnn)
  have hprod2 : (0 : ℝ) ≤ 2 * |x| * (Nat.centralBinom (2 * j + 2) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hCnn
  have hG : (0 : ℝ) ≤ (2 * (j : ℝ) + 3)
      * ((Nat.centralBinom (2 * j + 2) : ℝ) - |x| * (Nat.centralBinom (2 * j + 3) : ℝ)) := by
    nlinarith [hC, hprod1, hprod2]
  have hpos23 : (0 : ℝ) < 2 * (j : ℝ) + 3 := by positivity
  have hdiff : (0 : ℝ) ≤ (Nat.centralBinom (2 * j + 2) : ℝ)
      - |x| * (Nat.centralBinom (2 * j + 3) : ℝ) := by
    by_contra hlt
    push Not at hlt
    have hneg : (2 * (j : ℝ) + 3)
        * ((Nat.centralBinom (2 * j + 2) : ℝ) - |x| * (Nat.centralBinom (2 * j + 3) : ℝ)) < 0 :=
      mul_neg_of_pos_of_neg hpos23 hlt
    linarith
  have hfactor : (Nat.centralBinom (2 * j + 2) : ℝ) * |x| ^ (2 * j + 2)
      + (Nat.centralBinom (2 * j + 3) : ℝ) * -|x| ^ (2 * j + 3)
      = |x| ^ (2 * j + 2)
        * ((Nat.centralBinom (2 * j + 2) : ℝ) - |x| * (Nat.centralBinom (2 * j + 3) : ℝ)) := by
    rw [show (2 * j + 3 : ℕ) = (2 * j + 2) + 1 by omega, pow_succ]
    ring
  rw [hfactor]
  exact mul_nonneg (pow_nonneg (abs_nonneg _) _) hdiff

/-- The central binomial series is positive on `|x| < 1/4`. -/
private lemma base_pos (x : ℝ) (hx : |x| < 1 / 4) :
    0 < ∑' n : ℕ, (Nat.centralBinom n : ℝ) * x ^ n := by
  have hS := summable_centralBinom_mul x hx
  have h12 : (1 : ℝ) - 2 * |x| > 1 / 2 := by
    have hab := abs_nonneg x
    linarith
  suffices h : (1 : ℝ) - 2 * |x| ≤ ∑' n : ℕ, (Nat.centralBinom n : ℝ) * x ^ n by linarith
  by_cases hx0 : 0 ≤ x
  · have hxabs : |x| = x := abs_of_nonneg hx0
    rw [hxabs]
    have hge1 : ∀ N : ℕ, 1 ≤ N →
        (1 : ℝ) ≤ ∑ n ∈ Finset.range N, (Nat.centralBinom n : ℝ) * x ^ n := by
      intro N hN
      have h0 : 0 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      have hnn : ∀ i ∈ Finset.range N, (0 : ℝ) ≤ (Nat.centralBinom i : ℝ) * x ^ i := by
        intro i _
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _)
      have hle := Finset.single_le_sum hnn h0
      have ha0 : (Nat.centralBinom 0 : ℝ) * x ^ 0 = 1 := by simp
      rw [ha0] at hle
      exact hle
    have hlim := hS.hasSum.tendsto_sum_nat
    have hev : ∀ᶠ N in Filter.atTop,
        (1 : ℝ) ≤ ∑ n ∈ Finset.range N, (Nat.centralBinom n : ℝ) * x ^ n := by
      rw [Filter.eventually_atTop]
      exact ⟨1, fun N hN => hge1 N hN⟩
    have hle := ge_of_tendsto hlim hev
    linarith
  · have hxn : x < 0 := lt_of_not_ge hx0
    have hxabs : |x| = -x := abs_of_neg hxn
    rw [hxabs]
    have hge : ∀ J : ℕ, (Nat.centralBinom 0 : ℝ) * x ^ 0 + (Nat.centralBinom 1 : ℝ) * x ^ 1
        ≤ ∑ n ∈ Finset.range (2 * J + 2), (Nat.centralBinom n : ℝ) * x ^ n := by
      intro J
      have h2 := partial_pair (fun n : ℕ => (Nat.centralBinom n : ℝ) * x ^ n) J
      rw [h2]
      have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range J,
          ((Nat.centralBinom (2 * j + 2) : ℝ) * x ^ (2 * j + 2)
            + (Nat.centralBinom (2 * j + 3) : ℝ) * x ^ (2 * j + 3)) :=
        Finset.sum_nonneg (fun j _ => pair_nonneg x hx hxn j)
      linarith
    have hlim : Filter.Tendsto
        (fun J => ∑ n ∈ Finset.range (2 * J + 2), (Nat.centralBinom n : ℝ) * x ^ n)
        Filter.atTop (nhds (∑' n : ℕ, (Nat.centralBinom n : ℝ) * x ^ n)) :=
      hS.hasSum.tendsto_sum_nat.comp
        ((strictMono_nat_of_lt_succ
          (fun J => by omega : ∀ J, 2 * J + 2 < 2 * (J + 1) + 2)).tendsto_atTop)
    have hle := ge_of_tendsto hlim (Filter.Eventually.of_forall hge)
    have c1 : Nat.centralBinom 1 = 2 := by decide
    have ha01 : (Nat.centralBinom 0 : ℝ) * x ^ 0 + (Nat.centralBinom 1 : ℝ) * x ^ 1
        = 1 + 2 * x := by
      rw [Nat.centralBinom_zero, c1]
      push_cast
      ring
    rw [ha01] at hle
    linarith

/-- The central binomial generating function. -/
private lemma base_eq (x : ℝ) (hx : |x| < 1 / 4) :
    ∑' n : ℕ, (Nat.centralBinom n : ℝ) * x ^ n = 1 / Real.sqrt (1 - 4 * x) := by
  have hpos14 : (0 : ℝ) < 1 - 4 * x := by
    have hle := le_abs_self x
    linarith
  have hS := base_sq x hx
  have hT2 : (1 / Real.sqrt (1 - 4 * x)) ^ 2 = (1 - 4 * x)⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hpos14), one_div]
  have hSpos := base_pos x hx
  have hTpos : (0 : ℝ) < 1 / Real.sqrt (1 - 4 * x) :=
    one_div_pos.mpr (Real.sqrt_pos.mpr hpos14)
  have heq : (∑' n : ℕ, (Nat.centralBinom n : ℝ) * x ^ n) ^ 2
      = (1 / Real.sqrt (1 - 4 * x)) ^ 2 := by
    rw [pow_two, hS]
    exact hT2.symm
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp heq) with h | h
  · exact h
  · linarith

/-- Pointwise shift relation: `(n+1-k) a_{n+1} = 2(2n+1) x a_n`. -/
private lemma pw_shift (k n : ℕ) (x : ℝ) :
    ((n : ℝ) + 1 - (k : ℝ))
      * ((Nat.centralBinom (n + 1) : ℝ) * ((((n + 1).descFactorial k)) : ℕ) : ℝ) * x ^ (n + 1)
    = 2 * (2 * (n : ℝ) + 1) * x
      * ((Nat.centralBinom n : ℝ) * ((((n.descFactorial k)) : ℕ) : ℝ) * x ^ n) := by
  have hCrec : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    have h := Nat.succ_mul_centralBinom_succ n
    have hc := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at hc
    linear_combination hc
  by_cases h : k ≤ n + 1
  · have hd1adj : ((n : ℝ) + 1 - (k : ℝ)) * (((n + 1).descFactorial k : ℕ) : ℝ)
      = ((((n + 1).descFactorial (k + 1)) : ℕ) : ℝ) := by
      have h1 : (n + 1).descFactorial (k + 1) = (n + 1 - k) * (n + 1).descFactorial k :=
        Nat.descFactorial_succ (n + 1) k
      have hc := congrArg (Nat.cast : ℕ → ℝ) h1
      push_cast at hc
      rw [Nat.cast_sub h] at hc
      push_cast at hc
      linear_combination -hc
    have hd2adj : ((((n + 1).descFactorial (k + 1)) : ℕ) : ℝ)
        = ((n : ℝ) + 1) * (((n.descFactorial k : ℕ)) : ℝ) := by
      have h2 := Nat.succ_descFactorial_succ n k
      have hc := congrArg (Nat.cast : ℕ → ℝ) h2
      push_cast at hc
      linear_combination hc
    linear_combination (x ^ (n + 1) * ((((n.descFactorial k) : ℕ)) : ℝ)) * hCrec
      + ((Nat.centralBinom (n + 1) : ℝ) * x ^ (n + 1)) * hd1adj
      + ((Nat.centralBinom (n + 1) : ℝ) * x ^ (n + 1)) * hd2adj
  · have h1 : n + 1 < k := by omega
    have h2 : n < k := by omega
    have z1 : (n + 1).descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h1
    have z0 : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h2
    rw [z1, z0]
    simp

/-- Pointwise: `n (n)_k = (n)_{k+1} + k (n)_k` over `ℝ`. -/
private lemma pw_falling (n k : ℕ) :
    (n : ℝ) * ((((n.descFactorial k)) : ℕ) : ℝ)
    = ((((n.descFactorial (k + 1))) : ℕ) : ℝ) + (k : ℝ) * ((((n.descFactorial k)) : ℕ) : ℝ) := by
  by_cases h : k ≤ n
  · have hsub : (((n - k : ℕ)) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub h
    have hd : n.descFactorial (k + 1) = (n - k) * n.descFactorial k :=
      Nat.descFactorial_succ n k
    have hc := congrArg (Nat.cast : ℕ → ℝ) hd
    push_cast at hc
    rw [hsub] at hc
    linear_combination -hc
  · have h1 : n < k := by omega
    have z0 : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h1
    have z1 : n.descFactorial (k + 1) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [z0, z1]
    simp

/-- Recurrence for the falling-factorial-weighted sums. -/
private lemma step_rec (k : ℕ) (x : ℝ) (hx : |x| < 1 / 4) :
    ∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial (k + 1) : ℕ) : ℝ) * x ^ n
    = (2 * x * (2 * (k : ℝ) + 1) / (1 - 4 * x))
      * ∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n := by
  have h14 : (1 : ℝ) - 4 * x ≠ 0 := by
    have hle := le_abs_self x
    have hlt : x < 1 / 4 := lt_of_le_of_lt hle hx
    have hpos : (0 : ℝ) < 1 - 4 * x := by linarith
    exact ne_of_gt hpos
  have hsT := summable_centralBinom_desc k x hx
  have hsT' := summable_centralBinom_desc (k + 1) x hx
  have hpt : ∀ n : ℕ, (n : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)
      = (Nat.centralBinom n : ℝ) * ((n.descFactorial (k + 1) : ℕ) : ℝ) * x ^ n
        + (k : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n) := by
    intro n
    have h := pw_falling n k
    linear_combination ((Nat.centralBinom n : ℝ) * x ^ n) * h
  have hsU : Summable (fun n : ℕ => (n : ℝ)
      * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)) :=
    Summable.congr (hsT'.add (hsT.mul_left (k : ℝ))) (fun n => (hpt n).symm)
  have hshU : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ)
      * ((Nat.centralBinom (n + 1) : ℝ) * (((n + 1).descFactorial k : ℕ) : ℝ) * x ^ (n + 1)))
      (∑' n : ℕ, (n : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)) := by
    have hshift_summ := (summable_nat_add_iff 1).mpr hsU
    have hV := hshift_summ.hasSum
    have hU' := (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ)
      * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)) 1).mp hV
    rw [Finset.sum_range_one] at hU'
    have hSeq : (∑' n : ℕ, (fun m : ℕ => (m : ℝ)
        * ((Nat.centralBinom m : ℝ) * ((m.descFactorial k : ℕ) : ℝ) * x ^ m)) (n + 1))
        = (∑' n : ℕ, (n : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n))
          - ((0 : ℕ) : ℝ)
            * ((Nat.centralBinom 0 : ℝ) * (((0).descFactorial k : ℕ) : ℝ) * x ^ 0) := by
      have huniq := HasSum.unique hU' hsU.hasSum
      linarith
    rw [hSeq] at hV
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hV
    exact hV
  have hshT : HasSum (fun n : ℕ => (Nat.centralBinom (n + 1) : ℝ)
      * (((n + 1).descFactorial k : ℕ) : ℝ) * x ^ (n + 1))
      ((∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)
        - (Nat.centralBinom 0 : ℝ) * (((0).descFactorial k : ℕ) : ℝ) * x ^ 0) := by
    have hshift_summ := (summable_nat_add_iff 1).mpr hsT
    have hV := hshift_summ.hasSum
    have hT' := (hasSum_nat_add_iff (f := fun n : ℕ => (Nat.centralBinom n : ℝ)
      * ((n.descFactorial k : ℕ) : ℝ) * x ^ n) 1).mp hV
    rw [Finset.sum_range_one] at hT'
    have hSeq : (∑' n : ℕ, (fun m : ℕ => (Nat.centralBinom m : ℝ)
        * ((m.descFactorial k : ℕ) : ℝ) * x ^ m) (n + 1))
        = (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)
          - (Nat.centralBinom 0 : ℝ) * (((0).descFactorial k : ℕ) : ℝ) * x ^ 0 := by
      have huniq := HasSum.unique hT' hsT.hasSum
      linarith
    rw [hSeq] at hV
    exact hV
  have hLHS : HasSum (fun n : ℕ => ((n : ℝ) + 1 - (k : ℝ))
      * ((Nat.centralBinom (n + 1) : ℝ) * (((n + 1).descFactorial k : ℕ) : ℝ)) * x ^ (n + 1))
      ((∑' n : ℕ, (n : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n))
        - (k : ℝ) * ((∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)
          - (Nat.centralBinom 0 : ℝ) * (((0).descFactorial k : ℕ) : ℝ) * x ^ 0)) := by
    have h1 := hshU.sub (hshT.mul_left (k : ℝ))
    refine HasSum.congr_fun h1 (fun n => ?_)
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
    rw [hc]
    ring
  have hRHS : HasSum (fun n : ℕ => 2 * (2 * (n : ℝ) + 1) * x
      * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n))
      (4 * x * (∑' n : ℕ, (n : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n))
        + 2 * x * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)) := by
    have h1 := (hsU.hasSum.mul_left (4 * x)).add (hsT.hasSum.mul_left (2 * x))
    refine HasSum.congr_fun h1 (fun n => ?_)
    ring
  have hVals : (∑' n : ℕ, (n : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n))
      - (k : ℝ) * ((∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)
        - (Nat.centralBinom 0 : ℝ) * (((0).descFactorial k : ℕ) : ℝ) * x ^ 0)
      = 4 * x * (∑' n : ℕ, (n : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n))
        + 2 * x * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n) :=
    HasSum.unique
      (HasSum.congr_fun hLHS (fun n => (pw_shift k n x).symm)) hRHS
  have hk_a0 : (k : ℝ) * ((Nat.centralBinom 0 : ℝ) * (((0).descFactorial k : ℕ) : ℝ) * x ^ 0) = 0 := by
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have z : (0).descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hpos
      rw [z]
      simp
  have h_alg1 : (∑' n : ℕ, (n : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n))
      * (1 - 4 * x)
      = ((k : ℝ) + 2 * x)
        * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n) := by
    linear_combination hVals - hk_a0
  have hUeq : (∑' n : ℕ, (n : ℝ) * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n))
      = (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial (k + 1) : ℕ) : ℝ) * x ^ n)
        + (k : ℝ) * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n) := by
    have h1 := hsT'.hasSum.add (hsT.hasSum.mul_left (k : ℝ))
    have h2 : HasSum (fun n : ℕ => (n : ℝ)
        * ((Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n))
        ((∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial (k + 1) : ℕ) : ℝ) * x ^ n)
          + (k : ℝ) * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n)) :=
      HasSum.congr_fun h1 (fun n => hpt n)
    exact (HasSum.unique h2 hsU.hasSum).symm
  have hfin : (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial (k + 1) : ℕ) : ℝ) * x ^ n)
      = 2 * x * (2 * (k : ℝ) + 1)
        * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n) / (1 - 4 * x) := by
    rw [eq_div_iff h14]
    linear_combination h_alg1 - (1 - 4 * x) * hUeq
  rw [div_mul_eq_mul_div]
  exact hfin

/-- Closed form for the falling-factorial-weighted sums, by induction. -/
private lemma closed_form (k : ℕ) (x : ℝ) (hx : |x| < 1 / 4) :
    ∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial k : ℕ) : ℝ) * x ^ n
    = (Nat.centralBinom k : ℝ) * ((k.factorial : ℕ) : ℝ) * (x / (1 - 4 * x)) ^ k
      * (1 / Real.sqrt (1 - 4 * x)) := by
  have h14 : (1 : ℝ) - 4 * x ≠ 0 := by
    have hle := le_abs_self x
    have hlt : x < 1 / 4 := lt_of_le_of_lt hle hx
    have hpos : (0 : ℝ) < 1 - 4 * x := by linarith
    exact ne_of_gt hpos
  induction k with
  | zero =>
    simp only [Nat.descFactorial_zero, Nat.factorial_zero, Nat.centralBinom_zero,
      pow_zero, Nat.cast_one, mul_one, one_mul]
    exact base_eq x hx
  | succ k ih =>
    rw [step_rec k x hx, ih]
    have hCB : (Nat.centralBinom (k + 1) : ℝ) * ((((k + 1).factorial) : ℕ) : ℝ)
        = 2 * (2 * (k : ℝ) + 1) * ((Nat.centralBinom k : ℝ) * (((k.factorial) : ℕ) : ℝ)) := by
      have h := Nat.succ_mul_centralBinom_succ k
      have hf : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
      have hc := congrArg (Nat.cast : ℕ → ℝ) h
      have hfc := congrArg (Nat.cast : ℕ → ℝ) hf
      push_cast at hc hfc
      linear_combination (((k.factorial : ℕ)) : ℝ) * hc
        + (Nat.centralBinom (k + 1) : ℝ) * hfc
    rw [hCB, pow_succ]
    field_simp

/-- Swap a finite sum with a `tsum`. -/
private lemma tsum_finset_sum {s : Finset ℕ} {G : ℕ → ℕ → ℝ} (h : ∀ j ∈ s, Summable (G j)) :
    (∑' n, ∑ j ∈ s, G j n) = ∑ j ∈ s, ∑' n, G j n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' has ih =>
    have ha : Summable (G a) := h _ (Finset.mem_insert_self a s')
    have hs' : ∀ j ∈ s', Summable (G j) := fun j hj => h _ (Finset.mem_insert_of_mem hj)
    have iheq := ih hs'
    have e : (fun n => ∑ j ∈ insert a s', G j n)
        = (fun n => G a n + ∑ j ∈ s', G j n) :=
      funext (fun n => Finset.sum_insert has)
    rw [e, Summable.tsum_add ha (summable_sum hs'), iheq, Finset.sum_insert has]

/--
**Central binomial power sums via Stirling numbers.** For every natural number $m$ and every
real $x$ with $|x| < 1/4$,
$$\sum_{n=0}^{\infty} \binom{2n}{n} n^m x^n =
\frac{1}{\sqrt{1-4x}} \sum_{k=0}^{m} S(m,k) \binom{2k}{k}\, k! \left(\frac{x}{1-4x}\right)^k,$$
where $S(m,k)$ denotes the Stirling numbers of the second kind (and $n^0 = 1$ for every $n$).

The source asks for positive $m$; the identity also holds at $m = 0$, where both sides are the
generating function of the central binomial coefficients.

Proves `Wanted` entry `central_binom_power_sum_stirling`.

Source: Khristo N. Boyadzhiev, "Series with Central Binomial Coefficients,
Catalan Numbers, and Harmonic Numbers," Journal of Integer Sequences 15
(2012), Article 12.1.7, Theorem (label t3, equation 8), lines 155–160,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Boyadzhiev/boyadzhiev6.tex
-/
theorem central_binom_power_sum_stirling
    (m : ℕ) (x : ℝ) (hx : |x| < 1 / 4) :
    ∑' n : ℕ, (Nat.centralBinom n : ℝ) * (n : ℝ) ^ m * x ^ n =
      1 / Real.sqrt (1 - 4 * x) *
        ∑ k ∈ Finset.range (m + 1),
          (Nat.stirlingSecond m k : ℝ) * (Nat.centralBinom k : ℝ) *
            (Nat.factorial k : ℝ) * (x / (1 - 4 * x)) ^ k := by
  have hSt : ∀ n : ℕ, (n : ℝ) ^ m
      = ∑ j ∈ Finset.range (m + 1), ((Nat.stirlingSecond m j : ℕ) : ℝ)
        * (((n.descFactorial j) : ℕ) : ℝ) := by
    intro n
    have h := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n m
    have hc := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at hc
    linear_combination hc
  have hLHS : (∑' n : ℕ, (Nat.centralBinom n : ℝ) * (n : ℝ) ^ m * x ^ n)
      = ∑ j ∈ Finset.range (m + 1), ((Nat.stirlingSecond m j : ℕ) : ℝ)
        * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial j : ℕ) : ℝ) * x ^ n) := by
    have hpt : ∀ n : ℕ, (Nat.centralBinom n : ℝ) * (n : ℝ) ^ m * x ^ n
        = ∑ j ∈ Finset.range (m + 1), ((Nat.stirlingSecond m j : ℕ) : ℝ)
          * ((Nat.centralBinom n : ℝ) * (((n.descFactorial j) : ℕ) : ℝ) * x ^ n) := by
      intro n
      rw [hSt n, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hmid : (∑' n : ℕ, ∑ j ∈ Finset.range (m + 1),
          ((Nat.stirlingSecond m j : ℕ) : ℝ)
            * ((Nat.centralBinom n : ℝ) * (((n.descFactorial j) : ℕ) : ℝ) * x ^ n))
        = ∑ j ∈ Finset.range (m + 1), ((Nat.stirlingSecond m j : ℕ) : ℝ)
          * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial j : ℕ) : ℝ) * x ^ n) := by
      have hswap := tsum_finset_sum (s := Finset.range (m + 1))
        (G := fun j n => ((Nat.stirlingSecond m j : ℕ) : ℝ)
          * ((Nat.centralBinom n : ℝ) * (((n.descFactorial j) : ℕ) : ℝ) * x ^ n))
        (fun j _ => (summable_centralBinom_desc j x hx).mul_left _)
      have hpull : ∀ j ∈ Finset.range (m + 1),
          (∑' n : ℕ, ((Nat.stirlingSecond m j : ℕ) : ℝ)
            * ((Nat.centralBinom n : ℝ) * (((n.descFactorial j) : ℕ) : ℝ) * x ^ n))
          = ((Nat.stirlingSecond m j : ℕ) : ℝ)
            * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial j : ℕ) : ℝ) * x ^ n) :=
        fun j _ => tsum_mul_left
      calc (∑' n : ℕ, ∑ j ∈ Finset.range (m + 1),
              ((Nat.stirlingSecond m j : ℕ) : ℝ)
                * ((Nat.centralBinom n : ℝ) * (((n.descFactorial j) : ℕ) : ℝ) * x ^ n))
          = ∑ j ∈ Finset.range (m + 1), ∑' n : ℕ,
              ((Nat.stirlingSecond m j : ℕ) : ℝ)
                * ((Nat.centralBinom n : ℝ) * (((n.descFactorial j) : ℕ) : ℝ) * x ^ n) := hswap
        _ = ∑ j ∈ Finset.range (m + 1), ((Nat.stirlingSecond m j : ℕ) : ℝ)
            * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial j : ℕ) : ℝ) * x ^ n) :=
          Finset.sum_congr rfl hpull
    exact (tsum_congr hpt).trans hmid
  rw [hLHS]
  have hF : ∀ j ∈ Finset.range (m + 1),
      ((Nat.stirlingSecond m j : ℕ) : ℝ)
        * (∑' n : ℕ, (Nat.centralBinom n : ℝ) * ((n.descFactorial j : ℕ) : ℝ) * x ^ n)
      = 1 / Real.sqrt (1 - 4 * x) * (((Nat.stirlingSecond m j : ℕ) : ℝ)
        * (Nat.centralBinom j : ℝ) * ((j.factorial : ℕ) : ℝ) * (x / (1 - 4 * x)) ^ j) := by
    intro j _
    rw [closed_form j x hx]
    ring
  rw [Finset.sum_congr rfl hF, ← Finset.mul_sum]

end MetaMathlibExt
