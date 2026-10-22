/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Bernoulli

import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

private noncomputable def catalanExpBernoulliPolynomialEval (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.bernoulli n)

private lemma catalanExp_bernoulliPolynomialEval_eq (n : ℕ) (x : ℝ) :
    catalanExpBernoulliPolynomialEval n x =
      Polynomial.aeval x (Polynomial.bernoulli n) := rfl

private lemma catalanExp_hasseDeriv_bernoulli (n k : ℕ) :
    Polynomial.hasseDeriv k (Polynomial.bernoulli n) =
      (n.choose k : ℚ) • Polynomial.bernoulli (n - k) := by
  ext i
  rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_bernoulli,
    Polynomial.coeff_smul, Polynomial.coeff_bernoulli]
  by_cases hik : i + k ≤ n
  · rw [ite_eq_left hik, ite_eq_left (by omega : i ≤ n - k)]
    have hc : (i + k).choose k * n.choose (i + k) =
        n.choose k * (n - k).choose i := by
      have hc' := Nat.choose_mul (n := n) (k := i + k) (s := k) (by omega)
      rw [show i + k - k = i by omega] at hc'
      simpa only [mul_comm] using hc'
    rw [show n - (i + k) = n - k - i by omega]
    have hc' : ((i + k).choose k : ℚ) * n.choose (i + k) =
        n.choose k * (n - k).choose i := by exact_mod_cast hc
    linear_combination (bernoulli (n - k - i) : ℚ) * hc'
  · rw [ite_eq_right hik]
    by_cases hk : k ≤ n
    · rw [ite_eq_right (by omega : ¬i ≤ n - k)]
      simp
    · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]

private lemma catalanExp_bernoulli_eval_add (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli (n - k)).eval x * y ^ k := by
  have htaylor : Polynomial.taylor x (Polynomial.bernoulli n) =
      ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k
        ((n.choose k : ℚ) * (Polynomial.bernoulli (n - k)).eval x) := by
    ext k
    rw [Polynomial.taylor_coeff, catalanExp_hasseDeriv_bernoulli,
      Polynomial.eval_smul]
    by_cases hk : k ≤ n
    · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
      · simp
      · intro b hb hbk
        rw [Polynomial.coeff_monomial, ite_eq_right hbk]
      · simp [hk]
    · have hkn : n < k := by omega
      rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_smul,
        Polynomial.finsetSum_coeff]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have hbn : b ≤ n := by simpa using (Finset.mem_range.mp hb)
      have hbk : b ≠ k := by omega
      rw [Polynomial.coeff_monomial, ite_eq_right hbk]
  calc
    (Polynomial.bernoulli n).eval (x + y) =
        (Polynomial.taylor x (Polynomial.bernoulli n)).eval y := by
      rw [Polynomial.taylor_eval, add_comm]
    _ = _ := by
      rw [htaylor, Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Polynomial.eval_monomial]

private lemma catalanExp_bernoulli_eval_add' (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * y ^ (n - k) := by
  rw [catalanExp_bernoulli_eval_add, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega]
  rw [show n - (n - k) = k by omega, Nat.choose_symm hkn]

private lemma catalanExp_pow_mul_inv_pow {a : ℚ} (ha : a ≠ 0) {k n : ℕ} (hkn : k ≤ n) :
    a ^ n * a⁻¹ ^ (n - k) = a ^ k := by
  rw [inv_pow, ← pow_sub_mul_pow a hkn]
  field_simp

private lemma catalanExp_sum_range_even_odd {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2), f k =
      ∑ r ∈ Finset.range (m + 1), (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ m ih =>
      conv_lhs =>
        rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [ih]
      simp only [show 2 * m + 2 = 2 * (m + 1) by omega,
        show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by omega, add_assoc]

private lemma catalanExp_bernoulli_eval_half_odd (m : ℕ) :
    (Polynomial.bernoulli (2 * m + 1)).eval (1 / 2 : ℚ) = 0 := by
  have h := Polynomial.bernoulli_eval_one_sub (2 * m + 1) (1 / 2 : ℚ)
  norm_num [Even.neg_one_pow, Odd.neg_one_pow, show Odd (2 * m + 1) from ⟨m, by omega⟩] at h
  linarith

private lemma catalanExp_bernoulli_eval_zero_odd (m : ℕ) (hm : 0 < m) :
    (Polynomial.bernoulli (2 * m + 1)).eval 0 = 0 := by
  rw [Polynomial.bernoulli_eval_zero,
    bernoulli_eq_zero_of_odd (⟨m, by omega⟩ : Odd (2 * m + 1)) (by omega)]

private lemma catalanExp_weighted_bernoulli_add (n : ℕ) (x a : ℚ) (ha : a ≠ 0) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * a ^ k =
      a ^ n * (Polynomial.bernoulli n).eval (x + a⁻¹) := by
  rw [catalanExp_bernoulli_eval_add', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  calc
    (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * a ^ k =
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x *
          (a ^ n * a⁻¹ ^ (n - k)) := by
      rw [catalanExp_pow_mul_inv_pow ha hkn]
    _ = a ^ n * ((n.choose k : ℚ) * (Polynomial.bernoulli k).eval x *
          a⁻¹ ^ (n - k)) := by ring

private lemma catalanExp_odd_weighted_bernoulli_sum (m : ℕ) (hm : 0 < m) :
    ∑ r ∈ Finset.range (m + 1),
        ((2 * m + 1).choose (2 * r + 1) : ℚ) *
          (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
            (4 : ℚ) ^ (2 * r + 1) = 0 := by
  have hplus : (∑ k ∈ Finset.range (2 * m + 2),
      ((2 * m + 1).choose k : ℚ) *
        (Polynomial.bernoulli k).eval (1 / 4) * (4 : ℚ) ^ k) = 0 := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
      catalanExp_weighted_bernoulli_add (2 * m + 1) (1 / 4) 4 (by norm_num)]
    norm_num [catalanExp_bernoulli_eval_half_odd]
  have hminus : (∑ k ∈ Finset.range (2 * m + 2),
      ((2 * m + 1).choose k : ℚ) *
        (Polynomial.bernoulli k).eval (1 / 4) * (-4 : ℚ) ^ k) = 0 := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
      catalanExp_weighted_bernoulli_add (2 * m + 1) (1 / 4) (-4) (by norm_num)]
    norm_num [catalanExp_bernoulli_eval_zero_odd m hm]
  let f : ℕ → ℚ := fun k => ((2 * m + 1).choose k : ℚ) *
    (Polynomial.bernoulli k).eval (1 / 4) * ((4 : ℚ) ^ k - (-4 : ℚ) ^ k)
  have hdiff : ∑ k ∈ Finset.range (2 * m + 2), f k = 0 := by
    calc
      ∑ k ∈ Finset.range (2 * m + 2), f k =
          (∑ k ∈ Finset.range (2 * m + 2),
            ((2 * m + 1).choose k : ℚ) *
              (Polynomial.bernoulli k).eval (1 / 4) * (4 : ℚ) ^ k) -
          ∑ k ∈ Finset.range (2 * m + 2),
            ((2 * m + 1).choose k : ℚ) *
              (Polynomial.bernoulli k).eval (1 / 4) * (-4 : ℚ) ^ k := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [f]
        ring
      _ = 0 := by rw [hplus, hminus, sub_zero]
  rw [catalanExp_sum_range_even_odd f m] at hdiff
  have hpair (r : ℕ) : f (2 * r) + f (2 * r + 1) =
      2 * (((2 * m + 1).choose (2 * r + 1) : ℚ) *
        (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
          (4 : ℚ) ^ (2 * r + 1)) := by
    have heven : Even (2 * r) := ⟨r, by omega⟩
    have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
    dsimp [f]
    rw [neg_pow, heven.neg_one_pow, neg_pow, hodd.neg_one_pow]
    ring
  simp_rw [hpair] at hdiff
  rw [← Finset.mul_sum] at hdiff
  linarith

private noncomputable def catalanExpEulerEvenQ (m : ℕ) : ℚ :=
  -(4 : ℚ) ^ (2 * m + 1) *
      (Polynomial.bernoulli (2 * m + 1)).eval (1 / 4) / (2 * m + 1 : ℕ)

private lemma catalanExpEulerEvenQ_zero : catalanExpEulerEvenQ 0 = 1 := by
  norm_num [catalanExpEulerEvenQ, Polynomial.bernoulli_one]

private lemma catalanExpEulerEvenQ_recurrence (m : ℕ) :
    ∑ r ∈ Finset.range (m + 1),
        ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [catalanExpEulerEvenQ_zero]
  · rw [ite_eq_right hm]
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hterm (r : ℕ) : ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r =
        -(1 / (2 * m + 1 : ℚ)) *
          (((2 * m + 1).choose (2 * r + 1) : ℚ) *
            (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
              (4 : ℚ) ^ (2 * r + 1)) := by
      have hc := Nat.add_one_mul_choose_eq (2 * m) (2 * r)
      have hc' : (2 * m + 1 : ℚ) * (2 * m).choose (2 * r) =
          ((2 * m + 1).choose (2 * r + 1) : ℚ) * (2 * r + 1) := by
        exact_mod_cast hc
      have hratio : ((2 * m).choose (2 * r) : ℚ) / (2 * r + 1 : ℕ) =
          ((2 * m + 1).choose (2 * r + 1) : ℚ) / (2 * m + 1 : ℕ) := by
        apply (div_eq_div_iff (by positivity) (by positivity)).2
        push_cast at hc' ⊢
        nlinarith [hc']
      dsimp [catalanExpEulerEvenQ]
      calc
        ((2 * m).choose (2 * r) : ℚ) *
            (-(4 : ℚ) ^ (2 * r + 1) *
              (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) /
                (2 * r + 1 : ℕ)) =
            -(((2 * m).choose (2 * r) : ℚ) / (2 * r + 1 : ℕ)) *
              ((Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
                (4 : ℚ) ^ (2 * r + 1)) := by ring
        _ = -(((2 * m + 1).choose (2 * r + 1) : ℚ) / (2 * m + 1 : ℕ)) *
              ((Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
                (4 : ℚ) ^ (2 * r + 1)) := by rw [hratio]
        _ = _ := by
          push_cast
          ring
    calc
      ∑ r ∈ Finset.range (m + 1),
          ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r =
          -(1 / (2 * m + 1 : ℚ)) *
            ∑ r ∈ Finset.range (m + 1),
              (((2 * m + 1).choose (2 * r + 1) : ℚ) *
                (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
                  (4 : ℚ) ^ (2 * r + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        exact hterm r
      _ = 0 := by rw [catalanExp_odd_weighted_bernoulli_sum m hmpos, mul_zero]

private lemma catalanExp_even_binom_sum_reflect (m : ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j) : ℚ) * f (m - j) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j) : ℚ) * f j := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using (Finset.mem_range.mp hj)
  rw [show m + 1 - 1 - j = m - j by omega,
    show 2 * (m - j) = 2 * m - 2 * j by omega,
    Nat.choose_symm (by omega : 2 * j ≤ 2 * m),
    show m - (m - j) = j by omega]

private lemma catalanExp_even_E_eq (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) (m : ℕ) :
    (E (2 * m) : ℚ) = catalanExpEulerEvenQ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m = 0
      · subst m
        rw [mul_zero, hE.1, Int.cast_one, catalanExpEulerEvenQ_zero]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hEraw := hE.2 (2 * m) (by omega)
        have hErawQ : (∑ j ∈ Finset.range (m + 1),
            ((2 * m).choose (2 * j) : ℚ) * (E (2 * m - 2 * j) : ℚ)) = 0 := by
          have hcast := congrArg (fun z : ℤ => (z : ℚ)) hEraw
          push_cast at hcast
          simpa only [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using hcast
        have hEoriented : (∑ r ∈ Finset.range (m + 1),
            ((2 * m).choose (2 * r) : ℚ) * (E (2 * r) : ℚ)) = 0 := by
          rw [← catalanExp_even_binom_sum_reflect m (fun r => (E (2 * r) : ℚ))]
          convert hErawQ using 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [show 2 * m - 2 * j = 2 * (m - j) by omega]
        have hQ := catalanExpEulerEvenQ_recurrence m
        rw [ite_eq_right hm] at hQ
        rw [Finset.sum_range_succ] at hEoriented hQ
        have hprefix : (∑ r ∈ Finset.range m,
            ((2 * m).choose (2 * r) : ℚ) * (E (2 * r) : ℚ)) =
            ∑ r ∈ Finset.range m,
              ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [ih r (Finset.mem_range.mp hr)]
        rw [hprefix] at hEoriented
        simp only [Nat.choose_self, Nat.cast_one, one_mul] at hEoriented hQ
        linarith

private lemma catalanExp_bernoulli_quarter_eq (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) (m : ℕ) :
    (Polynomial.bernoulli (2 * m + 1)).eval (1 / 4) =
      -(2 * m + 1 : ℚ) * (E (2 * m) : ℚ) / (4 : ℚ) ^ (2 * m + 1) := by
  have h := catalanExp_even_E_eq E hE m
  rw [catalanExpEulerEvenQ] at h
  have hn : (2 * m + 1 : ℚ) ≠ 0 := by positivity
  have hp : (4 : ℚ) ^ (2 * m + 1) ≠ 0 := by positivity
  field_simp [hn, hp] at h ⊢
  push_cast at h ⊢
  linear_combination h

private lemma catalanExp_bernoulliPolynomialEval_eq_fun (n : ℕ) (x : ℝ) :
    catalanExpBernoulliPolynomialEval n x = bernoulliFun n x := by
  rw [catalanExp_bernoulliPolynomialEval_eq]
  simp only [bernoulliFun, Polynomial.aeval_def, Polynomial.eval_map]

private lemma catalanExp_bernoulliPolynomialEval_rat (n : ℕ) (x : ℚ) :
    catalanExpBernoulliPolynomialEval n (x : ℝ) =
      algebraMap ℚ ℝ ((Polynomial.bernoulli n).eval x) := by
  rw [catalanExp_bernoulliPolynomialEval_eq_fun]
  change (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)).eval
      (algebraMap ℚ ℝ x) =
    algebraMap ℚ ℝ ((Polynomial.bernoulli n).eval x)
  exact Polynomial.eval_map_apply (f := algebraMap ℚ ℝ)
    (p := Polynomial.bernoulli n) x

private lemma catalanExp_bernoulliPolynomialEval_two (n : ℕ) (hn : n ≠ 1) :
    catalanExpBernoulliPolynomialEval n 2 = (bernoulli n : ℝ) + n := by
  rw [show (2 : ℝ) = ((2 : ℚ) : ℝ) by norm_num,
    catalanExp_bernoulliPolynomialEval_rat]
  have hQ : (Polynomial.bernoulli n).eval (2 : ℚ) = bernoulli n + n := by
    calc
      (Polynomial.bernoulli n).eval (2 : ℚ) =
          (Polynomial.bernoulli n).eval (1 + 1) := by norm_num
      _ = (Polynomial.bernoulli n).eval 1 + n * (1 : ℚ) ^ (n - 1) :=
        Polynomial.bernoulli_eval_one_add n 1
      _ = bernoulli n + n := by
        rw [Polynomial.bernoulli_eval_one, bernoulli_eq_bernoulli'_of_ne_one hn]
        norm_num
  simpa only [map_add, map_natCast, eq_ratCast] using congrArg (algebraMap ℚ ℝ) hQ

private lemma catalanExp_first_bernoulli_difference (j : ℕ) :
    catalanExpBernoulliPolynomialEval (j + 2) (1 / 2) -
        catalanExpBernoulliPolynomialEval (j + 2) 2 =
      (((2 : ℝ) ^ (j + 1))⁻¹ - 2) * (bernoulli (j + 2) : ℝ) -
        (j + 1 : ℕ) - 1 := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    catalanExp_bernoulliPolynomialEval_eq_fun,
    bernoulliFun_eval_half, catalanExp_bernoulliPolynomialEval_two (j + 2) (by omega)]
  have hpow : (2 : ℝ) / 2 ^ (j + 2) = ((2 : ℝ) ^ (j + 1))⁻¹ := by
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    field_simp
  rw [hpow]
  push_cast
  ring

private lemma catalanExp_second_odd_bernoulli_difference (r : ℕ) :
    catalanExpBernoulliPolynomialEval (2 * r + 2) (-1 / 4) -
        catalanExpBernoulliPolynomialEval (2 * r + 2) (5 / 4) = 0 := by
  have hQ : (Polynomial.bernoulli (2 * r + 2)).eval (-1 / 4) -
      (Polynomial.bernoulli (2 * r + 2)).eval (5 / 4) = 0 := by
    have h := Polynomial.bernoulli_eval_one_sub (2 * r + 2) (-1 / 4 : ℚ)
    have heven : Even (2 * r + 2) := ⟨r + 1, by omega⟩
    rw [heven.neg_one_pow] at h
    norm_num at h
    linarith
  rw [show (-1 / 4 : ℝ) = ((-1 / 4 : ℚ) : ℝ) by norm_num,
    show (5 / 4 : ℝ) = ((5 / 4 : ℚ) : ℝ) by norm_num,
    catalanExp_bernoulliPolynomialEval_rat,
    catalanExp_bernoulliPolynomialEval_rat]
  simpa only [map_sub, map_zero] using congrArg (algebraMap ℚ ℝ) hQ

private lemma catalanExp_second_even_coefficient (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0)
    (r : ℕ) (hr : 0 < r) :
    (-1 : ℝ) ^ (2 * r + 1) *
        (catalanExpBernoulliPolynomialEval (2 * r + 1) (-1 / 4) -
          catalanExpBernoulliPolynomialEval (2 * r + 1) (5 / 4)) /
          ((2 * r : ℕ) * (2 * r + 1 : ℕ)) =
      ((2 : ℝ) ^ (4 * r + 2))⁻¹ * (4 - (E (2 * r) : ℝ)) / r := by
  let B : ℚ := (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4)
  have hneg : (Polynomial.bernoulli (2 * r + 1)).eval (-1 / 4) =
      -(B + (2 * r + 1 : ℚ) * (1 / 4) ^ (2 * r)) := by
    have h := Polynomial.bernoulli_eval_neg (2 * r + 1) (1 / 4 : ℚ)
    have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
    rw [hodd.neg_one_pow, show 2 * r + 1 - 1 = 2 * r by omega] at h
    push_cast at h ⊢
    norm_num at h ⊢
    simpa only [B, neg_mul, one_mul] using h
  have hplus : (Polynomial.bernoulli (2 * r + 1)).eval (5 / 4) =
      B + (2 * r + 1 : ℚ) * (1 / 4) ^ (2 * r) := by
    have h := Polynomial.bernoulli_eval_one_add (2 * r + 1) (1 / 4 : ℚ)
    norm_num at h ⊢
    simpa only [B, show 2 * r + 1 - 1 = 2 * r by omega] using h
  have hB := catalanExp_bernoulli_quarter_eq E hE r
  change B = -(2 * r + 1 : ℚ) * (E (2 * r) : ℚ) /
    (4 : ℚ) ^ (2 * r + 1) at hB
  have htwo : (2 : ℚ) ^ (4 * r + 2) = (4 : ℚ) ^ (2 * r + 1) := by
    calc
      (2 : ℚ) ^ (4 * r + 2) = 2 ^ (2 * (2 * r + 1)) := by
        congr 1
        omega
      _ = (2 ^ 2) ^ (2 * r + 1) := by rw [pow_mul]
      _ = (4 : ℚ) ^ (2 * r + 1) := by norm_num
  have hcoefQ : (-1 : ℚ) ^ (2 * r + 1) *
      ((Polynomial.bernoulli (2 * r + 1)).eval (-1 / 4) -
        (Polynomial.bernoulli (2 * r + 1)).eval (5 / 4)) /
        ((2 * r : ℕ) * (2 * r + 1 : ℕ)) =
      ((2 : ℚ) ^ (4 * r + 2))⁻¹ * (4 - (E (2 * r) : ℚ)) / r := by
    rw [hneg, hplus, hB, htwo]
    have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
    rw [hodd.neg_one_pow, show 2 * r + 1 = 2 * r + 1 by rfl, pow_succ,
      div_pow]
    norm_num
    field_simp
    ring
  rw [show (-1 / 4 : ℝ) = ((-1 / 4 : ℚ) : ℝ) by norm_num,
    show (5 / 4 : ℝ) = ((5 / 4 : ℚ) : ℝ) by norm_num,
    catalanExp_bernoulliPolynomialEval_rat,
    catalanExp_bernoulliPolynomialEval_rat]
  have hcast := congrArg (algebraMap ℚ ℝ) hcoefQ
  simp only [map_mul, map_sub, map_div₀, map_pow, map_inv₀, map_natCast,
    map_intCast, eq_ratCast] at hcast
  push_cast at hcast ⊢
  simpa only [eq_ratCast] using hcast

private lemma catalanExp_centralBinom_cast (n : ℕ) :
    (n.centralBinom : ℝ) = ((2 * n).factorial : ℝ) /
      ((n.factorial : ℝ) * (n.factorial : ℝ)) := by
  have hle : n ≤ 2 * n := by omega
  have hchoose : (2 * n).choose n * (n.factorial * ((2 * n) - n).factorial) =
      (2 * n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) hle
    rwa [mul_assoc] at h
  rw [show 2 * n - n = n by omega] at hchoose
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [eq_div_iff (mul_ne_zero hf.ne' hf.ne')]
  exact_mod_cast hchoose

private lemma catalanExp_catalan_cast (n : ℕ) :
    (catalan n : ℝ) = (n.centralBinom : ℝ) / ((n : ℝ) + 1) := by
  have h := succ_mul_catalan_eq_centralBinom n
  rw [eq_div_iff (by positivity : (n : ℝ) + 1 ≠ 0), mul_comm]
  exact_mod_cast h

private lemma catalanExp_stirling_model_identity (n : ℕ) (hn : 1 ≤ n) :
    ((Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
          ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) /
        ((Real.sqrt (2 * (n : ℝ) * Real.pi) *
            ((n : ℝ) / Real.exp 1) ^ n) *
          (Real.sqrt (2 * (n : ℝ) * Real.pi) *
            ((n : ℝ) / Real.exp 1) ^ n)) /
        ((n : ℝ) + 1)) *
      ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)) =
        (n : ℝ) / ((n : ℝ) + 1) := by
  have hn0 : 0 < n := by omega
  have ha : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnn : (0 : ℝ) ≤ (n : ℝ) * Real.pi :=
    mul_nonneg ha.le Real.pi_pos.le
  have hsq2 : Real.sqrt (2 * (2 * n : ℝ) * Real.pi) =
      2 * Real.sqrt ((n : ℝ) * Real.pi) := by
    have hsqnn : (0 : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * Real.pi) := by positivity
    have heq : (2 : ℝ) * (2 * n : ℝ) * Real.pi =
        (2 * Real.sqrt ((n : ℝ) * Real.pi)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hnn]
      ring
    rw [heq, Real.sqrt_sq hsqnn]
  have hsq1sq : (Real.sqrt (2 * (n : ℝ) * Real.pi)) ^ 2 =
      2 * (n : ℝ) * Real.pi := Real.sq_sqrt (by positivity)
  have hS1S1 :
      (Real.sqrt (2 * (n : ℝ) * Real.pi) * ((n : ℝ) / Real.exp 1) ^ n) *
        (Real.sqrt (2 * (n : ℝ) * Real.pi) * ((n : ℝ) / Real.exp 1) ^ n) =
      (2 * (n : ℝ) * Real.pi) *
        (((n : ℝ) / Real.exp 1) ^ n * ((n : ℝ) / Real.exp 1) ^ n) := by
    calc
      _ = (Real.sqrt (2 * (n : ℝ) * Real.pi)) ^ 2 *
          (((n : ℝ) / Real.exp 1) ^ n * ((n : ℝ) / Real.exp 1) ^ n) := by ring
      _ = _ := by rw [hsq1sq]
  have hPu : ((2 * n : ℝ) / Real.exp 1) ^ n =
      (2 : ℝ) ^ n * ((n : ℝ) / Real.exp 1) ^ n := by
    rw [div_pow, mul_pow, mul_div_assoc, ← div_pow]
  have h4 : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      show 2 * n = n + n by omega, pow_add]
  have hs3 : Real.sqrt (Real.pi * (n : ℝ)) =
      Real.sqrt ((n : ℝ) * Real.pi) := by rw [mul_comm]
  have hdouble : ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) =
      ((2 * n : ℝ) / Real.exp 1) ^ n *
        ((2 * n : ℝ) / Real.exp 1) ^ n := by
    rw [show 2 * n = n + n by omega, pow_add]
  rw [hsq2, hdouble, hPu, hS1S1, h4, hs3]
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2aπ : (2 : ℝ) * n * Real.pi ≠ 0 := by positivity
  have hae : (n : ℝ) / Real.exp 1 ≠ 0 := (div_pos ha he).ne'
  have hp : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := pow_ne_zero _ hae
  have ha1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hQ : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hs2 : (Real.sqrt ((n : ℝ) * Real.pi)) ^ 2 =
      (n : ℝ) * Real.pi := Real.sq_sqrt hnn
  field_simp [h2aπ, hae, hp, ha1, hQ, he.ne']
  ring_nf
  rw [hs2]

private theorem catalanExp_first_log_tendsto_zero :
    Filter.Tendsto (fun n : ℕ =>
      Real.log ((catalan n : ℝ) * ((n : ℝ) * Real.sqrt (Real.pi * n)) /
        (4 : ℝ) ^ n)) Filter.atTop (nhds 0) := by
  have h2top : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop_of_monotone
    · intro a b hab
      change 2 * a ≤ 2 * b
      omega
    · intro b
      exact ⟨b, by omega⟩
  have hFact := Stirling.factorial_isEquivalent_stirling
  have hFact2 := hFact.comp_tendsto h2top
  have eCB : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => ((2 * n).factorial : ℝ) /
        ((n.factorial : ℝ) * (n.factorial : ℝ)))
      (fun n : ℕ => (Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
          ((2 * n : ℝ) / Real.exp 1) ^ (2 * n)) /
        ((Real.sqrt (2 * (n : ℝ) * Real.pi) * ((n : ℝ) / Real.exp 1) ^ n) *
          (Real.sqrt (2 * (n : ℝ) * Real.pi) * ((n : ℝ) / Real.exp 1) ^ n))) :=
    by
      convert hFact2.div (hFact.mul hFact) using 1 <;>
        ext n <;> simp [Function.comp_apply]
  have rNp1 : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (n : ℝ) + 1) (fun n : ℕ => (n : ℝ) + 1) :=
    Asymptotics.IsEquivalent.refl
  have rR : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)
      (fun n : ℕ => (n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n) :=
    Asymptotics.IsEquivalent.refl
  have eST : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ =>
        ((Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
              ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) /
            ((Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n) *
              (Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      (fun n : ℕ =>
        ((((2 * n).factorial : ℝ) /
              ((n.factorial : ℝ) * (n.factorial : ℝ)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n))) :=
    ((eCB.div rNp1).mul rR).symm
  have hmodel : Filter.EventuallyEq Filter.atTop
      (fun n : ℕ =>
        ((Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
              ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) /
            ((Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n) *
              (Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact catalanExp_stirling_model_identity n hn
  have hzero : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : Filter.Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 1) := by
    have h : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hzero
    rw [sub_zero] at h
    refine h.congr fun n => ?_
    field_simp
    ring
  have hStirlingModel : Filter.Tendsto
      (fun n : ℕ =>
        ((Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
              ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) /
            ((Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n) *
              (Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      Filter.atTop (nhds 1) := Filter.Tendsto.congr' hmodel.symm hratio
  have hfactorialModel : Filter.Tendsto
      (fun n : ℕ =>
        ((((2 * n).factorial : ℝ) /
              ((n.factorial : ℝ) * (n.factorial : ℝ)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      Filter.atTop (nhds 1) := eST.tendsto_nhds hStirlingModel
  have hCatalanModel : Filter.EventuallyEq Filter.atTop
      (fun n : ℕ =>
        ((((2 * n).factorial : ℝ) /
              ((n.factorial : ℝ) * (n.factorial : ℝ)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      (fun n : ℕ =>
        (catalan n : ℝ) * ((n : ℝ) * Real.sqrt (Real.pi * n)) /
          (4 : ℝ) ^ n) := by
    filter_upwards with n
    rw [← catalanExp_centralBinom_cast n, ← catalanExp_catalan_cast n]
    ring
  have htarget : Filter.Tendsto (fun n : ℕ =>
      (catalan n : ℝ) * ((n : ℝ) * Real.sqrt (Real.pi * n)) /
        (4 : ℝ) ^ n) Filter.atTop (nhds 1) :=
    Filter.Tendsto.congr' hCatalanModel hfactorialModel
  simpa using htarget.log (by norm_num : (1 : ℝ) ≠ 0)

private lemma catalanExp_catalan_pos (n : ℕ) : (0 : ℝ) < catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hpos : 0 < (n + 1) * catalan n := by
    rw [h]
    exact Nat.centralBinom_pos n
  have hne : catalan n ≠ 0 := by
    intro hzero
    simp only [hzero, mul_zero, lt_self_iff_false] at hpos
  exact_mod_cast Nat.pos_of_ne_zero hne

private lemma catalanExp_catalan_succ_ratio (n : ℕ) :
    (catalan (n + 1) : ℝ) / catalan n =
      2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 2) := by
  have hcentral := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1),
    ← succ_mul_catalan_eq_centralBinom n] at hcentral
  have hcat : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 1)
    calc
      (n + 1) * ((n + 2) * catalan (n + 1)) =
          (n + 1) * ((n + 1 + 1) * catalan (n + 1)) := by
        rw [show n + 2 = n + 1 + 1 by omega]
      _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := hcentral
      _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by ring
  apply (div_eq_div_iff (catalanExp_catalan_pos n).ne' (by positivity)).2
  have hcat' : catalan (n + 1) * (n + 2) =
      2 * (2 * n + 1) * catalan n := by
    simpa [mul_comm] using hcat
  exact_mod_cast hcat'

private lemma catalanExp_sum_bernoulli_aeval (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose k : ℝ) * Polynomial.aeval x (Polynomial.bernoulli k)) =
      (n + 1 : ℝ) * x ^ n := by
  have h := congrArg (Polynomial.aeval x) (Polynomial.sum_bernoulli n)
  simp only [map_sum, map_smul, Polynomial.aeval_monomial] at h
  simpa only [Algebra.smul_def, map_natCast, map_add, map_one] using h

private lemma catalanExp_bernoulli_coeff (r : ℕ) (hr : 2 ≤ r) (α β : ℝ) :
    (∑ k ∈ Finset.range (r - 1),
        ((r - 1).choose k : ℝ) *
          (Polynomial.aeval α (Polynomial.bernoulli (k + 2)) -
            Polynomial.aeval β (Polynomial.bernoulli (k + 2))) /
          ((k + 1 : ℕ) * (k + 2 : ℕ))) =
      (α ^ r - β ^ r + β - α) / r := by
  let f : ℕ → ℝ := fun k => ((r + 1).choose k : ℝ) *
    (Polynomial.aeval α (Polynomial.bernoulli k) -
      Polynomial.aeval β (Polynomial.bernoulli k))
  have hfull : (∑ k ∈ Finset.range (r + 1), f k) =
      (r + 1 : ℝ) * (α ^ r - β ^ r) := by
    dsimp [f]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,
      catalanExp_sum_bernoulli_aeval, catalanExp_sum_bernoulli_aeval]
  have hsmall : (∑ k ∈ Finset.range 2, f k) = (r + 1 : ℝ) * (α - β) := by
    simp [f, Finset.sum_range_succ, Polynomial.aeval_def]
  have htail : (∑ k ∈ Finset.Ico 2 (r + 1), f k) =
      (r + 1 : ℝ) * (α ^ r - β ^ r + β - α) := by
    rw [Finset.sum_Ico_eq_sub f (by omega), hfull, hsmall]
    ring
  rw [Finset.sum_Ico_eq_sum_range f 2 (r + 1)] at htail
  rw [show r + 1 - 2 = r - 1 by omega] at htail
  have hshift : (∑ k ∈ Finset.range (r - 1), f (k + 2)) =
      (r + 1 : ℝ) * (α ^ r - β ^ r + β - α) := by
    simpa [add_comm] using htail
  have hchoose (k : ℕ) :
      ((r - 1).choose k : ℝ) / ((k + 1 : ℕ) * (k + 2 : ℕ)) =
        ((r + 1).choose (k + 2) : ℝ) / ((r : ℕ) * (r + 1 : ℕ)) := by
    have h₁ := Nat.add_one_mul_choose_eq (r - 1) k
    have h₂ := Nat.add_one_mul_choose_eq r (k + 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at h₁
    rw [show k + 1 + 1 = k + 2 by omega] at h₂
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    norm_cast
    calc
      (r - 1).choose k * (r * (r + 1))
          = (r + 1) * (r * (r - 1).choose k) := by ring
      _ = (r + 1) * (r.choose (k + 1) * (k + 1)) := by rw [h₁]
      _ = ((r + 1) * r.choose (k + 1)) * (k + 1) := by ring
      _ = ((r + 1).choose (k + 2) * (k + 2)) * (k + 1) := by rw [h₂]
      _ = (r + 1).choose (k + 2) * ((k + 1) * (k + 2)) := by ring
  calc
    _ = (∑ k ∈ Finset.range (r - 1), f (k + 2)) /
        ((r : ℝ) * (r + 1 : ℝ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = (((r - 1).choose k : ℝ) /
            ((k + 1 : ℕ) * (k + 2 : ℕ))) *
              (Polynomial.aeval α (Polynomial.bernoulli (k + 2)) -
                Polynomial.aeval β (Polynomial.bernoulli (k + 2))) := by ring
        _ = (((r + 1).choose (k + 2) : ℝ) /
            ((r : ℕ) * (r + 1 : ℕ))) *
              (Polynomial.aeval α (Polynomial.bernoulli (k + 2)) -
                Polynomial.aeval β (Polynomial.bernoulli (k + 2))) := by rw [hchoose]
        _ = f (k + 2) / ((r : ℝ) * (r + 1 : ℝ)) := by
          dsimp [f]
          field_simp
          push_cast
          ring
    _ = _ := by
      rw [hshift]
      field_simp

private noncomputable def catalanExpLogTaylor (a : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N,
    (-1 : ℝ) ^ i * a ^ (i + 1) / (i + 1 : ℕ) * y ^ (i + 1)

private lemma catalanExp_log_sub_taylor_isBigO (a : ℝ) (N : ℕ) :
    (fun y : ℝ => Real.log (1 + a * y) - catalanExpLogTaylor a N y) =O[nhds 0]
      fun y : ℝ => y ^ (N + 1) := by
  apply Asymptotics.IsBigO.of_bound (2 * |a| ^ (N + 1))
  have hlim : Filter.Tendsto (fun y : ℝ => a * y) (nhds 0) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (Filter.tendsto_id :
      Filter.Tendsto (fun y : ℝ => y) (nhds 0) (nhds 0)))
  have hevent : ∀ᶠ y : ℝ in nhds 0, |a * y| < 1 / 2 := by
    have h := hlim.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
    simpa [Metric.mem_ball, Real.dist_eq] using h
  filter_upwards [hevent] with y hy
  have hlog := Real.abs_log_sub_add_sum_range_le
    (x := -(a * y)) (by simpa only [abs_neg] using hy.trans (by norm_num)) N
  have hsum : (∑ i ∈ Finset.range N, (-(a * y)) ^ (i + 1) / (i + 1 : ℕ)) =
      -catalanExpLogTaylor a N y := by
    rw [catalanExpLogTaylor, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [neg_pow, mul_pow, pow_succ]
    ring
  simp only [Nat.cast_add, Nat.cast_one] at hsum
  rw [hsum, show 1 - -(a * y) = 1 + a * y by ring] at hlog
  simp only [abs_neg] at hlog
  calc
    ‖Real.log (1 + a * y) - catalanExpLogTaylor a N y‖
        = |-catalanExpLogTaylor a N y + Real.log (1 + a * y)| := by
          rw [Real.norm_eq_abs]
          congr 1
          ring
    _ ≤ |a * y| ^ (N + 1) / (1 - |a * y|) := hlog
    _ ≤ 2 * |a * y| ^ (N + 1) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [pow_nonneg (abs_nonneg (a * y)) (N + 1)]
    _ = (2 * |a| ^ (N + 1)) * ‖y ^ (N + 1)‖ := by
      rw [abs_mul, mul_pow, Real.norm_eq_abs, abs_pow]
      ring

private lemma catalanExp_choose_neg_nat (k l : ℕ) (hk : 1 ≤ k) :
    Ring.choose (-(k : ℝ)) l =
      (-1 : ℝ) ^ l * ((k + l - 1).choose l : ℝ) := by
  rw [Ring.choose_neg]
  have hcast : (k : ℝ) + l - 1 = ((k + l - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k + l)]
    push_cast
    rfl
  rw [hcast, Ring.choose_natCast]
  change Int.negOnePow (l : ℤ) • (((k + l - 1).choose l : ℕ) : ℝ) =
    (-1 : ℝ) ^ l * ((k + l - 1).choose l : ℝ)
  rw [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]

private lemma catalanExp_binomial_partialSum (k N : ℕ) (hk : 1 ≤ k) (y : ℝ) :
    (binomialSeries ℝ (-(k : ℝ))).partialSum N y =
      ∑ l ∈ Finset.range N,
        (-1 : ℝ) ^ l * ((k + l - 1).choose l : ℝ) * y ^ l := by
  simp only [FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul,
    binomialSeries, FormalMultilinearSeries.coeff_ofScalars]
  apply Finset.sum_congr rfl
  intro l hl
  rw [catalanExp_choose_neg_nat k l hk]
  ring

private noncomputable def catalanExpInvTaylor (k N : ℕ) (y : ℝ) : ℝ :=
  ∑ l ∈ Finset.range N,
    (-1 : ℝ) ^ l * ((k + l - 1).choose l : ℝ) * y ^ l

private lemma catalanExp_rpow_sub_invTaylor_isBigO (k N : ℕ) (hk : 1 ≤ k) :
    (fun y : ℝ => (1 + y) ^ (-(k : ℝ)) - catalanExpInvTaylor k N y) =O[nhds 0]
      fun y : ℝ => y ^ N := by
  have h := (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := -(k : ℝ))).isBigO_sub_partialSum_pow N
  rw [show (binomialSeries ℝ (-(k : ℝ))).partialSum N =
      catalanExpInvTaylor k N by
        funext y
        exact catalanExp_binomial_partialSum k N hk y] at h
  apply Asymptotics.IsBigO.of_norm_right
  simpa only [zero_add, Real.norm_eq_abs, abs_pow] using h

private noncomputable def catalanExpBernoulliCoeff (α β : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + 1) *
    (Polynomial.aeval α (Polynomial.bernoulli (k + 1)) -
      Polynomial.aeval β (Polynomial.bernoulli (k + 1))) /
    ((k : ℝ) * (k + 1 : ℕ))

private noncomputable def catalanExpDiffCoeff (α β : ℝ) (r : ℕ) : ℝ :=
  (-1 : ℝ) ^ (r + 1) * (α ^ r - β ^ r + β - α) / r

private noncomputable def catalanExpShiftInner (M j : ℕ) (y : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (M - j),
    (-1 : ℝ) ^ (q + 1) * ((j + q + 1).choose (q + 1) : ℝ) * y ^ (j + q + 2)

private noncomputable def catalanExpShiftTaylor (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M,
    catalanExpBernoulliCoeff α β (j + 1) * catalanExpShiftInner M j y

private noncomputable def catalanExpDiffTaylor (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanExpDiffCoeff α β (j + 2) * y ^ (j + 2)

private lemma catalanExp_logTaylor_combination (α β : ℝ) (M : ℕ) (y : ℝ) :
    catalanExpLogTaylor α (M + 1) y - catalanExpLogTaylor β (M + 1) y +
        (β - α) * catalanExpLogTaylor 1 (M + 1) y =
      catalanExpDiffTaylor α β M y := by
  induction M with
  | zero =>
      simp [catalanExpLogTaylor, catalanExpDiffTaylor]
      ring
  | succ M ih =>
      have hTaylor (a : ℝ) :
          catalanExpLogTaylor a (M + 2) y =
            catalanExpLogTaylor a (M + 1) y +
              (-1 : ℝ) ^ (M + 1) * a ^ (M + 2) / (M + 2 : ℕ) * y ^ (M + 2) := by
        unfold catalanExpLogTaylor
        rw [Finset.sum_range_succ]
      have hDiff : catalanExpDiffTaylor α β (M + 1) y =
          catalanExpDiffTaylor α β M y +
            catalanExpDiffCoeff α β (M + 2) * y ^ (M + 2) := by
        unfold catalanExpDiffTaylor
        rw [Finset.sum_range_succ]
      have hnew :
          (-1 : ℝ) ^ (M + 1) * α ^ (M + 2) / (M + 2 : ℕ) * y ^ (M + 2) -
              (-1 : ℝ) ^ (M + 1) * β ^ (M + 2) / (M + 2 : ℕ) * y ^ (M + 2) +
            (β - α) *
              ((-1 : ℝ) ^ (M + 1) * 1 ^ (M + 2) / (M + 2 : ℕ) * y ^ (M + 2)) =
            catalanExpDiffCoeff α β (M + 2) * y ^ (M + 2) := by
        simp only [one_pow, catalanExpDiffCoeff]
        rw [show (-1 : ℝ) ^ (M + 2 + 1) = (-1 : ℝ) ^ (M + 1) by
          rw [show M + 2 + 1 = (M + 1) + 2 by omega, pow_add]
          norm_num]
        field_simp
        ring
      change
        catalanExpLogTaylor α (M + 2) y - catalanExpLogTaylor β (M + 2) y +
            (β - α) * catalanExpLogTaylor 1 (M + 2) y =
          catalanExpDiffTaylor α β (M + 1) y
      rw [hTaylor α, hTaylor β, hTaylor 1, hDiff]
      linear_combination ih + hnew

private lemma catalanExp_shiftInner_succ (M j : ℕ) (hj : j < M) (y : ℝ) :
    catalanExpShiftInner (M + 1) j y = catalanExpShiftInner M j y +
      (-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) * y ^ (M + 2) := by
  unfold catalanExpShiftInner
  have hsub : M + 1 - j = (M - j) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  rw [show j + (M - j) + 1 = M + 1 by omega,
    show j + (M - j) + 2 = M + 2 by omega]

private lemma catalanExp_shiftTaylor_succ_raw (α β : ℝ) (M : ℕ) (y : ℝ) :
    catalanExpShiftTaylor α β (M + 1) y = catalanExpShiftTaylor α β M y +
      ∑ j ∈ Finset.range (M + 1),
        catalanExpBernoulliCoeff α β (j + 1) *
          ((-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) *
            y ^ (M + 2)) := by
  have hlast : catalanExpShiftInner (M + 1) M y =
      (-1 : ℝ) ^ (M - M + 1) * ((M + 1).choose (M - M + 1) : ℝ) *
        y ^ (M + 2) := by
    simp [catalanExpShiftInner]
  have hsum :
      (∑ j ∈ Finset.range M,
          catalanExpBernoulliCoeff α β (j + 1) * catalanExpShiftInner (M + 1) j y) =
        (∑ j ∈ Finset.range M,
            catalanExpBernoulliCoeff α β (j + 1) * catalanExpShiftInner M j y) +
          ∑ j ∈ Finset.range M,
            catalanExpBernoulliCoeff α β (j + 1) *
              ((-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) *
                y ^ (M + 2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [catalanExp_shiftInner_succ M j hj]
    ring
  unfold catalanExpShiftTaylor
  rw [Finset.sum_range_succ, Finset.sum_range_succ, hlast, hsum]
  ring

private lemma catalanExp_shift_diagonal (α β : ℝ) (M : ℕ) (y : ℝ) :
    (∑ j ∈ Finset.range (M + 1),
        catalanExpBernoulliCoeff α β (j + 1) *
          ((-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) *
            y ^ (M + 2))) =
      catalanExpDiffCoeff α β (M + 2) * y ^ (M + 2) := by
  have hterms :
      (∑ j ∈ Finset.range (M + 1),
          catalanExpBernoulliCoeff α β (j + 1) *
            ((-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) *
              y ^ (M + 2))) =
        ∑ j ∈ Finset.range (M + 1),
          (-1 : ℝ) ^ (M + 3) *
            (((M + 1).choose j : ℝ) *
              (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
                Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
              ((j + 1 : ℕ) * (j + 2 : ℕ))) * y ^ (M + 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hjle : j ≤ M + 1 := Nat.le_of_lt hj
    have hsub : M - j + 1 = M + 1 - j := by omega
    rw [hsub, Nat.choose_symm hjle]
    unfold catalanExpBernoulliCoeff
    have hsign : (-1 : ℝ) ^ (j + 2) * (-1 : ℝ) ^ (M + 1 - j) =
        (-1 : ℝ) ^ (M + 3) := by
      rw [← pow_add, show j + 2 + (M + 1 - j) = M + 3 by omega]
    rw [show j + 1 + 1 = j + 2 by omega]
    push_cast
    calc
      _ = ((-1 : ℝ) ^ (j + 2) * (-1 : ℝ) ^ (M + 1 - j)) *
          (((M + 1).choose j : ℝ) *
            (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
              Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
            ((j + 1 : ℝ) * (j + 2 : ℝ))) * y ^ (M + 2) := by ring
      _ = _ := by rw [hsign]
  rw [hterms]
  have hcoeff := catalanExp_bernoulli_coeff (M + 2) (by omega) α β
  have hcoeff' :
      (∑ j ∈ Finset.range (M + 1),
          ((M + 1).choose j : ℝ) *
            (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
              Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
            ((j + 1 : ℕ) * (j + 2 : ℕ))) =
        (α ^ (M + 2) - β ^ (M + 2) + β - α) / (M + 2 : ℕ) := by
    simpa only [show M + 2 - 1 = M + 1 by omega] using hcoeff
  calc
    (∑ j ∈ Finset.range (M + 1),
        (-1 : ℝ) ^ (M + 3) *
          (((M + 1).choose j : ℝ) *
            (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
              Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
            ((j + 1 : ℕ) * (j + 2 : ℕ))) * y ^ (M + 2)) =
      ((-1 : ℝ) ^ (M + 3) *
        ∑ j ∈ Finset.range (M + 1),
          ((M + 1).choose j : ℝ) *
            (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
              Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
            ((j + 1 : ℕ) * (j + 2 : ℕ))) * y ^ (M + 2) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
      rw [hcoeff']
      unfold catalanExpDiffCoeff
      ring

private lemma catalanExp_shiftTaylor_eq_diffTaylor (α β : ℝ) (M : ℕ) (y : ℝ) :
    catalanExpShiftTaylor α β M y = catalanExpDiffTaylor α β M y := by
  induction M with
  | zero => simp [catalanExpShiftTaylor, catalanExpDiffTaylor]
  | succ M ih =>
      rw [catalanExp_shiftTaylor_succ_raw, catalanExp_shift_diagonal, ih]
      unfold catalanExpDiffTaylor
      rw [Finset.sum_range_succ]

private lemma catalanExp_mul_invTaylor_sub_one (M j : ℕ) (hj : j < M) (y : ℝ) :
    y ^ (j + 1) * (catalanExpInvTaylor (j + 1) (M + 1 - j) y - 1) =
      catalanExpShiftInner M j y := by
  have hsub : M + 1 - j = (M - j) + 1 := by omega
  unfold catalanExpInvTaylor catalanExpShiftInner
  rw [hsub, Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [add_sub_cancel_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [show j + 1 + (q + 1) - 1 = j + q + 1 by omega]
  calc
    _ = (-1 : ℝ) ^ (q + 1) * ((j + q + 1).choose (q + 1) : ℝ) *
        (y ^ (j + 1) * y ^ (q + 1)) := by ring
    _ = _ := by
      rw [← pow_add, show j + 1 + (q + 1) = j + q + 2 by omega]

private noncomputable def catalanExpBernoulliSum (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanExpBernoulliCoeff α β (j + 1) * y ^ (j + 1)

private noncomputable def catalanExpShiftRemainder (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanExpBernoulliCoeff α β (j + 1) *
    (y ^ (j + 1) *
      ((1 + y) ^ (-((j + 1 : ℕ) : ℝ)) -
        catalanExpInvTaylor (j + 1) (M + 1 - j) y))

private lemma catalanExp_shiftRemainder_isBigO (α β : ℝ) (M : ℕ) :
    catalanExpShiftRemainder α β M =O[nhds 0] fun y : ℝ => y ^ (M + 2) := by
  unfold catalanExpShiftRemainder
  have hsum : (∑ j ∈ Finset.range M, fun y : ℝ =>
      catalanExpBernoulliCoeff α β (j + 1) *
        (y ^ (j + 1) *
          ((1 + y) ^ (-((j + 1 : ℕ) : ℝ)) -
            catalanExpInvTaylor (j + 1) (M + 1 - j) y))) =O[nhds 0]
      fun y : ℝ => y ^ (M + 2) := by
    apply Asymptotics.IsBigO.sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hmul := (Asymptotics.isBigO_refl (fun y : ℝ => y ^ (j + 1)) (nhds 0)).mul
      (catalanExp_rpow_sub_invTaylor_isBigO (j + 1) (M + 1 - j) (by omega))
    have hpow : (fun y : ℝ => y ^ (j + 1) * y ^ (M + 1 - j)) =
        fun y : ℝ => y ^ (M + 2) := by
      funext y
      rw [← pow_add, show j + 1 + (M + 1 - j) = M + 2 by omega]
    rw [hpow] at hmul
    exact hmul.const_mul_left (catalanExpBernoulliCoeff α β (j + 1))
  apply hsum.congr_left
  intro y
  exact Finset.sum_apply y (Finset.range M) _

private lemma catalanExp_shift_sub_eq_remainder (α β : ℝ) (M : ℕ) (y : ℝ)
    (hy : 0 < 1 + y) :
    catalanExpBernoulliSum α β M (y / (1 + y)) -
        catalanExpBernoulliSum α β M y - catalanExpShiftTaylor α β M y =
      catalanExpShiftRemainder α β M y := by
  unfold catalanExpBernoulliSum catalanExpShiftTaylor catalanExpShiftRemainder
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hratio : (y / (1 + y)) ^ (j + 1) =
      y ^ (j + 1) * (1 + y) ^ (-((j + 1 : ℕ) : ℝ)) := by
    rw [div_pow, Real.rpow_neg (le_of_lt hy), Real.rpow_natCast]
    rfl
  rw [hratio, ← catalanExp_mul_invTaylor_sub_one M j hj y]
  ring

private noncomputable def catalanExpLogStep (α β : ℝ) (y : ℝ) : ℝ :=
  Real.log (1 + α * y) - Real.log (1 + β * y) +
    (β - α) * Real.log (1 + y)

private noncomputable def catalanExpLogRemainder (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  (Real.log (1 + α * y) - catalanExpLogTaylor α (M + 1) y) -
    (Real.log (1 + β * y) - catalanExpLogTaylor β (M + 1) y) +
    (β - α) * (Real.log (1 + y) - catalanExpLogTaylor 1 (M + 1) y)

private lemma catalanExp_logRemainder_isBigO (α β : ℝ) (M : ℕ) :
    catalanExpLogRemainder α β M =O[nhds 0] fun y : ℝ => y ^ (M + 2) := by
  unfold catalanExpLogRemainder
  have h1 : (fun y : ℝ => Real.log (1 + y) - catalanExpLogTaylor 1 (M + 1) y) =O[nhds 0]
      fun y : ℝ => y ^ (M + 2) := by
    apply (catalanExp_log_sub_taylor_isBigO 1 (M + 1)).congr_left
    intro y
    congr 2
    ring
  exact ((catalanExp_log_sub_taylor_isBigO α (M + 1)).sub
    (catalanExp_log_sub_taylor_isBigO β (M + 1))).add
      (h1.const_mul_left (β - α))

private noncomputable def catalanExpLocalResidual (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  catalanExpLogStep α β y -
    (catalanExpBernoulliSum α β M (y / (1 + y)) -
      catalanExpBernoulliSum α β M y)

private lemma catalanExp_localResidual_isBigO (α β : ℝ) (M : ℕ) :
    catalanExpLocalResidual α β M =O[nhds 0] fun y : ℝ => y ^ (M + 2) := by
  have hO := (catalanExp_logRemainder_isBigO α β M).sub
    (catalanExp_shiftRemainder_isBigO α β M)
  apply hO.congr' _ (Filter.EventuallyEq.rfl)
  have hball : ∀ᶠ y : ℝ in nhds 0, |y| < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with y hy
    simpa [Metric.mem_ball, Real.dist_eq] using hy
  filter_upwards [hball] with y hy
  have hy' : 0 < 1 + y := by linarith [neg_lt_of_abs_lt hy]
  unfold catalanExpLocalResidual catalanExpLogStep
  rw [show catalanExpBernoulliSum α β M (y / (1 + y)) -
          catalanExpBernoulliSum α β M y =
        catalanExpShiftTaylor α β M y + catalanExpShiftRemainder α β M y by
      linarith [catalanExp_shift_sub_eq_remainder α β M y hy']]
  rw [catalanExp_shiftTaylor_eq_diffTaylor α β M y,
    ← catalanExp_logTaylor_combination α β M y]
  unfold catalanExpLogRemainder
  ring

private lemma catalanExp_sum_range_inv_sq (n N : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range N, (((k + n : ℕ) : ℝ) ^ 2)⁻¹) =
      ∑ i ∈ Finset.Ioc (n - 1) ((n - 1) + N), (((i : ℕ) : ℝ) ^ 2)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show n - 1 + (N + 1) = (n - 1 + N) + 1 by omega,
        Finset.sum_Ioc_succ_top (by omega : n - 1 ≤ n - 1 + N)]
      rw [show N + n = n - 1 + N + 1 by omega]

private lemma catalanExp_sum_range_inv_sq_le (n N : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range N, (((k + n : ℕ) : ℝ) ^ 2)⁻¹) ≤ 2 / (n : ℝ) := by
  calc
    (∑ k ∈ Finset.range N, (((k + n : ℕ) : ℝ) ^ 2)⁻¹) =
        ∑ i ∈ Finset.Ioc (n - 1) ((n - 1) + N), (((i : ℕ) : ℝ) ^ 2)⁻¹ :=
      catalanExp_sum_range_inv_sq n N (by omega)
    _ ≤ ((n - 1 : ℕ) : ℝ)⁻¹ - (((n - 1 + N : ℕ) : ℝ))⁻¹ :=
      sum_Ioc_inv_sq_le_sub (by omega) (by omega)
    _ ≤ ((n - 1 : ℕ) : ℝ)⁻¹ :=
      sub_le_self _ (inv_nonneg.mpr (by positivity))
    _ ≤ 2 / (n : ℝ) := by
      rw [← one_div]
      have hn1pos : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      apply (div_le_div_iff₀ hn1pos hnpos).2
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith

private lemma catalanExp_tendsto_nat_pow_mul_of_diff_isBigO (e : ℕ → ℝ) (M : ℕ)
    (he : Filter.Tendsto e Filter.atTop (nhds 0))
    (hd : (fun n : ℕ => e (n + 1) - e n) =O[Filter.atTop]
      fun n : ℕ => (((n : ℝ) ^ (M + 2))⁻¹)) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ M * e n) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hCO⟩ := hd.exists_pos
  have hbound := hCO.bound
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨N, hN⟩ := hbound
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _)
      _ (tendsto_const_div_atTop_nhds_zero_nat (2 * C))
  filter_upwards [Filter.eventually_ge_atTop (max N 2)] with n hn
  have hnN : N ≤ n := (Nat.le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let A : ℝ := C * (((n : ℝ) ^ M)⁻¹)
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hmajor : ∀ k : ℕ,
      |e (k + n + 1) - e (k + n)| ≤ A * (((k + n : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro k
    have hnkn : N ≤ k + n := hnN.trans (by omega)
    have hkpos : (0 : ℝ) < k + n := by exact_mod_cast (by omega : 0 < k + n)
    have hraw := hN (k + n) hnkn
    have hraw' : |e (k + n + 1) - e (k + n)| ≤
        C * (((k + n : ℝ) ^ (M + 2))⁻¹) := by
      simpa only [Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos hkpos,
        Nat.cast_add, Nat.cast_ofNat] using hraw
    have hle : (((k + n : ℝ) ^ M)⁻¹) ≤ (((n : ℝ) ^ M)⁻¹) := by
      apply (inv_le_inv₀ (pow_pos hkpos M) (pow_pos hnpos M)).2
      exact pow_le_pow_left₀ (le_of_lt hnpos) (by exact_mod_cast (show n ≤ k + n by omega)) M
    calc
      |e (k + n + 1) - e (k + n)| ≤ C * (((k + n : ℝ) ^ (M + 2))⁻¹) := hraw'
      _ = C * (((k + n : ℝ) ^ M)⁻¹) * (((k + n : ℝ) ^ 2)⁻¹) := by
        rw [show M + 2 = M + 2 by rfl, pow_add, mul_inv]
        ring
      _ ≤ C * (((n : ℝ) ^ M)⁻¹) * (((k + n : ℝ) ^ 2)⁻¹) := by
        gcongr
      _ = A * (((k + n : ℕ) : ℝ) ^ 2)⁻¹ := by
        simp only [A, Nat.cast_add]
  have htail : |e n| ≤ A * (2 / (n : ℝ)) := by
    have htel (L : ℕ) :
        (∑ k ∈ Finset.range L, (e (k + n + 1) - e (k + n))) = e (L + n) - e n := by
      have h := Finset.sum_range_sub (fun k => e (k + n)) L
      simpa only [Nat.add_assoc, Nat.add_comm n 1, Nat.zero_add] using h
    have hfinite (L : ℕ) : |e (L + n) - e n| ≤ A * (2 / (n : ℝ)) := by
      rw [← htel L]
      calc
        |∑ k ∈ Finset.range L, (e (k + n + 1) - e (k + n))| ≤
            ∑ k ∈ Finset.range L, |e (k + n + 1) - e (k + n)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range L, A * (((k + n : ℕ) : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum
          intro k hk
          exact hmajor k
        _ = A * ∑ k ∈ Finset.range L, (((k + n : ℕ) : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
        _ ≤ A * (2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (catalanExp_sum_range_inv_sq_le n L hn2) hAnonneg
    have hlim : Filter.Tendsto (fun L : ℕ => |e (L + n) - e n|)
        Filter.atTop (nhds |e n|) := by
      have h := (he.comp (Filter.tendsto_add_atTop_nat n)).sub_const (e n)
      simpa using h.abs
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hfinite)
  calc
    ‖(n : ℝ) ^ M * e n‖ = (n : ℝ) ^ M * |e n| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hnpos M)]
    _ ≤ (n : ℝ) ^ M * (A * (2 / (n : ℝ))) := by gcongr
    _ = (2 * C) / (n : ℝ) := by
      dsimp [A]
      field_simp

/--
An all-orders Bernoulli-polynomial expansion obtained from a logarithmic
first-difference equation. The normalization `u n → 0` fixes the otherwise
undetermined additive constant. Its coefficients use Mathlib's
`Polynomial.bernoulli`, evaluated by `Polynomial.aeval`.
-/
public theorem _root_.Real.tendsto_pow_mul_sub_bernoulli_sum_of_log_diff
    {u : ℕ → ℝ} (α β c : ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds 0))
    (hstep : ∀ᶠ n : ℕ in Filter.atTop,
      u (n + 1) - u n =
        Real.log (1 + α / (n + c : ℝ)) - Real.log (1 + β / (n + c : ℝ)) +
          (β - α) * Real.log (1 + 1 / (n + c : ℝ))) :
    ∀ M : ℕ,
      Filter.Tendsto
        (fun n : ℕ =>
          (n + c : ℝ) ^ M *
            (u n - ∑ j ∈ Finset.range M,
              (-1 : ℝ) ^ (j + 2) *
                (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
                  Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
                  ((j + 1 : ℕ) * (j + 2 : ℕ)) *
                (1 / (n + c : ℝ) ^ (j + 1))))
        Filter.atTop (nhds 0) := by
  intro M
  let x : ℕ → ℝ := fun n => (n : ℝ) + c
  let y : ℕ → ℝ := fun n => 1 / x n
  let e : ℕ → ℝ := fun n => u n - catalanExpBernoulliSum α β M (y n)
  have hxtop : Filter.Tendsto x Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_add_const_right Filter.atTop c tendsto_natCast_atTop_atTop
  have hy : Filter.Tendsto y Filter.atTop (nhds 0) := by
    exact hxtop.const_div_atTop 1
  have hnorm : Filter.Tendsto (fun n : ℕ => ‖(n : ℝ)‖) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.congr' (by simp)
  have hx_equiv : Asymptotics.IsEquivalent Filter.atTop x (fun n : ℕ => (n : ℝ)) := by
    simpa only [x] using
      (Asymptotics.IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm (c := c))
  have hsum0 : Filter.Tendsto
      (fun n : ℕ => catalanExpBernoulliSum α β M (y n)) Filter.atTop (nhds 0) := by
    unfold catalanExpBernoulliSum
    convert tendsto_finsetSum (Finset.range M) (fun j hj =>
      tendsto_const_nhds.mul (hy.pow (j + 1))) using 1
    all_goals simp
  have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
    simpa only [e, sub_zero] using hu.sub hsum0
  have hdiff : ∀ᶠ n : ℕ in Filter.atTop,
      e (n + 1) - e n = catalanExpLocalResidual α β M (y n) := by
    have hxpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < x n :=
      hxtop.eventually (Filter.eventually_gt_atTop 0)
    filter_upwards [hstep, hxpos] with n hn hnpos
    have hxne : x n ≠ 0 := ne_of_gt hnpos
    have hxone : x n + 1 ≠ 0 := ne_of_gt (by linarith)
    have hx_succ : x (n + 1) = x n + 1 := by
      dsimp [x]
      push_cast
      ring
    have hyden : 1 + 1 / x n ≠ 0 := by positivity
    have hy_succ : y (n + 1) = y n / (1 + y n) := by
      dsimp only [y]
      rw [hx_succ]
      field_simp [hxne, hxone, hyden]
    have hn' : u (n + 1) - u n = catalanExpLogStep α β (y n) := by
      rw [hn]
      unfold catalanExpLogStep
      dsimp [x, y]
      congr 1
      all_goals ring_nf
    dsimp [e]
    rw [hy_succ]
    unfold catalanExpLocalResidual
    linear_combination hn'
  have hdiff_shift : (fun n : ℕ => e (n + 1) - e n) =O[Filter.atTop]
      fun n : ℕ => (y n) ^ (M + 2) := by
    have hcomp := (catalanExp_localResidual_isBigO α β M).comp_tendsto hy
    apply hcomp.congr'
    · filter_upwards [hdiff] with n hn
      simpa only [Function.comp_apply] using hn.symm
    · exact Filter.EventuallyEq.rfl
  have hshift_nat : (fun n : ℕ => (y n) ^ (M + 2)) =O[Filter.atTop]
      fun n : ℕ => (((n : ℝ) ^ (M + 2))⁻¹) := by
    have h := ((hx_equiv.pow (M + 2)).inv).isBigO
    apply h.congr
    · intro n
      simp only [x, y, Pi.pow_apply, Pi.inv_apply, one_div, inv_pow]
    · intro n
      simp only [Pi.pow_apply, Pi.inv_apply]
  have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ M * e n)
      Filter.atTop (nhds 0) :=
    catalanExp_tendsto_nat_pow_mul_of_diff_isBigO e M he (hdiff_shift.trans hshift_nat)
  have hmul := (hx_equiv.pow M).isBigO.mul
    (Asymptotics.isBigO_refl e Filter.atTop)
  have hresult : Filter.Tendsto (fun n : ℕ => x n ^ M * e n)
      Filter.atTop (nhds 0) := by
    apply hmul.trans_tendsto
    simpa only [Pi.pow_apply, Pi.mul_apply] using hnat
  simpa only [x, y, e, catalanExpBernoulliSum, catalanExpBernoulliCoeff,
    one_div_pow, Nat.add_assoc] using hresult

private lemma catalanExp_shifted_log_eq (c : ℝ) (n : ℕ) (hn : 0 < n)
    (hx : 0 < (n : ℝ) + c) :
    Real.log ((catalan n : ℝ) *
        Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) / (4 : ℝ) ^ n) =
      Real.log ((catalan n : ℝ) *
        ((n : ℝ) * Real.sqrt (Real.pi * n)) / (4 : ℝ) ^ n) +
        (3 / 2 : ℝ) * Real.log (((n : ℝ) + c) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hC := catalanExp_catalan_pos n
  have hP : 0 < Real.pi * ((n : ℝ) + c) ^ 3 :=
    mul_pos Real.pi_pos (pow_pos hx 3)
  have hQ : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  have hF : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hsP : Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hP
  have hsQ : Real.sqrt (Real.pi * (n : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hQ
  rw [Real.log_div (mul_ne_zero hC.ne' hsP) hF,
    Real.log_div (mul_ne_zero hC.ne' (mul_ne_zero hnR.ne' hsQ)) hF,
    Real.log_div hx.ne' hnR.ne', Real.log_mul hC.ne' hsP,
    Real.log_mul hC.ne' (mul_ne_zero hnR.ne' hsQ),
    Real.log_mul hnR.ne' hsQ, Real.log_sqrt hP.le, Real.log_sqrt hQ.le,
    Real.log_mul Real.pi_ne_zero (pow_ne_zero 3 hx.ne'),
    Real.log_mul Real.pi_ne_zero hnR.ne', Real.log_pow, Real.log_pow]
  ring

private theorem catalanExp_shifted_log_tendsto_zero (c : ℝ) :
    Filter.Tendsto (fun n : ℕ =>
      Real.log ((catalan n : ℝ) *
        Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) / (4 : ℝ) ^ n))
      Filter.atTop (nhds 0) := by
  have hcdiv : Filter.Tendsto (fun n : ℕ => c / (n : ℝ))
      Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat c
  have hratio : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + c) / n)
      Filter.atTop (nhds 1) := by
    have hsum : Filter.Tendsto (fun n : ℕ => 1 + c / (n : ℝ))
        Filter.atTop (nhds 1) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).add hcdiv
    have heq : (fun n : ℕ => ((n : ℝ) + c) / n) =ᶠ[Filter.atTop]
        (fun n : ℕ => 1 + c / (n : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    exact Filter.Tendsto.congr' heq.symm hsum
  have hlog : Filter.Tendsto (fun n : ℕ =>
      Real.log (((n : ℝ) + c) / n)) Filter.atTop (nhds 0) := by
    simpa using hratio.log one_ne_zero
  have hcorr : Filter.Tendsto (fun n : ℕ =>
      (3 / 2 : ℝ) * Real.log (((n : ℝ) + c) / n))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlog
  have hxTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + c)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c tendsto_natCast_atTop_atTop
  have heq : (fun n : ℕ =>
      Real.log ((catalan n : ℝ) *
        Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) / (4 : ℝ) ^ n)) =ᶠ[Filter.atTop]
      (fun n : ℕ =>
        Real.log ((catalan n : ℝ) *
          ((n : ℝ) * Real.sqrt (Real.pi * n)) / (4 : ℝ) ^ n) +
          (3 / 2 : ℝ) * Real.log (((n : ℝ) + c) / n)) := by
    filter_upwards [Filter.eventually_ge_atTop 1,
      hxTop.eventually (Filter.eventually_gt_atTop 0)] with n hn hx
    exact catalanExp_shifted_log_eq c n (by omega) hx
  exact Filter.Tendsto.congr' heq.symm <| by
    simpa only [add_zero] using catalanExp_first_log_tendsto_zero.add hcorr

private lemma catalanExp_base_log_step (n : ℕ) (hn : 0 < n) :
    Real.log ((catalan (n + 1) : ℝ) *
        ((n + 1 : ℝ) * Real.sqrt (Real.pi * (n + 1 : ℝ))) /
          (4 : ℝ) ^ (n + 1)) -
      Real.log ((catalan n : ℝ) *
        ((n : ℝ) * Real.sqrt (Real.pi * n)) / (4 : ℝ) ^ n) =
      Real.log ((n : ℝ) + 1 / 2) - Real.log ((n : ℝ) + 2) +
        (3 / 2 : ℝ) *
          (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hC := catalanExp_catalan_pos n
  have hCs := catalanExp_catalan_pos (n + 1)
  have hPn : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  have hPns : 0 < Real.pi * ((n : ℝ) + 1) := mul_pos Real.pi_pos hn1R
  have hsPn : Real.sqrt (Real.pi * (n : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPn
  have hsPns : Real.sqrt (Real.pi * ((n : ℝ) + 1)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPns
  have hcatlog : Real.log (catalan (n + 1) : ℝ) -
      Real.log (catalan n : ℝ) =
      Real.log 4 + Real.log ((n : ℝ) + 1 / 2) -
        Real.log ((n : ℝ) + 2) := by
    rw [← Real.log_div hCs.ne' hC.ne', catalanExp_catalan_succ_ratio]
    have hrewrite : 2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 2) =
        4 * (((n : ℝ) + 1 / 2) / ((n : ℝ) + 2)) := by ring
    rw [hrewrite, Real.log_mul (by norm_num) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    ring
  rw [Real.log_div (mul_ne_zero hCs.ne' (mul_ne_zero hn1R.ne' hsPns))
      (by positivity),
    Real.log_div (mul_ne_zero hC.ne' (mul_ne_zero hnR.ne' hsPn))
      (by positivity),
    Real.log_mul hCs.ne' (mul_ne_zero hn1R.ne' hsPns),
    Real.log_mul hC.ne' (mul_ne_zero hnR.ne' hsPn),
    Real.log_mul hn1R.ne' hsPns, Real.log_mul hnR.ne' hsPn,
    Real.log_sqrt hPns.le, Real.log_sqrt hPn.le,
    Real.log_mul Real.pi_ne_zero hn1R.ne',
    Real.log_mul Real.pi_ne_zero hnR.ne', Real.log_pow, Real.log_pow]
  push_cast
  linear_combination hcatlog

private lemma catalanExp_shifted_log_step (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.log ((catalan (n + 1) : ℝ) *
          Real.sqrt (Real.pi * ((n + 1 : ℝ) + c) ^ 3) /
            (4 : ℝ) ^ (n + 1)) -
        Real.log ((catalan n : ℝ) *
          Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) / (4 : ℝ) ^ n) =
        Real.log (1 + (1 / 2 - c) / (n + c : ℝ)) -
          Real.log (1 + (2 - c) / (n + c : ℝ)) +
          (3 / 2 : ℝ) * Real.log (1 + 1 / (n + c : ℝ)) := by
  have hxTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + c)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1,
    hxTop.eventually (Filter.eventually_gt_atTop 0)] with n hn hx
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1R : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx1 : 0 < (n : ℝ) + c + 1 := by linarith
  have hshiftSucc := catalanExp_shifted_log_eq c (n + 1) (by omega)
    (by push_cast; linarith)
  push_cast at hshiftSucc
  have hbase := catalanExp_base_log_step n hn0
  rw [hshiftSucc, catalanExp_shifted_log_eq c n hn0 hx]
  have ha : 1 + (1 / 2 - c) / ((n : ℝ) + c) =
      ((n : ℝ) + 1 / 2) / ((n : ℝ) + c) := by
    field_simp
    ring
  have hb : 1 + (2 - c) / ((n : ℝ) + c) =
      ((n : ℝ) + 2) / ((n : ℝ) + c) := by
    field_simp
    ring
  have hone : 1 + 1 / ((n : ℝ) + c) =
      ((n : ℝ) + c + 1) / ((n : ℝ) + c) := by
    field_simp
  rw [ha, hb, hone, show (n : ℝ) + 1 + c = (n : ℝ) + c + 1 by ring,
    Real.log_div hx1.ne' hn1R.ne', Real.log_div hx.ne' hnR.ne',
    Real.log_div (by positivity) hx.ne', Real.log_div (by positivity) hx.ne',
    Real.log_div hx1.ne' hx.ne']
  linear_combination hbase

/--
The all-orders logarithmic asymptotic expansion of the Catalan numbers at an
arbitrary real shift, with coefficients given by differences of Bernoulli polynomials.
-/
public theorem _root_.tendsto_pow_mul_log_catalan_sub_bernoulli_sum (c : ℝ) :
    ∀ M : ℕ,
      Filter.Tendsto
        (fun n : ℕ =>
          (n + c : ℝ) ^ M *
            (Real.log ((catalan n : ℝ) *
                Real.sqrt (Real.pi * (n + c : ℝ) ^ 3) / (4 : ℝ) ^ n) -
              ∑ j ∈ Finset.range M,
                (-1 : ℝ) ^ (j + 2) *
                  (Polynomial.aeval (1 / 2 - c) (Polynomial.bernoulli (j + 2)) -
                    Polynomial.aeval (2 - c) (Polynomial.bernoulli (j + 2))) /
                    ((j + 1 : ℕ) * (j + 2 : ℕ)) *
                  (1 / (n + c : ℝ) ^ (j + 1))))
        Filter.atTop (nhds 0) := by
  refine Real.tendsto_pow_mul_sub_bernoulli_sum_of_log_diff
    (u := fun n : ℕ => Real.log ((catalan n : ℝ) *
      Real.sqrt (Real.pi * (n + c : ℝ) ^ 3) / (4 : ℝ) ^ n))
    (1 / 2 - c) (2 - c) c (catalanExp_shifted_log_tendsto_zero c) ?_
  filter_upwards [catalanExp_shifted_log_step c] with n hn
  simpa only [Nat.cast_add, Nat.cast_one,
    show (2 - c) - (1 / 2 - c) = (3 / 2 : ℝ) by ring] using hn

private lemma catalanExp_first_log_eventuallyEq :
    (fun n : ℕ => Real.log ((catalan n : ℝ) *
      Real.sqrt (Real.pi * (n : ℝ) ^ 3) / (4 : ℝ) ^ n)) =ᶠ[Filter.atTop]
    (fun n : ℕ => Real.log ((catalan n : ℝ) *
      ((n : ℝ) * Real.sqrt (Real.pi * n)) / (4 : ℝ) ^ n)) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have h := catalanExp_shifted_log_eq 0 n hn0 (by positivity)
  simpa only [add_zero, div_self hnR, Real.log_one, mul_zero, add_zero] using h

private lemma catalanExp_first_sum_eq (m n : ℕ) :
    (∑ j ∈ Finset.range m,
      (-1 : ℝ) ^ (j + 2) *
        (catalanExpBernoulliPolynomialEval (j + 2) (1 / 2) -
          catalanExpBernoulliPolynomialEval (j + 2) 2) /
          ((j + 1 : ℕ) * (j + 2 : ℕ)) *
        (1 / (n : ℝ) ^ (j + 1))) =
      ∑ j ∈ Finset.range m,
        (-1 : ℝ) ^ (j + 2) *
          ((((2 : ℝ) ^ (j + 1))⁻¹ - 2) *
              (bernoulli (j + 2) : ℝ) - (j + 1 : ℕ) - 1) /
            ((j + 1 : ℕ) * (j + 2 : ℕ)) *
          (1 / ((n : ℝ) ^ (j + 1))) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [catalanExp_first_bernoulli_difference]

private lemma catalanExp_sum_range_two_mul {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k =
      ∑ r ∈ Finset.range m, (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      conv_lhs =>
        rw [show 2 * (m + 1) = 2 * m + 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [ih]
      simp only [add_assoc]

private lemma catalanExp_second_sum_eq (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0)
    (m n : ℕ) :
    (∑ j ∈ Finset.range (2 * m),
      (-1 : ℝ) ^ (j + 2) *
        (catalanExpBernoulliPolynomialEval (j + 2) (-1 / 4) -
          catalanExpBernoulliPolynomialEval (j + 2) (5 / 4)) /
          ((j + 1 : ℕ) * (j + 2 : ℕ)) *
        (1 / ((n : ℝ) + 3 / 4) ^ (j + 1))) =
      ∑ j ∈ Finset.range m,
        ((2 : ℝ) ^ (4 * (j + 1) + 2))⁻¹ *
          (4 - (E (2 * (j + 1)) : ℝ)) / (j + 1 : ℕ) *
          (1 / ((n : ℝ) + 3 / 4) ^ (2 * (j + 1))) := by
  rw [catalanExp_sum_range_two_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [catalanExp_second_odd_bernoulli_difference r]
  simp only [mul_zero, zero_div, zero_mul, zero_add]
  have hcoef := catalanExp_second_even_coefficient E hE (r + 1) (by omega)
  have hmul := congrArg
    (fun z : ℝ => z * (1 / ((n : ℝ) + 3 / 4) ^ (2 * (r + 1)))) hcoef
  convert hmul using 1

/--
**Stirling-type asymptotic expansions of the Catalan numbers.** Let $C_n$ be the $n$-th Catalan
number and $B_k$ the $k$-th Bernoulli number, and let $(E_k)$ be a sequence of integers with
$E_0 = 1$ and $\sum_{j=0}^{\lfloor n/2 \rfloor} \binom{n}{2j} E_{n-2j} = 0$ for every $n > 0$
(these are the Euler numbers $1, 0, -1, 0, 5, \dots$). For $k \ge 1$ put
$c_k = (-1)^{k+1} \left((2^{-k} - 2) B_{k+1} - k - 1\right) / (k (k + 1))$ and
$d_k = 2^{-4k-2} (4 - E_{2k}) / k$. Then for every $m \ge 0$, as $n \to \infty$,
$\log\left(C_n \, n \sqrt{\pi n} / 4^n\right) = \sum_{k=1}^{m} c_k n^{-k} + o(n^{-m})$ and,
writing $x = n + 3/4$,
$\log\left(C_n \sqrt{\pi x^3} / 4^n\right) = \sum_{k=1}^{m} d_k x^{-2k} + o(x^{-2m})$.

The first coefficient is $c_1 = -9/8$, matching the classical expansion
$C_n = \frac{4^n}{\sqrt{\pi} \, n^{3/2}} \left(1 - \frac{9}{8n} + \dots\right)$.

Proof: The Catalan recurrence gives a logarithmic first-difference equation.
Telescoping its Bernoulli-polynomial expansion yields both all-orders formulas.

Proves `Wanted` entry `catalan_stirling_asymptotic_expansions`.

Source: Neven Elezović, "Asymptotic Expansions of Central Binomial
Coefficients and Catalan Numbers," Journal of Integer Sequences 17 (2014),
Article 14.2.1, Catalan Stirling-type theorem (unlabeled, equation 42),
lines 626–637,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Elezovic/elezovic5.tex
-/
public theorem catalan_stirling_asymptotic_expansions
    (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) :
    ((∀ m : ℕ,
      Filter.Tendsto
        (fun n : ℕ =>
          (n : ℝ) ^ m *
            (Real.log
                ((catalan n : ℝ) * ((n : ℝ) * Real.sqrt (Real.pi * n)) /
                  (4 : ℝ) ^ n) -
              ∑ j ∈ Finset.range m,
                (-1 : ℝ) ^ (j + 2) *
                  ((((2 : ℝ) ^ (j + 1))⁻¹ - 2) *
                      (bernoulli (j + 2) : ℝ) - (j + 1 : ℕ) - 1) /
                    ((j + 1 : ℕ) * (j + 2 : ℕ)) *
                  (1 / ((n : ℝ) ^ (j + 1)))))
        Filter.atTop (nhds 0)) ∧
    (∀ m : ℕ,
      Filter.Tendsto
        (fun n : ℕ =>
          (n + 3 / 4 : ℝ) ^ (2 * m) *
            (Real.log
                ((catalan n : ℝ) *
                    Real.sqrt (Real.pi * (n + 3 / 4 : ℝ) ^ 3) /
                  (4 : ℝ) ^ n) -
              ∑ j ∈ Finset.range m,
                ((2 : ℝ) ^ (4 * (j + 1) + 2))⁻¹ *
                  (4 - (E (2 * (j + 1)) : ℝ)) / (j + 1 : ℕ) *
                  (1 / ((n + 3 / 4 : ℝ) ^ (2 * (j + 1))))))
        Filter.atTop (nhds 0))) := by
  constructor
  · intro m
    have h := tendsto_pow_mul_log_catalan_sub_bernoulli_sum 0 m
    simp only [← catalanExp_bernoulliPolynomialEval_eq] at h
    refine h.congr' ?_
    filter_upwards [catalanExp_first_log_eventuallyEq] with n hlog
    simp only [add_zero, sub_zero] at *
    rw [hlog, catalanExp_first_sum_eq]
  · intro m
    have h := tendsto_pow_mul_log_catalan_sub_bernoulli_sum (3 / 4) (2 * m)
    simp only [← catalanExp_bernoulliPolynomialEval_eq] at h
    refine h.congr' ?_
    filter_upwards with n
    norm_num only [show (1 / 2 : ℝ) - 3 / 4 = -1 / 4 by norm_num,
      show (2 : ℝ) - 3 / 4 = 5 / 4 by norm_num]
    rw [show -(1 / 4 : ℝ) = -1 / 4 by norm_num]
    rw [catalanExp_second_sum_eq E hE m n]

end

end MetaMathlibExt
