/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.NumberTheory.GeneralizedTribonacci
public import MathlibExt.NumberTheory.GibonacciNumber
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.DivRunCountFour
import MathlibExt.NumberTheory.DivisibilityRuns
import MathlibExt.NumberTheory.GeneralizedTribonacciBasis
import MathlibExt.NumberTheory.DivisibilityRunsGibonacciNumberEqFib

/-!
# Growth bounds for Gibonacci and generalized Tribonacci sequences

This module proves upper exponential bounds for Gibonacci numbers and generalized Tribonacci
numbers, and an exponential lower bound for Gibonacci numbers above a logarithmic threshold.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 1
(`integers-2026-A122-lem-1`), with the threshold as used in the proof of Theorem 2.
-/

namespace MetaMathlibExt

/-- Upper bound for two consecutive Gibonacci numbers, proved jointly for the induction. -/
private theorem gibonacci_abs_le_two_step (x y : ℤ) (m : ℕ) :
    |(gibonacciNumber x y m : ℝ)| ≤ (|(x : ℝ)| + |(y : ℝ)|) * Real.goldenRatio ^ m ∧
    |(gibonacciNumber x y (m + 1) : ℝ)|
      ≤ (|(x : ℝ)| + |(y : ℝ)|) * Real.goldenRatio ^ (m + 1) := by
  induction m with
  | zero =>
    have e0 : gibonacciNumber x y 0 = x := rfl
    have e1 : gibonacciNumber x y (0 + 1) = y := rfl
    have hS : (0 : ℝ) ≤ |(x : ℝ)| + |(y : ℝ)| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hφ : (1 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.one_lt_goldenRatio
    refine ⟨?_, ?_⟩
    · rw [e0]
      simp only [pow_zero, mul_one]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [e1, show (0 : ℕ) + 1 = 1 from rfl, pow_one]
      calc |(y : ℝ)| ≤ |(x : ℝ)| + |(y : ℝ)| := le_add_of_nonneg_left (abs_nonneg _)
        _ = (|(x : ℝ)| + |(y : ℝ)|) * 1 := (mul_one _).symm
        _ ≤ (|(x : ℝ)| + |(y : ℝ)|) * Real.goldenRatio :=
            mul_le_mul_of_nonneg_left hφ hS
  | succ m ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    have hidx : m + 1 + 1 = m + 2 := by omega
    have hrec : gibonacciNumber x y (m + 2)
        = gibonacciNumber x y (m + 1) + gibonacciNumber x y m := rfl
    have hφ2 : Real.goldenRatio ^ (m + 2)
        = Real.goldenRatio ^ (m + 1) + Real.goldenRatio ^ m := by
      have e1 : Real.goldenRatio ^ (m + 2)
          = Real.goldenRatio ^ m * Real.goldenRatio ^ 2 := by rw [pow_add]
      have e2 : Real.goldenRatio ^ (m + 1)
          = Real.goldenRatio ^ m * Real.goldenRatio := by rw [pow_add, pow_one]
      rw [e1, e2, Real.goldenRatio_sq]
      ring
    rw [hidx, hrec]
    push_cast
    calc |(gibonacciNumber x y (m + 1) : ℝ) + (gibonacciNumber x y m : ℝ)|
          ≤ |(gibonacciNumber x y (m + 1) : ℝ)| + |(gibonacciNumber x y m : ℝ)| :=
            abs_add_le _ _
        _ ≤ (|(x : ℝ)| + |(y : ℝ)|) * Real.goldenRatio ^ (m + 1)
            + (|(x : ℝ)| + |(y : ℝ)|) * Real.goldenRatio ^ m := add_le_add ih1 ih0
        _ = (|(x : ℝ)| + |(y : ℝ)|) * Real.goldenRatio ^ (m + 2) := by
            rw [hφ2]; ring

/-- A real root of the Tribonacci equation is at least one. -/
private theorem one_le_of_tribonacci_root (τ : ℝ) (hτ : τ ^ 3 = τ ^ 2 + τ + 1) :
    1 ≤ τ := by
  have hpos : 0 < τ := by
    by_contra hcon
    have hle : τ ≤ 0 := not_lt.mp hcon
    have h3 : τ ^ 3 ≤ 0 := by
      have hsq : (0 : ℝ) ≤ τ ^ 2 := sq_nonneg τ
      have e : τ ^ 3 = τ * τ ^ 2 := by ring
      rw [e]
      exact mul_nonpos_of_nonpos_of_nonneg hle hsq
    have hgt : (0 : ℝ) < τ ^ 2 + τ + 1 := by nlinarith [sq_nonneg (τ + 1 / 2)]
    have h4 : (0 : ℝ) < τ ^ 3 := by rw [hτ]; exact hgt
    linarith
  by_contra hcon
  have hle : τ ≤ 1 := le_of_lt (not_le.mp hcon)
  have h3 : τ ^ 3 ≤ 1 := pow_le_one₀ (le_of_lt hpos) hle
  have hgt : (1 : ℝ) < τ ^ 2 + τ + 1 := by
    have hsq : (0 : ℝ) ≤ τ ^ 2 := sq_nonneg τ
    linarith
  have h4 : (1 : ℝ) < τ ^ 3 := by rw [hτ]; exact hgt
  linarith

/-- Upper bound for three consecutive generalized Tribonacci numbers. -/
private theorem generalizedTribonacci_abs_le_three_step (τ : ℝ)
    (hτ : τ ^ 3 = τ ^ 2 + τ + 1) (a b c : ℤ) (m : ℕ) :
    |(generalizedTribonacci a b c m : ℝ)|
      ≤ (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ m ∧
    |(generalizedTribonacci a b c (m + 1) : ℝ)|
      ≤ (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ (m + 1) ∧
    |(generalizedTribonacci a b c (m + 2) : ℝ)|
      ≤ (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ (m + 2) := by
  have h1τ : 1 ≤ τ := one_le_of_tribonacci_root τ hτ
  have hS : (0 : ℝ) ≤ |(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hτ3 : ∀ k : ℕ, τ ^ (k + 3) = τ ^ (k + 2) + τ ^ (k + 1) + τ ^ k := by
    intro k
    have e1 : τ ^ (k + 3) = τ ^ k * τ ^ 3 := by rw [pow_add]
    have e2 : τ ^ (k + 2) = τ ^ k * τ ^ 2 := by rw [pow_add]
    have e3 : τ ^ (k + 1) = τ ^ k * τ := by rw [pow_add, pow_one]
    rw [e1, e2, e3]
    linear_combination τ ^ k * hτ
  induction m with
  | zero =>
    have hτ1 : (1 : ℝ) ≤ τ ^ 2 := one_le_pow₀ h1τ
    refine ⟨?_, ?_, ?_⟩
    · simp only [generalizedTribonacci_zero, pow_zero, mul_one]
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans
        (le_add_of_nonneg_right (abs_nonneg _))
    · rw [show (0 : ℕ) + 1 = 1 from rfl, generalizedTribonacci_one, pow_one]
      calc |(b : ℝ)| ≤ |(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| :=
            (le_add_of_nonneg_left (abs_nonneg _)).trans
              (le_add_of_nonneg_right (abs_nonneg _))
        _ = (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * 1 := (mul_one _).symm
        _ ≤ (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ :=
            mul_le_mul_of_nonneg_left h1τ hS
    · rw [show (0 : ℕ) + 2 = 2 from rfl, generalizedTribonacci_two]
      calc |(c : ℝ)| ≤ |(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| :=
            le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * 1 := (mul_one _).symm
        _ ≤ (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ 2 :=
            mul_le_mul_of_nonneg_left hτ1 hS
  | succ m ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    have i1 : m + 1 + 1 = m + 2 := by omega
    have i2 : m + 1 + 2 = m + 3 := by omega
    refine ⟨ih1, ?_, ?_⟩
    · rw [i1]; exact ih2
    · rw [i2, generalizedTribonacci_add_three]
      push_cast
      calc |(generalizedTribonacci a b c (m + 2) : ℝ)
              + (generalizedTribonacci a b c (m + 1) : ℝ)
              + (generalizedTribonacci a b c m : ℝ)|
            ≤ |(generalizedTribonacci a b c (m + 2) : ℝ)
              + (generalizedTribonacci a b c (m + 1) : ℝ)|
              + |(generalizedTribonacci a b c m : ℝ)| := abs_add_le _ _
          _ ≤ (|(generalizedTribonacci a b c (m + 2) : ℝ)|
              + |(generalizedTribonacci a b c (m + 1) : ℝ)|)
              + |(generalizedTribonacci a b c m : ℝ)| :=
              add_le_add (abs_add_le _ _) le_rfl
          _ ≤ ((|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ (m + 2)
              + (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ (m + 1))
              + (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ m :=
              add_le_add (add_le_add ih2 ih1) ih0
          _ = (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ (m + 3) := by
              rw [hτ3 m]; ring

/-- Fibonacci numbers dominate powers of the golden ratio, two steps jointly. -/
private theorem fib_lower_two_step (m : ℕ) :
    Real.goldenRatio ^ m ≤ (Nat.fib (m + 2) : ℝ) ∧
    Real.goldenRatio ^ (m + 1) ≤ (Nat.fib (m + 3) : ℝ) := by
  induction m with
  | zero =>
    have e2 : Nat.fib (0 + 2) = 1 := rfl
    have e3 : Nat.fib (0 + 3) = 2 := rfl
    have e2R : ((2 : ℕ) : ℝ) = 2 := by norm_num
    refine ⟨?_, ?_⟩
    · rw [e2]
      simp
    · rw [e3, show (0 : ℕ) + 1 = 1 from rfl, pow_one, e2R]
      exact le_of_lt Real.goldenRatio_lt_two
  | succ m ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have i1 : m + 1 + 2 = m + 3 := by omega
    have i2 : m + 1 + 3 = m + 2 + 2 := by omega
    have i3 : m + 2 + 1 = m + 3 := by omega
    have hφ2 : Real.goldenRatio ^ (m + 1 + 1)
        = Real.goldenRatio ^ (m + 1) + Real.goldenRatio ^ m := by
      have j : m + 1 + 1 = m + 2 := by omega
      have e1 : Real.goldenRatio ^ (m + 2)
          = Real.goldenRatio ^ m * Real.goldenRatio ^ 2 := by rw [pow_add]
      have e2 : Real.goldenRatio ^ (m + 1)
          = Real.goldenRatio ^ m * Real.goldenRatio := by rw [pow_add, pow_one]
      rw [j, e1, e2, Real.goldenRatio_sq]
      ring
    refine ⟨?_, ?_⟩
    · rw [i1]; exact ih1
    · rw [i2, Nat.fib_add_two, i3]
      push_cast
      calc Real.goldenRatio ^ (m + 1 + 1)
            = Real.goldenRatio ^ (m + 1) + Real.goldenRatio ^ m := hφ2
        _ ≤ (Nat.fib (m + 3) : ℝ) + (Nat.fib (m + 2) : ℝ) := add_le_add ih1 ih0
        _ = (Nat.fib (m + 2) : ℝ) + (Nat.fib (m + 3) : ℝ) := add_comm _ _

/-- The Gibonacci norm form vanishes only at the origin. -/
private theorem gibonacci_norm_ne_zero (x y : ℤ) (hne : (x, y) ≠ (0, 0)) :
    x ^ 2 + x * y - y ^ 2 ≠ 0 := by
  intro hcon
  have hsq : (2 * x + y) ^ 2 = 5 * y ^ 2 := by linear_combination 4 * hcon
  by_cases hy : y = 0
  · subst hy
    have hx2 : x ^ 2 = 0 := by linear_combination hcon
    have hx : x = 0 := sq_eq_zero_iff.mp hx2
    exact hne (by simp [hx])
  · have hyR : ((y : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hy
    have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy
    set q : ℚ := ((2 * x + y : ℤ) : ℚ) / (y : ℚ) with hqdef
    have hq2 : ((q : ℚ) : ℝ) ^ 2 = 5 := by
      have hAB : ((2 * x + y : ℤ) : ℝ) ^ 2 = 5 * ((y : ℤ) : ℝ) ^ 2 := by
        exact_mod_cast hsq
      have hX : ((y : ℤ) : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hyR
      have hcancel : (5 : ℝ) = 5 * ((y : ℤ) : ℝ) ^ 2 / ((y : ℤ) : ℝ) ^ 2 :=
        (eq_div_iff hX).mpr rfl
      rw [hqdef, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, div_pow, hAB]
      exact hcancel.symm
    have habs : Real.sqrt 5 = |((q : ℚ) : ℝ)| := by
      have h5 : (5 : ℝ) = ((q : ℚ) : ℝ) ^ 2 := hq2.symm
      rw [h5, Real.sqrt_sq_eq_abs]
    have hrat : Real.sqrt 5 = (((|q| : ℚ)) : ℝ) := by
      rw [habs]
      exact (Rat.cast_abs q).symm
    have h5irr : Irrational (Real.sqrt 5) := by
      have h := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by decide)
      simpa using h
    exact (h5irr.ne_rat |q|) hrat

/-- The size of the initial values is at least one off the origin. -/
private theorem gibonacci_size_ge_one (x y : ℤ) (hne : (x, y) ≠ (0, 0)) :
    1 ≤ |(x : ℝ)| + |(y : ℝ)| := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy0
      exact hne (by simp [hx, hy0])
    have h1 : (1 : ℝ) ≤ |(y : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hy
    calc (1 : ℝ) ≤ |(y : ℝ)| := h1
      _ ≤ |(x : ℝ)| + |(y : ℝ)| := le_add_of_nonneg_left (abs_nonneg _)
  · have h1 : (1 : ℝ) ≤ |(x : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hx
    calc (1 : ℝ) ≤ |(x : ℝ)| := h1
      _ ≤ |(x : ℝ)| + |(y : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)

/-- The Binet coefficient of a Gibonacci sequence is bounded away from zero. -/
private theorem gibonacci_coeff_lower (x y : ℤ) (hne : (x, y) ≠ (0, 0)) :
    1 / (|(x : ℝ)| + |(y : ℝ)|) ≤ |(x : ℝ) + (y : ℝ) * Real.goldenRatio| := by
  have hne4 := gibonacci_norm_ne_zero x y hne
  have hS1 : 1 ≤ |(x : ℝ)| + |(y : ℝ)| := gibonacci_size_ge_one x y hne
  have hSpos : 0 < |(x : ℝ)| + |(y : ℝ)| := lt_of_lt_of_le zero_lt_one hS1
  have hsum := Real.goldenRatio_add_goldenConj
  have hprod := Real.goldenRatio_mul_goldenConj
  have hN : ((x : ℝ) + (y : ℝ) * Real.goldenRatio)
        * ((x : ℝ) + (y : ℝ) * Real.goldenConj)
      = ((x ^ 2 + x * y - y ^ 2 : ℤ) : ℝ) := by
    push_cast
    linear_combination ((y : ℝ) ^ 2) * hprod + ((x : ℝ) * (y : ℝ)) * hsum
  have hN1 : (1 : ℝ) ≤ |(((x ^ 2 + x * y - y ^ 2 : ℤ)) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne4
  have hψ1 : |Real.goldenConj| ≤ 1 := by
    have h1 := Real.neg_one_lt_goldenConj
    have h2 := Real.goldenConj_neg
    rw [abs_of_neg h2]
    linarith
  have hle : |(x : ℝ) + (y : ℝ) * Real.goldenConj|
      ≤ |(x : ℝ)| + |(y : ℝ)| := by
    have e : |(y : ℝ) * Real.goldenConj| ≤ |(y : ℝ)| := by
      rw [abs_mul]
      calc |(y : ℝ)| * |Real.goldenConj| ≤ |(y : ℝ)| * 1 :=
            mul_le_mul_of_nonneg_left hψ1 (abs_nonneg _)
        _ = |(y : ℝ)| := mul_one _
    calc |(x : ℝ) + (y : ℝ) * Real.goldenConj|
          ≤ |(x : ℝ)| + |(y : ℝ) * Real.goldenConj| := abs_add_le _ _
      _ ≤ |(x : ℝ)| + |(y : ℝ)| := add_le_add_right e _
  have hpos : 0 < |(x : ℝ) + (y : ℝ) * Real.goldenConj| := by
    by_contra hcon
    have hz0 : |(x : ℝ) + (y : ℝ) * Real.goldenConj| = 0 :=
      le_antisymm (not_lt.mp hcon) (abs_nonneg _)
    have h0 : (x : ℝ) + (y : ℝ) * Real.goldenConj = 0 := abs_eq_zero.mp hz0
    rw [h0, mul_zero] at hN
    have hNc : (((x ^ 2 + x * y - y ^ 2 : ℤ)) : ℝ) = 0 := hN.symm
    have hcon2 : x ^ 2 + x * y - y ^ 2 = 0 := by exact_mod_cast hNc
    exact hne4 hcon2
  have hmul : |(((x ^ 2 + x * y - y ^ 2 : ℤ)) : ℝ)|
      = |(x : ℝ) + (y : ℝ) * Real.goldenRatio|
        * |(x : ℝ) + (y : ℝ) * Real.goldenConj| := by
    rw [← hN, abs_mul]
  have h1 : (1 : ℝ) ≤ |(x : ℝ) + (y : ℝ) * Real.goldenRatio|
      * (|(x : ℝ)| + |(y : ℝ)|) := by
    calc (1 : ℝ) ≤ |(((x ^ 2 + x * y - y ^ 2 : ℤ)) : ℝ)| := hN1
      _ = |(x : ℝ) + (y : ℝ) * Real.goldenRatio|
          * |(x : ℝ) + (y : ℝ) * Real.goldenConj| := hmul
      _ ≤ |(x : ℝ) + (y : ℝ) * Real.goldenRatio| * (|(x : ℝ)| + |(y : ℝ)|) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  rw [div_le_iff₀ hSpos]
  exact h1

/-- A Gibonacci term split into a main term and a decaying error term. -/
private theorem gibonacci_key_identity (x y : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    Real.goldenRatio * (gibonacciNumber x y n : ℝ) =
    ((x : ℝ) + (y : ℝ) * Real.goldenRatio) * (Nat.fib n : ℝ)
      - (x : ℝ) * Real.goldenConj ^ (n - 1) := by
  have hP : (gibonacciNumber x y n : ℝ)
      = (Nat.fib (n - 1) : ℝ) * (x : ℝ) + (Nat.fib n : ℝ) * (y : ℝ) := by
    exact_mod_cast gibonacciNumber_eq_fib x y n hn
  have hi : n - 1 + 1 = n := by omega
  have he : (Nat.fib n : ℝ) - Real.goldenRatio * (Nat.fib (n - 1) : ℝ)
      = Real.goldenConj ^ (n - 1) := by
    have h := Real.fib_succ_sub_goldenRatio_mul_fib (n - 1)
    rw [hi] at h
    exact h
  linear_combination Real.goldenRatio * hP - (x : ℝ) * he

/-- Two is less than three times the logarithm of two. -/
private theorem two_lt_three_log_two : 2 < 3 * Real.log 2 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he2 : (Real.exp 1) ^ 2 < 8 := by
    have hpow : (Real.exp 1) ^ 2 < (2.7182818286 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ he (le_of_lt (Real.exp_pos 1)) two_ne_zero
    have hnum : (2.7182818286 : ℝ) ^ 2 < 8 := by norm_num
    exact lt_trans hpow hnum
  have hlog : Real.log ((Real.exp 1) ^ 2) = 2 := by
    rw [Real.log_pow, Real.log_exp]
    norm_num
  have hlt : Real.log ((Real.exp 1) ^ 2) < Real.log 8 :=
    Real.log_lt_log (pow_pos (Real.exp_pos 1) 2) he2
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    have e : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e, Real.log_pow]
    norm_num
  rw [hlog, h8] at hlt
  exact hlt

/-- Above the logarithmic threshold, twice the squared size is small. -/
private theorem threshold_pow_bound (x y : ℤ) (n : ℕ) (hne : (x, y) ≠ (0, 0))
    (hth : 3 * (Real.log (|(x : ℝ)| + |(y : ℝ)|) + 1) ≤ (n : ℝ)) :
    2 * (|(x : ℝ)| + |(y : ℝ)|) ^ 2 ≤ Real.goldenRatio ^ (2 * n - 3) := by
  have hS1 : 1 ≤ |(x : ℝ)| + |(y : ℝ)| := gibonacci_size_ge_one x y hne
  have hlogS : 0 ≤ Real.log (|(x : ℝ)| + |(y : ℝ)|) := Real.log_nonneg hS1
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by linarith [hth, hlogS]
  have hn3 : 3 ≤ n := by exact_mod_cast hn3R
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h32 : 2 < 3 * Real.log 2 := two_lt_three_log_two
  have hcast : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
    have h := Nat.sub_add_cancel hn3
    have hR : ((n - 3 : ℕ) : ℝ) + 3 = (n : ℝ) := by exact_mod_cast h
    linarith
  have hkey : 2 * Real.log (|(x : ℝ)| + |(y : ℝ)|)
      ≤ ((n - 3 : ℕ) : ℝ) * Real.log 2 := by
    rw [hcast]
    have hn' : 3 * Real.log (|(x : ℝ)| + |(y : ℝ)|) ≤ (n : ℝ) - 3 := by linarith
    have h1 : 3 * Real.log (|(x : ℝ)| + |(y : ℝ)|) * Real.log 2
        ≤ ((n : ℝ) - 3) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hn' (le_of_lt h2pos)
    have h2 : 2 * Real.log (|(x : ℝ)| + |(y : ℝ)|)
        ≤ 3 * Real.log (|(x : ℝ)| + |(y : ℝ)|) * Real.log 2 := by
      have h3 : (0 : ℝ)
          ≤ Real.log (|(x : ℝ)| + |(y : ℝ)|) * (3 * Real.log 2 - 2) :=
        mul_nonneg hlogS (by linarith)
      linarith
    linarith [h1, h2]
  have e1 : Real.log ((|(x : ℝ)| + |(y : ℝ)|) ^ 2)
      = 2 * Real.log (|(x : ℝ)| + |(y : ℝ)|) := by rw [Real.log_pow]; norm_num
  have e2 : Real.log ((2 : ℝ) ^ (n - 3)) = ((n - 3 : ℕ) : ℝ) * Real.log 2 :=
    Real.log_pow 2 (n - 3)
  have hS2 : (|(x : ℝ)| + |(y : ℝ)|) ^ 2 ≤ (2 : ℝ) ^ (n - 3) := by
    have hpos1 : (0 : ℝ) < (|(x : ℝ)| + |(y : ℝ)|) ^ 2 :=
      pow_pos (lt_of_lt_of_le zero_lt_one hS1) 2
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (n - 3) := pow_pos (by norm_num) _
    rw [← Real.log_le_log_iff hpos1 hpos2, e1, e2]
    exact hkey
  have hφ2 : (2 : ℝ) ≤ Real.goldenRatio ^ 2 := by
    have hsq := Real.goldenRatio_sq
    have h1 := Real.one_lt_goldenRatio
    linarith
  have hφ1 : (1 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.one_lt_goldenRatio
  have hexp : 2 * n - 3 = 2 * (n - 2) + 1 := by omega
  have hpow : (2 : ℝ) ^ (n - 2) ≤ Real.goldenRatio ^ (2 * n - 3) := by
    have e : Real.goldenRatio ^ (2 * (n - 2) + 1)
        = (Real.goldenRatio ^ 2) ^ (n - 2) * Real.goldenRatio := by
      rw [pow_add, pow_one, pow_mul]
    rw [hexp, e]
    calc (2 : ℝ) ^ (n - 2) ≤ (Real.goldenRatio ^ 2) ^ (n - 2) :=
          pow_le_pow_left₀ (by norm_num) hφ2 _
      _ ≤ (Real.goldenRatio ^ 2) ^ (n - 2) * Real.goldenRatio :=
          le_mul_of_one_le_right (pow_nonneg (sq_nonneg _) _) hφ1
  have hn2 : n - 2 = (n - 3) + 1 := by omega
  calc 2 * (|(x : ℝ)| + |(y : ℝ)|) ^ 2 ≤ 2 * (2 : ℝ) ^ (n - 3) :=
        mul_le_mul_of_nonneg_left hS2 (by norm_num)
    _ = (2 : ℝ) ^ (n - 2) := by rw [hn2, pow_add, pow_one]; ring
    _ ≤ Real.goldenRatio ^ (2 * n - 3) := hpow

/-- Exponential lower bound for Gibonacci numbers above the threshold. -/
private theorem gibonacci_lower_of_threshold (x y : ℤ) (n : ℕ) (hne : (x, y) ≠ (0, 0))
    (hth : 3 * (Real.log (|(x : ℝ)| + |(y : ℝ)|) + 1) ≤ (n : ℝ)) :
    (1 / 16) * Real.goldenRatio ^ (n + 1) / (|(x : ℝ)| + |(y : ℝ)|)
      ≤ |(gibonacciNumber x y n : ℝ)| := by
  have hS1 : 1 ≤ |(x : ℝ)| + |(y : ℝ)| := gibonacci_size_ge_one x y hne
  have hSpos : 0 < |(x : ℝ)| + |(y : ℝ)| := lt_of_lt_of_le zero_lt_one hS1
  have hSnn : (0 : ℝ) ≤ 1 / (|(x : ℝ)| + |(y : ℝ)|) :=
    div_nonneg zero_le_one (le_of_lt hSpos)
  have hφpos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hn3 : 3 ≤ n := by
    have hlogS := Real.log_nonneg hS1
    have hn3R : (3 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast hn3R
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hkey := gibonacci_key_identity x y n hn1
  have hF2 : Real.goldenRatio ^ (n - 2) ≤ (Nat.fib n : ℝ) := by
    have i : n - 2 + 2 = n := by omega
    have h := (fib_lower_two_step (n - 2)).1
    rw [i] at h
    exact h
  have hFnn : (0 : ℝ) ≤ (Nat.fib n : ℝ) := Nat.cast_nonneg _
  have htri : |(x : ℝ) + (y : ℝ) * Real.goldenRatio| * (Nat.fib n : ℝ)
      - |(x : ℝ)| * |Real.goldenConj| ^ (n - 1)
      ≤ Real.goldenRatio * |(gibonacciNumber x y n : ℝ)| := by
    have h := abs_sub_abs_le_abs_sub
      (((x : ℝ) + (y : ℝ) * Real.goldenRatio) * (Nat.fib n : ℝ))
      ((x : ℝ) * Real.goldenConj ^ (n - 1))
    rw [← hkey] at h
    simpa only [abs_mul, abs_of_nonneg (le_of_lt hφpos), abs_of_nonneg hFnn,
      abs_pow] using h
  have hψpow : |Real.goldenConj| ^ (n - 1)
      = 1 / Real.goldenRatio ^ (n - 1) := by
    have hp := Real.goldenRatio_mul_goldenConj
    have h1 : Real.goldenRatio * |Real.goldenConj| = 1 := by
      have h2 : |Real.goldenRatio * Real.goldenConj| = 1 := by
        rw [hp, abs_neg, abs_one]
      rwa [abs_mul, abs_of_nonneg (le_of_lt hφpos)] at h2
    have h2 : Real.goldenRatio ^ (n - 1) * |Real.goldenConj| ^ (n - 1) = 1 := by
      have h3 : (Real.goldenRatio * |Real.goldenConj|) ^ (n - 1) = 1 := by
        rw [h1, one_pow]
      rwa [mul_pow] at h3
    have hφne2 : Real.goldenRatio ^ (n - 1) ≠ 0 :=
      ne_of_gt (pow_pos hφpos _)
    rw [eq_div_iff hφne2, mul_comm]
    exact h2
  have hmain : (1 / (|(x : ℝ)| + |(y : ℝ)|)) * (Nat.fib n : ℝ)
      ≤ |(x : ℝ) + (y : ℝ) * Real.goldenRatio| * (Nat.fib n : ℝ) :=
    mul_le_mul_of_nonneg_right (gibonacci_coeff_lower x y hne) hFnn
  have h2S : 2 * (|(x : ℝ)| + |(y : ℝ)|) ^ 2
      ≤ (Nat.fib n : ℝ) * Real.goldenRatio ^ (n - 1) := by
    have h9 := threshold_pow_bound x y n hne hth
    have hFn : Real.goldenRatio ^ (n - 2) * Real.goldenRatio ^ (n - 1)
        ≤ (Nat.fib n : ℝ) * Real.goldenRatio ^ (n - 1) :=
      mul_le_mul_of_nonneg_right hF2 (pow_nonneg (le_of_lt hφpos) _)
    have hexp2 : Real.goldenRatio ^ (n - 2) * Real.goldenRatio ^ (n - 1)
        = Real.goldenRatio ^ (2 * n - 3) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← hexp2] at h9
    exact le_trans h9 hFn
  have herr1 : |(x : ℝ)| * |Real.goldenConj| ^ (n - 1)
      ≤ (|(x : ℝ)| + |(y : ℝ)|) * (1 / Real.goldenRatio ^ (n - 1)) := by
    have hxS : |(x : ℝ)| ≤ |(x : ℝ)| + |(y : ℝ)| :=
      le_add_of_nonneg_right (abs_nonneg _)
    rw [hψpow]
    exact mul_le_mul_of_nonneg_right hxS
      (div_nonneg zero_le_one (pow_nonneg (le_of_lt hφpos) _))
  have herr2 : (|(x : ℝ)| + |(y : ℝ)|) * (1 / Real.goldenRatio ^ (n - 1))
      ≤ ((1 / (|(x : ℝ)| + |(y : ℝ)|)) * (Nat.fib n : ℝ)) / 2 := by
    have h1pos : (0 : ℝ) < Real.goldenRatio ^ (n - 1) := pow_pos hφpos _
    have h2pos : (0 : ℝ) < (|(x : ℝ)| + |(y : ℝ)|) * 2 :=
      mul_pos hSpos (by norm_num)
    rw [mul_one_div, div_mul_eq_mul_div, one_mul, div_div,
      div_le_div_iff₀ h1pos h2pos]
    linarith [h2S]
  have herr : |(x : ℝ)| * |Real.goldenConj| ^ (n - 1)
      ≤ ((1 / (|(x : ℝ)| + |(y : ℝ)|)) * (Nat.fib n : ℝ)) / 2 :=
    le_trans herr1 herr2
  have hcomb : ((1 / (|(x : ℝ)| + |(y : ℝ)|)) * (Nat.fib n : ℝ)) / 2
      ≤ Real.goldenRatio * |(gibonacciNumber x y n : ℝ)| := by
    linarith [htri, hmain, herr]
  have hFbound : ((1 / (|(x : ℝ)| + |(y : ℝ)|))
        * Real.goldenRatio ^ (n - 2)) / 2
      ≤ ((1 / (|(x : ℝ)| + |(y : ℝ)|)) * (Nat.fib n : ℝ)) / 2 := by
    have h := mul_le_mul_of_nonneg_left hF2 hSnn
    linarith [h]
  have hcc : ((1 / (|(x : ℝ)| + |(y : ℝ)|)) * Real.goldenRatio ^ (n - 2)) / 2
      ≤ Real.goldenRatio * |(gibonacciNumber x y n : ℝ)| :=
    le_trans hFbound hcomb
  have hdiv : ((1 / (|(x : ℝ)| + |(y : ℝ)|)) * Real.goldenRatio ^ (n - 2))
      / (2 * Real.goldenRatio) ≤ |(gibonacciNumber x y n : ℝ)| := by
    have h2φ : (0 : ℝ) < 2 * Real.goldenRatio := mul_pos (by norm_num) hφpos
    rw [div_le_iff₀ h2φ]
    have h := (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).mp hcc
    linarith [h]
  have hφ4 : Real.goldenRatio ^ 4 ≤ 8 := by
    have h4 : Real.goldenRatio ^ 4 = 3 * Real.goldenRatio + 2 := by
      linear_combination
        (Real.goldenRatio ^ 2 + Real.goldenRatio + 2) * Real.goldenRatio_sq
    have h2 := Real.goldenRatio_lt_two
    linarith
  have hfinal : (1 / 16) * Real.goldenRatio ^ (n + 1)
      / (|(x : ℝ)| + |(y : ℝ)|)
      ≤ ((1 / (|(x : ℝ)| + |(y : ℝ)|)) * Real.goldenRatio ^ (n - 2))
        / (2 * Real.goldenRatio) := by
    have hde : Real.goldenRatio ^ (n + 1)
        = Real.goldenRatio ^ (n - 2) * Real.goldenRatio ^ 3 := by
      rw [← pow_add]
      congr 1
      omega
    have h2φ : (0 : ℝ) < 2 * Real.goldenRatio := mul_pos (by norm_num) hφpos
    have hrhs : ((1 / (|(x : ℝ)| + |(y : ℝ)|)) * Real.goldenRatio ^ (n - 2))
        / (2 * Real.goldenRatio)
        = Real.goldenRatio ^ (n - 2)
          / ((|(x : ℝ)| + |(y : ℝ)|) * (2 * Real.goldenRatio)) := by
      rw [div_mul_eq_mul_div, one_mul, div_div]
    rw [hrhs, hde, div_le_div_iff₀ hSpos (mul_pos hSpos h2φ)]
    have hprod : (0 : ℝ) ≤ (Real.goldenRatio ^ (n - 2)
        * (|(x : ℝ)| + |(y : ℝ)|)) * (8 - Real.goldenRatio ^ 4) :=
      mul_nonneg
        (mul_nonneg (pow_nonneg (le_of_lt hφpos) _) (le_of_lt hSpos))
        (by linarith)
    linarith [hprod]
  exact le_trans hfinal hdiv

/-- **Growth bounds for Gibonacci and generalized Tribonacci sequences.** Let $\varphi$ be the
golden ratio. For integers $x, y$ let $(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$
and $P_1 = y$, and for integers $a, b, c$ let $(Q_n)_{n \ge 0}$ be the generalized Tribonacci
sequence with $Q_0 = a$, $Q_1 = b$ and $Q_2 = c$. Then (i) for all integers $x, y$ and every
$n \ge 0$, $|P_n| \le (|x| + |y|)\,\varphi^n$; (ii) there are real constants $c_0 > 0$ and
$c_1 > 0$ such that for all integers $x, y$ with $(x, y) \ne (0, 0)$ and every $n \ge 0$ with
$c_1 (\log(|x| + |y|) + 1) \le n$, one has $c_0\,\varphi^{n+1} / (|x| + |y|) \le |P_n|$; and
(iii) for every real $\tau$ with $\tau^3 = \tau^2 + \tau + 1$, all integers $a, b, c$ and every
$n \ge 0$, $|Q_n| \le (|a| + |b| + |c|)\,\tau^n$.

The paper indexes both sequences from $1$, so its $n$-th terms are $P_{n-1}$ and $Q_{n-1}$ here.
It prints (ii) with the threshold "n large enough depending on $|x| + |y|$"; the logarithmic
threshold is the one the paper uses in its proof of Theorem 2.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 1
(`integers-2026-A122-lem-1`), with the threshold as used in the proof of Theorem 2. -/
public theorem gibonacci_generalizedTribonacci_growth_bounds :
    (∀ (x y : ℤ) (n : ℕ),
      |(gibonacciNumber x y n : ℝ)| ≤ (|(x : ℝ)| + |(y : ℝ)|) * Real.goldenRatio ^ n) ∧
    (∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∀ x y : ℤ, (x, y) ≠ (0, 0) →
      ∀ n : ℕ, c₁ * (Real.log (|(x : ℝ)| + |(y : ℝ)|) + 1) ≤ (n : ℝ) →
        c₀ * Real.goldenRatio ^ (n + 1) / (|(x : ℝ)| + |(y : ℝ)|)
          ≤ |(gibonacciNumber x y n : ℝ)|) ∧
    (∀ τ : ℝ, τ ^ 3 = τ ^ 2 + τ + 1 → ∀ (a b c : ℤ) (n : ℕ),
      |(generalizedTribonacci a b c n : ℝ)| ≤ (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ n)
    := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y n
    exact (gibonacci_abs_le_two_step x y n).1
  · refine ⟨1 / 16, 3, by norm_num, by norm_num, ?_⟩
    intro x y hne n hth
    exact gibonacci_lower_of_threshold x y n hne hth
  · intro τ hτ a b c n
    exact (generalizedTribonacci_abs_le_three_step τ hτ a b c n).1

end MetaMathlibExt
