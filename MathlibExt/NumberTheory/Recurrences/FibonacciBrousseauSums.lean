/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSums
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Recurrences.Internal.BrousseauSum
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula

/-!
# Brousseau sums of Fibonacci numbers

We prove the endpoint formula for power-weighted Fibonacci sums along odd steps.
-/

namespace MetaMathlibExt

open Finset

namespace fibonacci_brousseau_sum_mul_odd

open scoped goldenRatio in
private lemma fib_step (m : ℕ) (hm : Odd m) (n : ℕ) :
    (Nat.fib (m * (n + 2)) : ℚ) =
      (lucasNumber m : ℚ) * Nat.fib (m * (n + 1)) + Nat.fib (m * n) := by
  have hne : φ ≠ ψ := ne_of_gt (Real.goldenConj_neg.trans Real.goldenRatio_pos)
  have hL : (lucasNumber m : ℝ) = φ ^ m + ψ ^ m := by
    have h := ((lucas_binet_formulas_of_field fibonacciLucasParams φ ψ
      (by simp [fibonacciLucasParams]) (by simp [fibonacciLucasParams])).1 hne m).2
    simpa [lucasV_fibonacciLucasParams] using h
  have hprod : φ ^ m * ψ ^ m = -1 := by
    rw [← mul_pow, Real.goldenRatio_mul_goldenConj, hm.neg_one_pow]
  have h : (Nat.fib (m * (n + 2)) : ℝ) =
      (lucasNumber m : ℝ) * Nat.fib (m * (n + 1)) + Nat.fib (m * n) := by
    simp only [hL, Real.coe_fib_eq, pow_mul, pow_add, pow_one]
    have hsqrt : (√5 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
    linear_combination ((ψ ^ m) ^ n - (φ ^ m) ^ n) * hprod
  have hnat : Nat.fib (m * (n + 2)) =
      lucasNumber m * Nat.fib (m * (n + 1)) + Nat.fib (m * n) := by exact_mod_cast h
  exact_mod_cast hnat

private lemma lucasNumber_pos (m : ℕ) : 0 < lucasNumber m := by
  induction m using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more m _ ih => exact Nat.add_pos_left ih _

end fibonacci_brousseau_sum_mul_odd

/-- **Brousseau sums of Fibonacci numbers along an odd step.** Let $F_n$ be the Fibonacci
numbers, $L_n$ the Lucas numbers and $C_k^{(p)}$ the coefficient polynomials. For every odd
natural number $m$ and all $n, p \ge 0$,
$$
L_m \sum_{i=1}^{n} i^p F_{mi} = C_{L_m}^{(p)}(n) F_{m(n+1)} + C_{L_m}^{(p)}(n+1) F_{mn} -
C_{L_m}^{(p)}(0) F_m.
$$

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Corollary 9 (`jis-2024-24.6.4-cor-9`). -/
public theorem fibonacci_brousseau_sum_mul_odd (m : ℕ) (hm : Odd m) (n p : ℕ) :
    (lucasNumber m : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * Nat.fib (m * i) =
      brousseauCoeff (lucasNumber m) p n * Nat.fib (m * (n + 1)) +
        brousseauCoeff (lucasNumber m) p (n + 1) * Nat.fib (m * n) -
        brousseauCoeff (lucasNumber m) p 0 * Nat.fib m := by
  open fibonacci_brousseau_sum_mul_odd in
  let k : ℚ := lucasNumber m
  have hk : k ≠ 0 := by
    change (lucasNumber m : ℚ) ≠ 0
    exact_mod_cast (lucasNumber_pos m).ne'
  let F (i : ℕ) : ℚ := Nat.fib (m * i)
  let C := brousseauCoeff k p
  change k * ∑ i ∈ Icc 1 n, (i : ℚ) ^ p * F i =
    C n * F (n + 1) + C (n + 1) * F n - C 0 * Nat.fib m
  induction n with
  | zero => simp [F]
  | succ n ih =>
    -- The new summand is the difference between the two successive endpoint expressions.
    rw [sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), mul_add, ih]
    have hC : k * C ((n : ℚ) + 1) + C ((n : ℚ) + 1 + 1) - C n =
        k * ((n : ℚ) + 1) ^ p := by
      simpa only [C, add_sub_cancel_right] using BrousseauSum.coeff_shift k hk p ((n : ℚ) + 1)
    have hF : F (n + 2) = k * F (n + 1) + F n := fib_step m hm n
    simp only [Nat.cast_add_one]
    rw [hF]
    linear_combination -F (n + 1) * hC

end MetaMathlibExt
