/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GibonacciCompositionSum
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A companion composition sum for shifted Fibonacci numbers

We specialize the Gibonacci composition sum at the negative root with shift three.
-/

open scoped BigOperators

namespace MetaMathlibExt

/-- **Companion composition-sum formula for $F_{n+3}$.** Let $F_k$ be the Fibonacci numbers. For
every $n \ge 1$,
$$\frac{5}{9} F_{n+3} = \left(-\frac{1}{3}\right)^n \sum \prod_{i=1}^{r} (5 c_i - 10),$$
where the sum runs over all compositions $(c_1, \dots, c_r)$ of $n$ (tuples of positive integers
with $c_1 + \dots + c_r = n$).

This is the companion of identity (13) of the source: identity (30) with $m = 3$ and the square
root $\lambda = -1$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 5 (`integers-2025-A97-cor-5`). -/
public theorem fib_add_three_companion_composition_sum (n : ℕ) (hn : 1 ≤ n) :
    5 / 9 * (Nat.fib (n + 3) : ℚ) =
      (-1 / 3) ^ n * ∑ c : Composition n, ∏ i : Fin c.length, (5 * (c.blocksFun i : ℚ) - 10) := by
  have h := gibonacci_add_eq_composition_sum 0 1 (by decide) (by decide)
    (Or.inr (by decide)) 3 (by decide) (-1) (by norm_num) n hn
  rw [gibonacci_zero_one_eq_fib, Int.cast_natCast] at h
  -- At this root the two normalizing constants are B = 1 and A = 5.
  have hspecialized : (Nat.fib (n + 3) : ℂ) =
      5 ^ (n - 1) / (3 : ℂ) ^ ((n : ℤ) - 2) *
        ∑ c : Composition n, (-1 / 5 : ℂ) ^ (n - c.length) *
          ∏ i : Fin c.length, (2 - (c.blocksFun i : ℂ)) := by
    convert h using 1
    norm_num [gibonacciNumber, sub_eq_add_neg, add_comm]
  have hweight (a : ℂ) : 2 - a = (-1 / 5) * (5 * a - 10) := by ring
  have hsum :
      (∑ c : Composition n, (-1 / 5 : ℂ) ^ (n - c.length) *
        ∏ i : Fin c.length, (2 - (c.blocksFun i : ℂ))) =
      (-1 / 5 : ℂ) ^ n * ∑ c : Composition n,
        ∏ i : Fin c.length, (5 * (c.blocksFun i : ℂ) - 10) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp_rw [hweight]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel c.length_le]
  -- Keep the exponent integral: in particular, at n = 1 this uses 3⁻¹, not 3⁰.
  have hscale : (5 / 9 : ℂ) * (5 ^ (n - 1) / 3 ^ ((n : ℤ) - 2) * (-1 / 5) ^ n) =
      (-1 / 3) ^ n := by
    rw [zpow_sub₀ (by norm_num : (3 : ℂ) ≠ 0), zpow_natCast, zpow_ofNat,
      show (-1 / 3 : ℂ) = 5 / 3 * (-1 / 5) by norm_num, mul_pow, div_pow (5 : ℂ) 3]
    have hfive : (5 : ℂ) ^ (n - 1) * 5 = 5 ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [← hfive]
    field_simp
    ring
  rw [hsum, ← mul_assoc] at hspecialized
  have hcomplex : 5 / 9 * (Nat.fib (n + 3) : ℂ) =
      (-1 / 3) ^ n * ∑ c : Composition n, ∏ i : Fin c.length, (5 * (c.blocksFun i : ℂ) - 10) := by
    rw [hspecialized, ← mul_assoc, hscale]
  apply (show Function.Injective (Rat.castHom ℂ) from Rat.cast_injective)
  simpa only [map_mul, map_div₀, map_pow, map_sum, map_prod, map_sub, map_neg, map_ofNat,
    map_natCast, map_one] using hcomplex

end MetaMathlibExt
