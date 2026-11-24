/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Sum of products of Tribonacci terms two apart

For a two-sided Tribonacci sequence, four times the sum of the products of terms two apart
telescopes to the difference of the endpoint squares.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted

/-- **Sum of products of Tribonacci terms two apart.** Let $T \colon \mathbb{Z} \to \mathbb{Z}$
satisfy $T(m+3) = T(m+2) + T(m+1) + T(m)$ for every integer $m$. Then for every
natural number $n$,
$$4 \sum_{k=1}^{n} T(k)\,T(k-2) = \bigl(T(n+1) - T(n-1)\bigr)^2 - \bigl(T(1) - T(-1)\bigr)^2.$$

Source: Karol Gryszka, "A Simple Proof of the Formula for the Sum
of Tribonacci and Tetranacci Numbers Squared", Lemma 1. -/
theorem four_mul_sum_tribonacci_mul_sub_two
    (T : ℤ → ℤ)
    (hT : ∀ n : ℤ, T (n + 3) = T (n + 2) + T (n + 1) + T n)
    (n : ℕ) :
    4 * (∑ k ∈ Finset.Icc 1 n, T k * T ((k : ℤ) - 2)) =
      (T ((n : ℤ) + 1) - T ((n : ℤ) - 1)) ^ 2 -
        (T 1 - T (-1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), mul_add, ih, Nat.cast_succ]
    -- The recurrence turns the new difference into T(n+1) + T(n-1).
    have h := hT ((n : ℤ) - 1)
    simp only [sub_eq_add_neg, add_assoc, Int.reduceNeg, Int.reduceAdd, add_zero] at h ⊢
    rw [h]
    ring

end MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted
