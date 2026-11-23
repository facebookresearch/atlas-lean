/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination

/-! # A Fibonacci identity for super FiboCatalan numbers -/

public section

namespace MathlibExt.NumberTheory.SuperFibocatalanWanted

/-- **Fibonacci identity $F_{2n} F_{n+2} - F_{2n+2} F_n = (-1)^n F_n$.** For every natural
number $n$, the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$, $F_{k+2} = F_{k+1} + F_k$) satisfy
$F_{2n} F_{n+2} - F_{2n+2} F_n = (-1)^n F_n$.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Lemma 6. -/
theorem fib_mul_sub_mul (n : ℕ) :
    (Nat.fib (2 * n) : ℤ) * (Nat.fib (n + 2) : ℤ) -
        (Nat.fib (2 * n + 2) : ℤ) * (Nat.fib n : ℤ) =
      (-1) ^ n * (Nat.fib n : ℤ) := by
  -- Shifting both pairs of consecutive indices by one negates their determinant.
  have shift (k : ℕ) :
      (Nat.fib (n + k) : ℤ) * Nat.fib (k + 1) - (Nat.fib (n + k + 1) : ℤ) * Nat.fib k =
        (-1) ^ k * (Nat.fib n : ℤ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ n k, pow_succ, Nat.fib_add_two (n := k), Nat.fib_add_two (n := n + k)]
      push_cast
      linear_combination -ih
  rw [two_mul, Nat.fib_add_two (n := n), Nat.fib_add_two (n := n + n)]
  push_cast
  linear_combination shift n

end MathlibExt.NumberTheory.SuperFibocatalanWanted
