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
# Sum of squares of a Tribonacci sequence

Let `T : ℤ → ℤ` satisfy the Tribonacci recurrence `T (m + 3) = T (m + 2) + T (m + 1) + T m` for
every integer `m`. The initial values are arbitrary, and the terms of negative index are those the
recurrence gives when run backwards. `four_mul_sum_tribonacci_sq` evaluates the sum of the squares
of `T 1, …, T n`, cleared of the denominator `4`: `4 * ∑ k ∈ Finset.Icc 1 n, T k ^ 2` equals
`4 * T n * T (n + 1) - 4 * T 0 * T 1 - (T (n + 1) - T (n - 1)) ^ 2 + (T 1 - T (-1)) ^ 2`.

## Proof outline

Induction on `n`; for `n = 0` both sides vanish. Write `a = T (n - 1)`, `b = T n` and
`c = T (n + 1)`. The recurrence at `n - 1` gives `T (n + 2) = c + b + a`, so
`T (n + 2) - T n = c + a`, and from `n` to `n + 1` the right-hand side grows by
`4 * c * (c + b + a) - 4 * b * c - (c + a) ^ 2 + (c - a) ^ 2 = 4 * c ^ 2`, the new term on the left.

## Implementation notes

`four_mul_sum_tribonacci_sq` keeps the full name, the statement and the docstring it had as a
wanted theorem in `WantedExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted`, so
its namespace reads `TribonacciTetranacciSumsOfSquaresWanted`.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted

/-- **Sum of squares of a Tribonacci sequence.** Let $T \colon \mathbb{Z} \to \mathbb{Z}$ satisfy
$T(m+3) = T(m+2) + T(m+1) + T(m)$ for every integer $m$. Then for every natural number $n$,
$$4 \sum_{k=1}^{n} T(k)^2 = 4\,T(n)\,T(n+1) - 4\,T(0)\,T(1) -
\bigl(T(n+1) - T(n-1)\bigr)^2 + \bigl(T(1) - T(-1)\bigr)^2.$$

Source: Karol Gryszka, "A Simple Proof of the Formula for the Sum
of Tribonacci and Tetranacci Numbers Squared", Theorem 1. -/
theorem four_mul_sum_tribonacci_sq
    (T : ℤ → ℤ)
    (hT : ∀ n : ℤ, T (n + 3) = T (n + 2) + T (n + 1) + T n)
    (n : ℕ) :
    4 * (∑ k ∈ Finset.Icc 1 n, (T k) ^ 2) =
      4 * T n * T ((n : ℤ) + 1) - 4 * T 0 * T 1 -
        (T ((n : ℤ) + 1) - T ((n : ℤ) - 1)) ^ 2 +
        (T 1 - T (-1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- The recurrence at `n - 1`: `T (n + 2) = T (n + 1) + T n + T (n - 1)`.
    have h := hT ((n : ℤ) - 1)
    rw [show (n : ℤ) - 1 + 3 = n + 1 + 1 by ring, show (n : ℤ) - 1 + 2 = n + 1 by ring,
      sub_add_cancel] at h
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), mul_add, ih, Nat.cast_succ,
      add_sub_cancel_right, h]
    ring

end MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted
