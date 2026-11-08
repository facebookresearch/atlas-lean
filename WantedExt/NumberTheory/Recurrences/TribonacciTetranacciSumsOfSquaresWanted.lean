/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of squares of Tribonacci and Tetranacci numbers

Statements from Karol Gryszka, "A Simple Proof of the Formula for
the Sum of Tribonacci and Tetranacci Numbers Squared", *INTEGERS* 25
(2025), Article A110
(<https://math.colgate.edu/~integers/z110/z110.pdf>).

The sequences have arbitrary initial conditions and are extended to
all integer indices by their recurrences.  The formulas are cleared
of denominators.  In the Tetranacci boundary term the sign is
`Q₀ + Q₋₃`, as forced by the paper's telescoping calculation; the
extracted statement's displayed minus sign is not correct for
arbitrary initial conditions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted

/-- Gryszka's Lemma 1, cleared of the denominator `4`: for an
integer-indexed Tribonacci recurrence, four times
`∑ k ∈ [1,n], T k * T (k - 2)` is the displayed difference of
squares.

Source: Karol Gryszka, "A Simple Proof of the Formula for the Sum
of Tribonacci and Tetranacci Numbers Squared", Lemma 1. -/
theorem_wanted four_mul_sum_tribonacci_mul_sub_two
    (T : ℤ → ℤ)
    (hT : ∀ n : ℤ, T (n + 3) = T (n + 2) + T (n + 1) + T n)
    (n : ℕ) :
    4 * (∑ k ∈ Finset.Icc 1 n, T k * T ((k : ℤ) - 2)) =
      (T ((n : ℤ) + 1) - T ((n : ℤ) - 1)) ^ 2 -
        (T 1 - T (-1)) ^ 2

/-- Gryszka's Theorem 1, cleared of the denominator `4`: the sum of
squares of an arbitrary integer-indexed Tribonacci sequence.

Source: Karol Gryszka, "A Simple Proof of the Formula for the Sum
of Tribonacci and Tetranacci Numbers Squared", Theorem 1. -/
theorem_wanted four_mul_sum_tribonacci_sq
    (T : ℤ → ℤ)
    (hT : ∀ n : ℤ, T (n + 3) = T (n + 2) + T (n + 1) + T n)
    (n : ℕ) :
    4 * (∑ k ∈ Finset.Icc 1 n, (T k) ^ 2) =
      4 * T n * T ((n : ℤ) + 1) - 4 * T 0 * T 1 -
        (T ((n : ℤ) + 1) - T ((n : ℤ) - 1)) ^ 2 +
        (T 1 - T (-1)) ^ 2

/-- Gryszka's Lemma 2, cleared of the denominator `3`, with the
boundary sign given by the paper's telescoping calculation:
three times `∑ k ∈ [1,n], Q k * (Q (k - 2) + Q (k - 3))` is the
displayed expression.

Source: Karol Gryszka, "A Simple Proof of the Formula for the Sum
of Tribonacci and Tetranacci Numbers Squared", Lemma 2. -/
theorem_wanted three_mul_sum_tetranacci_mul_sub_two_add_sub_three
    (Q : ℤ → ℤ)
    (hQ : ∀ n : ℤ, Q (n + 4) =
      Q (n + 3) + Q (n + 2) + Q (n + 1) + Q n)
    (n : ℕ) :
    3 * (∑ k ∈ Finset.Icc 1 n,
      Q k * (Q ((k : ℤ) - 2) + Q ((k : ℤ) - 3))) =
      (Q ((n : ℤ) + 1) - Q ((n : ℤ) - 1)) ^ 2 -
        (Q 1 - Q (-1)) ^ 2 -
        Q ((n : ℤ) - 2) * (Q n + Q ((n : ℤ) - 3)) +
        Q (-2) * (Q 0 + Q (-3))

/-- Gryszka's Theorem 2, cleared of the denominator `3`: the sum of
squares of an arbitrary integer-indexed Tetranacci sequence, with
the same boundary sign as in Lemma 2.

Source: Karol Gryszka, "A Simple Proof of the Formula for the Sum
of Tribonacci and Tetranacci Numbers Squared", Theorem 2. -/
theorem_wanted three_mul_sum_tetranacci_sq
    (Q : ℤ → ℤ)
    (hQ : ∀ n : ℤ, Q (n + 4) =
      Q (n + 3) + Q (n + 2) + Q (n + 1) + Q n)
    (n : ℕ) :
    3 * (∑ k ∈ Finset.Icc 1 n, (Q k) ^ 2) =
      3 * Q n * Q ((n : ℤ) + 1) - 3 * Q 0 * Q 1 -
        (Q ((n : ℤ) + 1) - Q ((n : ℤ) - 1)) ^ 2 +
        (Q 1 - Q (-1)) ^ 2 +
        Q ((n : ℤ) - 2) * (Q n + Q ((n : ℤ) - 3)) -
        Q (-2) * (Q 0 + Q (-3))

end MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted
