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

/-- **Sum of products of Tribonacci terms two apart.** Let $T \colon \mathbb{Z} \to \mathbb{Z}$
satisfy $T(m+3) = T(m+2) + T(m+1) + T(m)$ for every integer $m$. Then for every
natural number $n$,
$$4 \sum_{k=1}^{n} T(k)\,T(k-2) = \bigl(T(n+1) - T(n-1)\bigr)^2 - \bigl(T(1) - T(-1)\bigr)^2.$$

Source: Karol Gryszka, "A Simple Proof of the Formula for the Sum
of Tribonacci and Tetranacci Numbers Squared", Lemma 1. -/
theorem_wanted four_mul_sum_tribonacci_mul_sub_two
    (T : ℤ → ℤ)
    (hT : ∀ n : ℤ, T (n + 3) = T (n + 2) + T (n + 1) + T n)
    (n : ℕ) :
    4 * (∑ k ∈ Finset.Icc 1 n, T k * T ((k : ℤ) - 2)) =
      (T ((n : ℤ) + 1) - T ((n : ℤ) - 1)) ^ 2 -
        (T 1 - T (-1)) ^ 2

/-- **Sum of squares of a Tribonacci sequence.** Let $T \colon \mathbb{Z} \to \mathbb{Z}$ satisfy
$T(m+3) = T(m+2) + T(m+1) + T(m)$ for every integer $m$. Then for every natural number $n$,
$$4 \sum_{k=1}^{n} T(k)^2 = 4\,T(n)\,T(n+1) - 4\,T(0)\,T(1) -
\bigl(T(n+1) - T(n-1)\bigr)^2 + \bigl(T(1) - T(-1)\bigr)^2.$$

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

/-- **Sum of products of Tetranacci terms two and three apart.** Let
$Q \colon \mathbb{Z} \to \mathbb{Z}$ satisfy $Q(m+4) = Q(m+3) + Q(m+2) + Q(m+1) + Q(m)$ for every
integer $m$. Then for every natural number $n$,
$$3 \sum_{k=1}^{n} Q(k)\bigl(Q(k-2) + Q(k-3)\bigr) = \bigl(Q(n+1) - Q(n-1)\bigr)^2 -
\bigl(Q(1) - Q(-1)\bigr)^2 - Q(n-2)\bigl(Q(n) + Q(n-3)\bigr) + Q(-2)\bigl(Q(0) + Q(-3)\bigr).$$

The boundary terms contain $Q(n) + Q(n-3)$ and $Q(0) + Q(-3)$, with the sign given by the
paper's telescoping calculation.

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

/-- **Sum of squares of a Tetranacci sequence.** Let $Q \colon \mathbb{Z} \to \mathbb{Z}$ satisfy
$Q(m+4) = Q(m+3) + Q(m+2) + Q(m+1) + Q(m)$ for every integer $m$. Then for every natural
number $n$,
$$3 \sum_{k=1}^{n} Q(k)^2 = 3\,Q(n)\,Q(n+1) - 3\,Q(0)\,Q(1) - \bigl(Q(n+1) - Q(n-1)\bigr)^2 +
\bigl(Q(1) - Q(-1)\bigr)^2 + Q(n-2)\bigl(Q(n) + Q(n-3)\bigr) - Q(-2)\bigl(Q(0) + Q(-3)\bigr).$$

Inside the boundary terms the sums $Q(n) + Q(n-3)$ and $Q(0) + Q(-3)$ carry a plus sign, as in
Gryszka's Lemma 2; this sign is the one forced by the paper's telescoping calculation.

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
