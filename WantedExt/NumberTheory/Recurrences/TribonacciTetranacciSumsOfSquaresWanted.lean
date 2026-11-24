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

The square-sum formulas are proved in the imported modules
`MathlibExt.NumberTheory.Recurrences.TribonacciSumOfSquares` and
`MathlibExt.NumberTheory.Recurrences.TetranacciSumOfSquares`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.Recurrences.TetranacciSumOfProducts
public import MathlibExt.NumberTheory.Recurrences.TetranacciSumOfSquares
public import MathlibExt.NumberTheory.Recurrences.TribonacciSumOfSquares

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

end MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted
