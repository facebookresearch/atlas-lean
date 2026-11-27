/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multiplicative functions additive on sums of two triangular numbers

Statements from Poo-Sung Park, "Multiplicative Functions Additive on
the Sums of Two Positive Triangular Numbers", *Journal of Integer
Sequences* 28 (2025), Article 25.4.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Park/park10.html>).

The paper's `T₂` is the set of sums of two positive triangular numbers.
Here that condition is written without division as
`2 * n = a * (a + 1) + b * (b + 1)` with `1 ≤ a` and `1 ≤ b`.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditive

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted

/-- **Park's theorem on multiplicative functions additive on sums of two triangular numbers.**
Let $f$ be a multiplicative arithmetic function with values in $\mathbb{C}$ (so $f$ is defined on
the natural numbers with $f(0) = 0$) such that $f(a + b) = f(a) + f(b)$ whenever $a$ and $b$ are
both sums of two positive triangular numbers. Then either $f(n) = n$ for every natural number
$n$, or $f(n) = 0$ for every natural number $n \notin \{1, 3, 5\}$ and $f(3) f(5) = 0$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Theorem 1 (TeX label `thm1`). -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_classification
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b) :
    (∀ n : ℕ, f n = (n : ℂ)) ∨
      ((∀ n : ℕ, n ≠ 1 ∧ n ≠ 3 ∧ n ≠ 5 → f n = 0) ∧ f 3 * f 5 = 0)

end MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted
