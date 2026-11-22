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
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted

/-- **Sums of two positive triangular numbers.** A natural number $n$ is a sum of two positive
triangular numbers if there are natural numbers $a \ge 1$ and $b \ge 1$ with
$2n = a(a+1) + b(b+1)$, that is, $n = \frac{a(a+1)}{2} + \frac{b(b+1)}{2}$. -/
def IsSumTwoPositiveTriangular (n : ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 2 * n = a * (a + 1) + b * (b + 1)

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

/-- **Park's Lemma 2: the identity up to 21 when the value at 2 is nonzero.** Let $f$ be a
multiplicative arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$
whenever $a$ and $b$ are both sums of two positive triangular numbers. If $f(2) \neq 0$, then
$f(n) = n$ for every natural number $n \le 21$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 2. -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_eq_id_le_21
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 ≠ 0) :
    ∀ n : ℕ, n ≤ 21 → f n = (n : ℂ)

/-- **Park's Lemma 3: vanishing from 4 to 21 when the value at 2 is zero and at 3 is not.** Let
$f$ be a multiplicative arithmetic function with values in $\mathbb{C}$ such that
$f(a + b) = f(a) + f(b)$ whenever $a$ and $b$ are both sums of two positive triangular numbers.
If $f(2) = 0$ and $f(3) \neq 0$, then $f(n) = 0$ for every natural number $n$ with
$4 \le n \le 21$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 3. -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_zero_of_three_ne_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) (hf3 : f 3 ≠ 0) :
    ∀ n : ℕ, 4 ≤ n → n ≤ 21 → f n = 0

/-- **Park's Lemma 4: vanishing from 2 to 21 except at 5.** Let $f$ be a multiplicative
arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$ whenever
$a$ and $b$ are both sums of two positive triangular numbers. If $f(2) = 0$ and $f(5) \neq 0$,
then $f(n) = 0$ for every natural number $n$ with $2 \le n \le 21$ and $n \neq 5$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 4. -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_zero_of_five_ne_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) (hf5 : f 5 ≠ 0) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 21 → n ≠ 5 → f n = 0

/-- **Park's Lemma 5: vanishing from 2 to 21 when the values at 2, 3 and 5 are zero.** Let $f$
be a multiplicative arithmetic function with values in $\mathbb{C}$ such that
$f(a + b) = f(a) + f(b)$ whenever $a$ and $b$ are both sums of two positive triangular numbers.
If $f(2) = f(3) = f(5) = 0$, then $f(n) = 0$ for every natural number $n$ with $2 \le n \le 21$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 5. -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_zero_of_all_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) (hf3 : f 3 = 0) (hf5 : f 5 = 0) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 21 → f n = 0

end MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted
