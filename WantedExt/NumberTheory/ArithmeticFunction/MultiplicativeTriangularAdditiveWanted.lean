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

/-- A natural number is a sum of two positive triangular numbers. -/
def IsSumTwoPositiveTriangular (n : ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 2 * n = a * (a + 1) + b * (b + 1)

/-- Park's Theorem 1: a multiplicative function additive on pairs from
`T₂` is either the identity or vanishes outside `{1, 3, 5}` with
`f 3 * f 5 = 0`.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Theorem 1 (TeX label `thm1`). -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_classification
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b) :
    (∀ n : ℕ, f n = (n : ℂ)) ∨
      ((∀ n : ℕ, n ≠ 1 ∧ n ≠ 3 ∧ n ≠ 5 → f n = 0) ∧ f 3 * f 5 = 0)

/-- Park's Lemma 2: under the same hypotheses, if `f 2 ≠ 0`, then
`f n = n` for every `n ≤ 21`.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 2. -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_eq_id_le_21
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 ≠ 0) :
    ∀ n : ℕ, n ≤ 21 → f n = (n : ℂ)

/-- Park's Lemma 3: under the same hypotheses, if `f 2 = 0` and
`f 3 ≠ 0`, then `f n = 0` for `4 ≤ n ≤ 21`.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 3. -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_zero_of_three_ne_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) (hf3 : f 3 ≠ 0) :
    ∀ n : ℕ, 4 ≤ n → n ≤ 21 → f n = 0

/-- Park's Lemma 4: under the same hypotheses, if `f 2 = 0` and
`f 5 ≠ 0`, then `f n = 0` for `2 ≤ n ≤ 21` with `n ≠ 5`.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 4. -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_zero_of_five_ne_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) (hf5 : f 5 ≠ 0) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 21 → n ≠ 5 → f n = 0

/-- Park's Lemma 5: under the same hypotheses, if
`f 2 = f 3 = f 5 = 0`, then `f n = 0` for `2 ≤ n ≤ 21`.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 5. -/
theorem_wanted multiplicative_additive_on_sum_two_triangular_zero_of_all_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) (hf3 : f 3 = 0) (hf5 : f 5 = 0) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 21 → f n = 0

end MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted
