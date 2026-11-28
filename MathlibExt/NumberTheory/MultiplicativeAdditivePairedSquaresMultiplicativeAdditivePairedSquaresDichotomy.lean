/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresRigidity

/-!
# Dichotomy for multiplicative functions additive on paired squares

For `k ≥ 5`, a complex-valued multiplicative function that is `k`-additive on sums of two
positive squares either is the identity on all positive integers or vanishes on every integer
that is a sum of two positive squares, of the form `2k + t` with
`t ∈ {0, 3, 6, 8, 9, 11, 12}`, or at least `2k + 14`. This follows from the rigidity theorem:
any nonzero value in the vanishing range forces the identity.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 2 (`integers-2026-A121-thm-2`).
-/

namespace MetaMathlibExt

/-- **Dichotomy for multiplicative functions additive on paired squares.** Let $k \ge 5$ and
let $f$ be a complex-valued multiplicative function such that
$$f\Big(\sum_{j=1}^{k} (x_j^2 + y_j^2)\Big) = \sum_{j=1}^{k} f(x_j^2 + y_j^2)$$
for all positive integers $x_1, \dots, x_k, y_1, \dots, y_k$. Then either $f(n) = n$ for every
positive integer $n$, or $f(n) = 0$ for every positive integer $n$ that is of the form $a^2 + b^2$
with integers $a, b \ge 1$, or of the form $2k + t$ with $t \in \{0, 3, 6, 8, 9, 11, 12\}$, or
satisfies $n \ge 2k + 14$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 2 (`integers-2026-A121-thm-2`). -/
public theorem multiplicative_additive_paired_squares_dichotomy
    (k : ℕ) (hk : 5 ≤ k) (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin k → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2)) :
    (∀ n : ℕ, 0 < n → f n = n) ∨
      ∀ n : ℕ, ((∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a ^ 2 + b ^ 2) ∨
          (∃ t ∈ ({0, 3, 6, 8, 9, 11, 12} : Finset ℕ), n = 2 * k + t) ∨ 2 * k + 14 ≤ n) →
        f n = 0 := by
  by_cases h : ∀ n : ℕ, 0 < n → f n = n
  · exact Or.inl h
  · refine Or.inr fun n hn ↦ ?_
    by_contra hne
    exact h (multiplicative_additive_paired_squares_eq_id_of_ne_zero k hk f hf hadd n hn hne)

end MetaMathlibExt
