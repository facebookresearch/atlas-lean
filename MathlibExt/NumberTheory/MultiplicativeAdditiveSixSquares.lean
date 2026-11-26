/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresEqIdOfThreeOrFour

/-!
# Multiplicative functions additive on three sums of two positive squares are the identity

We show that a complex-valued multiplicative function which is additive on three sums of
two positive squares and nonzero at `2` fixes every positive integer. This is Theorem 3 of
Jewel Mahajan, *Multiplicative functions additive on partitions of 2k nonzero squares*
(https://arxiv.org/abs/2606.29507), obtained as the `k = 3` case of
`multiplicative_additive_paired_squares_eq_id_of_three_or_four`.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- **Multiplicative functions additive on six paired squares and nonzero at $2$ are the
identity.** Let $f$ be a complex-valued multiplicative function with $f(2) \ne 0$ such that
$$f\Big(\sum_{j=1}^{3} (x_j^2 + y_j^2)\Big) = \sum_{j=1}^{3} f(x_j^2 + y_j^2)$$
for all positive integers $x_1, x_2, x_3, y_1, y_2, y_3$. Then $f(n) = n$ for every positive
integer $n$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 3 (`integers-2026-A121-thm-3`). -/
public theorem multiplicative_additive_six_squares_eq_id (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin 3 → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n := by
  exact multiplicative_additive_paired_squares_eq_id_of_three_or_four 3 (Or.inl rfl) f hf hadd h2

end MetaMathlibExt
