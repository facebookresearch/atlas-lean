/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessMain

/-!
# Tests for parallelogram uniqueness of squares
-/

open ArithmeticFunction MetaMathlibExt

private abbrev squares : ArithmeticFunction ℂ :=
  (ArithmeticFunction.pow 2 : ArithmeticFunction ℕ)

-- Check directly that the square function meets the hypotheses, without using uniqueness.
example : squares.IsMultiplicative ∧ squares 4 ≠ 0 ∧
    ∀ m n : ℕ, 0 < n → n < m →
      squares (m ^ 2 + n ^ 2) + squares (m ^ 2 - n ^ 2) =
        2 * squares (m ^ 2) + 2 * squares (n ^ 2) := by
  refine ⟨ArithmeticFunction.isMultiplicative_pow.natCast, ?_, ?_⟩
  · norm_num [squares, ArithmeticFunction.pow_apply]
  · intro m n _ hnm
    have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
    simp only [squares, ArithmeticFunction.natCoe_apply, ArithmeticFunction.pow_apply,
      show (2 : ℕ) ≠ 0 by decide, false_and, ite_false, Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow]
    ring

-- Check both exponent parities directly at the first odd prime, without the induction theorem.
example : squares (3 ^ 2) = 81 ∧ squares (3 ^ 3) = 729 := by
  norm_num [squares, ArithmeticFunction.pow_apply]

section

variable (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
variable (hpar : ∀ m n : ℕ, 0 < n → n < m →
  f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
variable (h4 : f 4 ≠ 0)

-- The conclusion includes zero as well as the initial values that distinguish the square solution.
example : f 0 = 0 ∧ f 4 = 16 ∧ f 11 = 121 := by
  have h := multiplicative_parallelogram_squares_eq_sq f hf hpar h4
  have h₀ : f 0 = 0 := by
    simpa only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h 0
  have h₄ := h 4
  have h₁₁ := h 11
  norm_num at h₄ h₁₁
  exact ⟨h₀, h₄, h₁₁⟩

-- Both exponent parities and coprime products are covered beyond the initial values.
example : f (2 ^ 7) = 16384 ∧ f (19 ^ 2) = 130321 ∧ f (4 * 23 ^ 3) = (48668 : ℂ) ^ 2 := by
  have h := multiplicative_parallelogram_squares_eq_sq f hf hpar h4
  have heven := h (19 ^ 2)
  have hodd := h (2 ^ 7)
  norm_num at heven hodd
  exact ⟨hodd, heven, h (4 * 23 ^ 3)⟩

end
