/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.BinaryRecurrenceQuadraticForm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! # Tests for the quadratic form identity for binary recurrences -/

namespace MetaMathlibExt.binary_recurrence_quadratic_form_eq_neg_pow_mul_sq.Tests

-- The first example in the source has determinant -1 and a nonzero mixed coefficient.
example (G H : ℕ → ℤ) (hG : ∀ j, G (j + 2) = 4 * G j) (hH : ∀ j, H (j + 2) = 4 * H j)
    (g₀ : G 0 = 1) (g₁ : G 1 = 2) (h₀ : H 0 = 2) (h₁ : H 1 = 3) (n : ℕ) :
    -7 * G n ^ 2 + 4 * G n * H n = (-4) ^ n := by
  have h := binary_recurrence_quadratic_form_eq_neg_pow_mul_sq 0 4 G H
    (by simpa using hG) (by simpa using hH) n
  norm_num [g₀, g₁, h₀, h₁] at h
  linear_combination h

-- Proportional initial data give a square equal to zero over any commutative ring.
example {R : Type*} [CommRing R] (A B : R) (G H : ℕ → R)
    (hG : ∀ j, G (j + 2) = A * G (j + 1) + B * G j)
    (hH : ∀ j, H (j + 2) = A * H (j + 1) + B * H j)
    (g₀ : G 0 = 0) (g₁ : G 1 = 1) (h₀ : H 0 = 0) (h₁ : H 1 = 2) (n : ℕ) :
    (2 * G n - H n) ^ 2 = 0 := by
  have h := binary_recurrence_quadratic_form_eq_neg_pow_mul_sq A B G H hG hH n
  simp [g₀, g₁, h₀, h₁] at h
  linear_combination h

end MetaMathlibExt.binary_recurrence_quadratic_form_eq_neg_pow_mul_sq.Tests
