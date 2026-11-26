/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.IsSquare
import MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticNineTermProgression

namespace MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

-- Positive definite, with discriminant `-15` and an odd mixed coefficient.
example : ∃ u0 d : ℤ, d ≠ 0 ∧ ∀ i : ℕ, i < 9 → ∃ x y : ℤ,
    u0 + i * d = 2 * x ^ 2 + x * y + 2 * y ^ 2 := by
  simpa only [one_mul] using
    exists_nine_term_arithmetic_progression_binary_quadratic 2 1 2 (hirr := by norm_num)

-- Indefinite, with discriminant `17` and a negative leading coefficient.
example : ∃ u0 d : ℤ, d ≠ 0 ∧ ∀ i : ℕ, i < 9 → ∃ x y : ℤ,
    u0 + i * d = -2 * x ^ 2 + x * y + 2 * y ^ 2 := by
  simpa only [one_mul] using
    exists_nine_term_arithmetic_progression_binary_quadratic (-2) 1 2 (hirr := by norm_num)

end MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted
