/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressions
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

-- The two terms use coordinates with denominators two and three, and share one scale.
example : ∃ k : ℤ, k ≠ 0 ∧ ∀ i ∈ Finset.range 2, ∃ x y : ℤ,
    (x : ℚ) ^ 2 + x * (y : ℚ) + (y : ℚ) ^ 2 = (k : ℚ) ^ 2 * (1 / 4 + i * (1 / 12)) := by
  have hrep (i : ℕ) (hi : i ∈ Finset.range 2) :
      ∃ x y : ℚ, x ^ 2 + x * y + y ^ 2 = 1 / 4 + i * (1 / 12) := by
    have hi' := Finset.mem_range.mp hi
    interval_cases i
    · exact ⟨1 / 2, -1 / 2, by norm_num⟩
    · exact ⟨1 / 3, 1 / 3, by norm_num⟩
  simpa using exists_int_representations_of_rat_arithmetic_progression
    1 1 1 2 (1 / 4) (1 / 12) (by simpa using hrep)

-- An empty progression requires no rational witnesses and still admits a nonzero scale.
example (a b c : ℤ) (u0 d : ℚ) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ i ∈ Finset.range 0, ∃ x y : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2 : ℚ) = (k : ℚ) ^ 2 * (u0 + i * d) :=
  exists_int_representations_of_rat_arithmetic_progression a b c 0 u0 d (by simp)

end MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted
