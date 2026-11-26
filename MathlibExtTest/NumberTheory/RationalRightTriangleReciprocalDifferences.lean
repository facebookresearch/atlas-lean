/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RationalRightTriangleReciprocalDifferences
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat

/-! # Tests for rational right triangles with sides differences of unit fractions -/

open MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

-- Outside any finite collection, the hypotenuse still has a representation with
-- strictly increasing positive denominators.
example (excluded : Finset (ℚ × ℚ × ℚ)) :
    ∃ X Y Z : ℚ, (X, Y, Z) ∉ excluded ∧ X ^ 2 + Y ^ 2 = Z ^ 2 ∧
      ∃ r s : ℕ, 0 < r ∧ r < s ∧ Z = 1 / (r : ℚ) - 1 / (s : ℚ) := by
  obtain ⟨⟨X, Y, Z⟩, h, hout⟩ :=
    rational_right_triangles_reciprocal_differences_infinite.exists_notMem_finset excluded
  obtain ⟨_, _, hZ, hright, x, y, p, q, r, s, _, _, _, _, hr, hs, _, _, heq⟩ := h
  refine ⟨X, Y, Z, hout, hright, r, s, hr, ?_, heq⟩
  rw [heq, sub_pos] at hZ
  exact_mod_cast lt_of_one_div_lt_one_div (show 0 < (s : ℚ) by exact_mod_cast hs) hZ
