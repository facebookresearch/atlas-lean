/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RationalRightTriangleReciprocalSums

/-! # Tests for rational right triangles with sides sums of unit fractions -/

open MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

-- Excluding a finite list of side triples still leaves a triangle with a positive
-- unit-fraction decomposition of its hypotenuse.
example (excluded : Finset (ℚ × ℚ × ℚ)) :
    ∃ X Y Z : ℚ, (X, Y, Z) ∉ excluded ∧ 0 < X ∧ 0 < Y ∧ X ^ 2 + Y ^ 2 = Z ^ 2 ∧
      ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Z = 1 / (r : ℚ) + 1 / (s : ℚ) := by
  obtain ⟨⟨X, Y, Z⟩, h, hout⟩ :=
    rational_right_triangles_reciprocal_sums_infinite.exists_notMem_finset excluded
  obtain ⟨hX, hY, _, hright, x, y, p, q, r, s, _, _, _, _, hr, hs, _, _, hZ⟩ := h
  exact ⟨X, Y, Z, hout, hX, hY, hright, r, s, hr, hs, hZ⟩
