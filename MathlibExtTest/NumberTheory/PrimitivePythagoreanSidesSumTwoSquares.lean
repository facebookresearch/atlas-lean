/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimitivePythagoreanSidesSumTwoSquares

/-! # Tests for primitive Pythagorean triples with sides sums of two squares -/

open MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

-- Even after bounding all three coordinates, the theorem supplies a triple outside the box.
-- Its hypotenuse exceeds the bound and still has two positive square summands.
example (bound : ℕ) :
    ∃ X Y Z : ℕ, bound < Z ∧ X ^ 2 + Y ^ 2 = Z ^ 2 ∧ Nat.Coprime X Y ∧
      ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Z = r ^ 2 + s ^ 2 := by
  let small := Finset.range (bound + 1)
  obtain ⟨⟨X, Y, Z⟩, h, hout⟩ :=
    primitive_pythagorean_sides_sum_two_squares_infinite.exists_notMem_finset
      (small ×ˢ (small ×ˢ small))
  obtain ⟨hpyth, hcop, _, _, _, _, r, s, _, _, _, _, hr, hs, _, _, hZ⟩ := h
  refine ⟨X, Y, Z, ?_, hpyth, hcop, r, s, hr, hs, hZ⟩
  by_contra! hbound
  have hx : X ≤ Z := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (by omega)
  have hy : Y ≤ Z := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (by omega)
  exact hout (by simp [small]; omega)
