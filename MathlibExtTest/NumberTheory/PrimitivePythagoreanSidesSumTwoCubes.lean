/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimitivePythagoreanSidesSumTwoCubes

/-! # Tests for primitive Pythagorean triples with sides sums of two cubes -/

open MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

-- The theorem supplies a triple with hypotenuse above any prescribed bound.
example (bound : ℕ) :
    ∃ X Y Z : ℕ, bound < Z ∧ X ^ 2 + Y ^ 2 = Z ^ 2 ∧ Nat.Coprime X Y ∧
      ∃ x y p q r s : ℕ,
        0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧
          X = x ^ 3 + y ^ 3 ∧ Y = p ^ 3 + q ^ 3 ∧ Z = r ^ 3 + s ^ 3 := by
  let small := Finset.range (bound + 1)
  obtain ⟨⟨X, Y, Z⟩, h, hout⟩ :=
    primitive_pythagorean_sides_sum_two_cubes_infinite.exists_notMem_finset
      (small ×ˢ (small ×ˢ small))
  obtain ⟨hpyth, hcop, hcubes⟩ := h
  refine ⟨X, Y, Z, ?_, hpyth, hcop, hcubes⟩
  by_contra! hbound
  have hx : X ≤ Z := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (by omega)
  have hy : Y ≤ Z := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (by omega)
  exact hout (by simp [small]; omega)

-- The first parameter yields a primitive triple with all six cube bases positive.
example :
    let X : ℕ := 16776487
    let Y : ℕ := 221184
    let Z : ℕ := 16777945
    X ^ 2 + Y ^ 2 = Z ^ 2 ∧ Nat.Coprime X Y ∧
      X = 220 ^ 3 + 183 ^ 3 ∧ Y = 48 ^ 3 + 48 ^ 3 ∧ Z = 256 ^ 3 + 9 ^ 3 := by
  decide
