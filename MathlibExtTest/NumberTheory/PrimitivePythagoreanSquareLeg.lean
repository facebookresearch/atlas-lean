/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimitivePythagoreanSquareLeg
import Mathlib.Tactic.Linarith

/-! # Tests for primitive Pythagorean triples with a square leg -/

open MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

-- The square legs have unbounded square roots. For a fixed root p, the identity
-- Z² - X² = p⁴ bounds Z because X < Z.
example (bound : ℕ) :
    ∃ X p Z : ℕ, bound < p ∧ X ^ 2 + (p ^ 2) ^ 2 = Z ^ 2 ∧ Nat.Coprime X (p ^ 2) := by
  let small := Finset.range (bound ^ 4 + 1)
  obtain ⟨⟨X, Y, Z⟩, h, hout⟩ :=
    primitive_pythagorean_sides_square_middle_infinite.exists_notMem_finset
      (small ×ˢ (small ×ˢ small))
  obtain ⟨hpyth, hcop, _, _, p, _, _, _, _, hp, _, _, _, rfl, _⟩ := h
  refine ⟨X, p, Z, ?_, hpyth, hcop⟩
  by_contra! hsmall
  have hXZ : X < Z := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by
    have : 0 < (p ^ 2) ^ 2 := by positivity
    omega)
  have hZ : Z ≤ p ^ 4 := by
    nlinarith [Nat.mul_le_mul_right (X + Z) (show X + 1 ≤ Z from hXZ)]
  have hpZ : p ^ 2 ≤ Z := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (by omega)
  have := Nat.pow_le_pow_left hsmall 4
  exact hout (by simp [small]; omega)
