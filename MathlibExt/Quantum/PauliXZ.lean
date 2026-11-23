/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic.Abel

/-!
# Pauli XZ operators

Pauli operators `X^a Z^b` in the computational basis, as matrices indexed by bitstrings,
with the product phase rule. CSS code construction is not included here.
-/

@[expose] public section

namespace MathlibExt.Quantum.PauliXZ

/-- Pauli `X^a Z^b` operator in the computational basis. Basis states are bitstrings
`x : Fin n → ZMod 2`; the matrix sends `x` to `x + a` with phase `(-1) ^ (b ⬝ᵥ x)`, where
the dot product is over `ZMod 2` and read through `ZMod.val`. -/
noncomputable def pauliXZ {n : ℕ} (a b : Fin n → ZMod 2) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  Matrix.of fun y x => if y = x + a then (-1 : ℂ) ^ (b ⬝ᵥ x).val else 0

@[simp]
theorem pauliXZ_apply {n : ℕ} (a b y x : Fin n → ZMod 2) :
    pauliXZ a b y x = if y = x + a then (-1 : ℂ) ^ (b ⬝ᵥ x).val else 0 :=
  rfl

private theorem neg_one_pow_val_add (s t : ZMod 2) :
    (-1 : ℂ) ^ (s + t).val = (-1 : ℂ) ^ s.val * (-1 : ℂ) ^ t.val := by
  have h2 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  have v0 : (0 : ZMod 2).val = 0 := by decide
  have v1 : (1 : ZMod 2).val = 1 := by decide
  rcases h2 s with rfl | rfl <;> rcases h2 t with rfl | rfl <;> simp [h11, v0, v1]

/-- Product of Pauli operators: `X^a Z^b` times `X^a' Z^b'` is
`X^(a + a') Z^(b + b')` with the phase `(-1) ^ (b ⬝ᵥ a')`. -/
theorem pauliXZ_mul {n : ℕ} (a b a' b' : Fin n → ZMod 2) :
    pauliXZ a b * pauliXZ a' b'
      = (-1 : ℂ) ^ (b ⬝ᵥ a').val • pauliXZ (a + a') (b + b') := by
  ext y x
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [pauliXZ_apply]
  by_cases h : y = x + (a + a')
  · rw [ite_eq_left h]
    rw [Finset.sum_eq_single (x + a')]
    · have hy : y = (x + a') + a := by rw [h, add_comm a a', ← add_assoc]
      rw [ite_eq_left hy, ite_eq_left rfl]
      have hsum : b ⬝ᵥ (x + a') + b' ⬝ᵥ x = b ⬝ᵥ a' + (b + b') ⬝ᵥ x := by
        rw [dotProduct_add, add_dotProduct]; abel
      rw [← neg_one_pow_val_add, ← neg_one_pow_val_add, hsum]
    · intro z _ hz
      rw [ite_eq_right hz, mul_zero]
    · exact fun hmem => absurd (Finset.mem_univ _) hmem
  · rw [ite_eq_right h, mul_zero]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : z = x + a'
    · by_cases hy : y = z + a
      · exfalso; apply h
        rw [hy, hz, add_assoc, add_comm a' a]
      · rw [ite_eq_right hy, zero_mul]
    · rw [ite_eq_right hz, mul_zero]

end MathlibExt.Quantum.PauliXZ

end
