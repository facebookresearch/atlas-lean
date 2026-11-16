/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Tactic.Abel

/-!
# Pauli XZ operators

Pauli operators `X^a Z^b` in the computational basis, with
the product phase rule. CSS code construction is not
included here.
-/

@[expose] public section

/-- Pauli `X^a Z^b` operator in the computational basis
(QCI-16 stabilizer core). Basis states are bitstrings
`x : Fin n → ZMod 2`; the operator is given by its matrix
entries: it sends `x` to `x + a` with phase
`(-1) ^ (b · x)`, where the dot product is over `ZMod 2`
and read through `ZMod.val`. -/
noncomputable def pauliXZ {n : ℕ} (a b : Fin n → ZMod 2) :
    (Fin n → ZMod 2) → (Fin n → ZMod 2) → ℂ :=
  fun y x => if y = x + a then (-1 : ℂ) ^ (∑ i, b i * x i).val else 0

/-- Matrix composition over the finite basis. -/
noncomputable def matMul {n : ℕ}
    (M N : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → (Fin n → ZMod 2) → ℂ :=
  fun y x => ∑ z, M y z * N z x

private theorem neg_one_pow_val_add (s t : ZMod 2) :
    (-1 : ℂ) ^ (s + t).val = (-1 : ℂ) ^ s.val * (-1 : ℂ) ^ t.val := by
  have h2 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  have v0 : (0 : ZMod 2).val = 0 := by decide
  have v1 : (1 : ZMod 2).val = 1 := by decide
  rcases h2 s with rfl | rfl <;> rcases h2 t with rfl | rfl <;> simp [h11, v0, v1]

/-- Product of Pauli operators: `X^a Z^b` times
`X^a' Z^b'` picks up the phase `(-1) ^ (b · a')`. In
particular the two commute exactly when `b · a'` and
`b' · a` have the same parity. -/
theorem pauliXZ_mul {n : ℕ} (a b a' b' : Fin n → ZMod 2) :
    matMul (pauliXZ a b) (pauliXZ a' b')
      = fun y x => (-1 : ℂ) ^ (∑ i, b i * a' i).val
          * pauliXZ (a + a') (b + b') y x := by
  funext y x
  simp only [matMul, pauliXZ]
  by_cases h : y = x + (a + a')
  · rw [ite_eq_left h]
    rw [Finset.sum_eq_single (x + a')]
    · have hy : y = (x + a') + a := by rw [h, add_comm a a', ← add_assoc]
      rw [ite_eq_left hy, ite_eq_left rfl]
      have h1 : (∑ i, b i * (x + a') i) = (∑ i, b i * x i) + (∑ i, b i * a' i) := by
        simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      have h2 : (∑ i, (b + b') i * x i) = (∑ i, b i * x i) + (∑ i, b' i * x i) := by
        simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      have hsum : (∑ i, b i * (x + a') i) + (∑ i, b' i * x i)
          = (∑ i, b i * a' i) + ∑ i, (b + b') i * x i := by
        rw [h1, h2]; abel
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

end
