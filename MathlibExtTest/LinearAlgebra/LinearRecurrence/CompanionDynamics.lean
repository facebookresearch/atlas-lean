/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.LinearRecurrence.CompanionDynamics
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! Tests for the companion matrix and the characteristic-polynomial recurrence. -/

open Matrix Polynomial

namespace MetaMathlibExt.LinearRecurrence

-- Order one has no shift rows and includes negative integer coefficients.
private abbrev orderOne : _root_.LinearRecurrence ℤ := ⟨1, fun _ ↦ -2⟩

example (n : ℕ) :
    (-2 : ℤ) ^ n * 3 = ((companionMatrix orderOne ^ n) *ᵥ (fun _ ↦ 3)) (0 : Fin 1) := by
  have h : orderOne.IsSolution (fun m ↦ (-2 : ℤ) ^ m * 3) := by
    intro m
    change (-2 : ℤ) ^ (m + 1) * 3 = ∑ _ : Fin 1, (-2 : ℤ) * ((-2) ^ (m + 0) * 3)
    simp [pow_succ', mul_assoc]
  have hs : (fun i : Fin 1 ↦ (-2 : ℤ) ^ (i : ℕ) * 3) = fun _ ↦ 3 := by
    funext i
    fin_cases i
    decide
  have hobs := (isSolution_iff_obs_companion orderOne (by decide) _).mp h n
  rwa [hs] at hobs

-- The first row really shifts; the final row is not in reverse order.
private abbrev orderTwo : _root_.LinearRecurrence ℤ := ⟨2, ![2, -1]⟩

private theorem orderTwo_matrix : companionMatrix orderTwo = !![0, 1; 2, -1] := by
  ext i j
  rw [companionMatrix_apply]
  fin_cases i <;> fin_cases j <;> decide

example : (companionMatrix orderTwo ^ 2) *ᵥ ![2, -1] = ![5, -7] := by
  rw [orderTwo_matrix, pow_succ, pow_one, ← Matrix.mulVec_mulVec]
  ext i
  fin_cases i <;> decide

example : orderTwo.IsSolution (fun n ↦ ((companionMatrix orderTwo ^ n) *ᵥ ![2, -1]) 0) := by
  let u : ℕ → ℤ := fun n ↦ ((companionMatrix orderTwo ^ n) *ᵥ ![2, -1]) 0
  have hinit : (fun i : Fin 2 ↦ u i) = ![2, -1] := by
    funext i
    fin_cases i
    · simp [u]
    · change ((companionMatrix orderTwo ^ 1) *ᵥ ![2, -1]) (0 : Fin 2) = -1
      rw [pow_one, orderTwo_matrix]
      decide
  apply (isSolution_iff_obs_companion orderTwo (by decide) u).mpr
  rw [hinit]
  intro n
  rfl

-- This singular matrix has a nonzero observation at `n = 1`, then an all-zero tail.
-- The recurrence certified by `X ^ 2` holds from `n = 0`, not just on the tail.
private def A : Matrix (Fin 2) (Fin 2) ℤ := !![0, 2; 0, 0]

private theorem charpoly_A : A.charpoly = X ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  have ht : A.trace = 0 := by decide
  have hd : A.det = 0 := by rw [Matrix.det_fin_two]; decide
  simp [ht, hd]

example : (![3, 4] : Fin 2 → ℤ) ⬝ᵥ (A ^ 1 *ᵥ ![5, 7]) = 42 := by
  rw [pow_one]
  decide

example (n : ℕ) : (![3, 4] : Fin 2 → ℤ) ⬝ᵥ (A ^ (n + 2) *ᵥ ![5, 7]) = 0 := by
  have h := isSolution_charpolyRecurrence_dotProduct_pow_mulVec A ![3, 4] ![5, 7] n
  have hcoeff (i : Fin (Fintype.card (Fin 2))) : A.charpoly.coeff i = 0 := by
    have hi : (i : ℕ) < 2 := lt_of_lt_of_le i.isLt (Fintype.card_fin 2).le
    rw [charpoly_A, Polynomial.coeff_X_pow, ite_eq_right hi.ne]
  change (![3, 4] : Fin 2 → ℤ) ⬝ᵥ (A ^ (n + Fintype.card (Fin 2)) *ᵥ ![5, 7]) =
    ∑ i : Fin (Fintype.card (Fin 2)), -A.charpoly.coeff i *
      ((![3, 4] : Fin 2 → ℤ) ⬝ᵥ (A ^ (n + i) *ᵥ ![5, 7])) at h
  simp only [hcoeff, neg_zero, zero_mul, Finset.sum_const_zero] at h
  rwa [Fintype.card_fin] at h

end MetaMathlibExt.LinearRecurrence
