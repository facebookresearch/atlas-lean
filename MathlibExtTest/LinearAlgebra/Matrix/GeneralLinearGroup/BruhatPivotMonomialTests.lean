/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.CanonicalPivotReduction
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatMonomialUniqueness
import Mathlib.Tactic.NormNum

/-! # Concrete pivot reduction and monomial entries

These tests calculate a rational pivot reduction and check the entries of a weighted 3-cycle
using `monomialMatrixHom_entry`. They do not test uniqueness of Bruhat factors.
-/

open Matrix

namespace Matrix.GeneralLinearGroup.R01BruhatInstances

private def pivotMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 3, 7]

private def pivotFixture : GL (Fin 2) ℚ where
  val := pivotMatrix
  inv := !![7, -2; -3, 1]
  val_inv := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, pivotMatrix, Matrix.one_apply]
  inv_val := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, pivotMatrix, Matrix.one_apply]

private theorem pivotFixture_row : pivotRow pivotFixture (0 : Fin 2) = 1 := by
  apply le_antisymm
  · generalize pivotRow pivotFixture (0 : Fin 2) = r
    fin_cases r <;> decide
  · apply pivotRow_le
    rw [mem_columnSupport]
    decide

private theorem pivotMatrix_nonzero : pivotMatrix 1 0 ≠ 0 := by decide

-- Transport only the row index; the two nonzero witnesses are proof-irrelevant.
private theorem clear_eq_of_row_eq (r s : Fin 2) (hr : pivotMatrix r 0 ≠ 0)
    (hs : pivotMatrix s 0 ≠ 0) (h : r = s) :
    pivotCleared pivotMatrix r 0 hr = pivotCleared pivotMatrix s 0 hs := by
  subst s
  rfl

private theorem pivotFixture_cleared :
    canonicalPivotClearedAt pivotFixture (0 : Fin 2) = !![0, -(1 / 3); 3, 0] := by
  calc
    _ = pivotCleared pivotMatrix 1 0 pivotMatrix_nonzero :=
      clear_eq_of_row_eq _ _ (pivotRow_ne_zero pivotFixture 0) pivotMatrix_nonzero pivotFixture_row
    _ = _ := by
      apply Matrix.ext
      intro i j
      unfold pivotCleared columnClear
      rw [columnSweep_mul_apply]
      simp only [rowClear_mul_apply, columnClearCoeffs]
      fin_cases i <;> fin_cases j <;> norm_num [pivotMatrix]

-- Both triangular clearers are nonidentity, and the swap is on the left.
example :
    pivotRow pivotFixture (0 : Fin 2) = 1 ∧
      canonicalPivotClearedAt pivotFixture (0 : Fin 2) = !![0, -(1 / 3); 3, 0] ∧
      (↑(alignedPivotUnitAt pivotFixture (0 : Fin 2)) : Matrix (Fin 2) (Fin 2) ℚ) =
        !![3, 0; 0, -(1 / 3)] := by
  refine ⟨pivotFixture_row, pivotFixture_cleared, ?_⟩
  rw [coe_alignedPivotUnitAt, pivotFixture_row, pivotFixture_cleared]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.swap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.permMatrix_entry_eq,
      Equiv.swap_apply_def]

private def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

private def weights (i : Fin 3) : ℚˣ :=
  if i = 0 then Units.mk0 2 (by decide)
  else if i = 1 then Units.mk0 3 (by decide)
  else Units.mk0 (1 / 6) (by norm_num)

-- The cycle is not its own inverse; the three weights distinguish row and column weighting.
example :
    (monomialMatrixHom ℚ (Fin 3) ⟨weights, cycle⟩ : Matrix (Fin 3) (Fin 3) ℚ) =
      !![0, 0, 2; 3, 0, 0; 0, 1 / 6, 0] := by
  apply Matrix.ext
  intro i j
  rw [monomialMatrixHom_entry]
  fin_cases i <;> fin_cases j <;>
    norm_num [weights, cycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

end Matrix.GeneralLinearGroup.R01BruhatInstances
