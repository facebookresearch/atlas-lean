/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.Determinant.QuotientBaseChange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A nonlocal integral algebra reduced modulo two

The integral algebra is ℤ² and the ideal is (2). The diagonal endomorphism
(3,5) has determinant 15, whose residue is 1. Its quotient action is checked
on an actual representative, rather than only by its type.
-/

@[expose] public section

noncomputable section
open Polynomial
namespace MathlibExtTest.QuotientBaseChange

abbrev S := Fin 2 → ℤ
def I : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
abbrev Base := ℤ ⧸ I
abbrev Quot := S ⧸ I.map (algebraMap ℤ S)

instance quotientFree : Module.Free Base Quot :=
  Module.Free.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv

instance quotientFinite : Module.Finite Base Quot :=
  Module.Finite.equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv

def diagonal : S →ₗ[ℤ] S := Matrix.toLin' (Matrix.diagonal ![(3 : ℤ), 5])

theorem residue_two : Ideal.Quotient.mk I (2 : ℤ) = 0 := by
  apply (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr
  exact Ideal.subset_span (by simp)

theorem residue_odd (k : ℤ) : Ideal.Quotient.mk I (2 * k + 1) = 1 := by
  rw [map_add, map_mul, residue_two, map_one]
  simp

theorem diagonal_det : diagonal.det = 15 := by
  norm_num [diagonal, Fin.prod_univ_two]

theorem diagonal_charpoly :
    diagonal.charpoly = (X - C (3 : ℤ)) * (X - C (5 : ℤ)) := by
  simp [diagonal, Matrix.charpoly_diagonal, Fin.prod_univ_two]

example :
    diagonal.quotientBaseChange I
        (Ideal.Quotient.mk (I.map (algebraMap ℤ S)) ![(1 : ℤ), 2]) =
      Ideal.Quotient.mk (I.map (algebraMap ℤ S)) ![(3 : ℤ), 10] := by
  rw [LinearMap.quotientBaseChange_mk]
  congr 1
  ext i
  fin_cases i <;> norm_num [diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example : (diagonal.quotientBaseChange I).det = 1 := by
  rw [LinearMap.det_quotientBaseChange, diagonal_det]
  simpa using residue_odd 7

end MathlibExtTest.QuotientBaseChange
