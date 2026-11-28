/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.Determinant.ColumnNormalization
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Column powers for an ordinary scalar and for zero

On ℤ², the diagonal columns 2¹ and 2² give determinant 8. With scalar zero
and exponents (0,1), the first column remains nonzero because 0⁰=1. The
existential normalization still fixes that first normalized column.
-/

@[expose] public section

noncomputable section
namespace MathlibExtTest.ColumnNormalization

abbrev V := Fin 2 → ℤ
def columnMap (π : ℤ) (c : Fin 2 → ℕ) : V →ₗ[ℤ] V :=
  Matrix.toLin' (Matrix.diagonal fun i => π ^ c i)

theorem columnMap_basis (π : ℤ) (c : Fin 2 → ℕ) (i : Fin 2) :
    columnMap π c (Pi.basisFun ℤ (Fin 2) i) =
      π ^ c i • Pi.basisFun ℤ (Fin 2) i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [columnMap, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example : (columnMap 2 ![(1 : ℕ), 2]).det = 8 := by
  have h := LinearMap.det_eq_pow_sum_mul_det_of_apply_basis
    (Pi.basisFun ℤ (Fin 2)) (2 : ℤ) ![(1 : ℕ), 2]
    (columnMap 2 ![(1 : ℕ), 2]) LinearMap.id
    (fun i => by simpa using columnMap_basis 2 ![(1 : ℕ), 2] i)
  norm_num [Fin.sum_univ_two] at h
  exact h

example :
    ∃ g : V →ₗ[ℤ] V,
      g (Pi.single 0 1) = Pi.single 0 1 ∧
        (columnMap 0 ![(0 : ℕ), 1]).det = 0 * g.det := by
  obtain ⟨g, hg, hd⟩ :=
    LinearMap.exists_det_eq_pow_sum_mul_det_of_exists_apply_basis
      (Pi.basisFun ℤ (Fin 2)) (0 : ℤ) ![(0 : ℕ), 1]
      (columnMap 0 ![(0 : ℕ), 1])
      (fun i => ⟨Pi.basisFun ℤ (Fin 2) i, columnMap_basis 0 ![(0 : ℕ), 1] i⟩)
  refine ⟨g, ?_, ?_⟩
  · have hfirst := hg (0 : Fin 2)
    rw [columnMap_basis] at hfirst
    norm_num at hfirst
    simpa using hfirst.symm
  · simpa [Fin.sum_univ_two] using hd

end MathlibExtTest.ColumnNormalization
