/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Pi

/-! The commutant of ordinary symmetric matrices on the coordinate factor.
The tensor index is arbitrary; only the 24 coordinate columns are used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- Insert a tensor-index vector into a single coordinate column. -/
def tensorColumnInsert {I : Type*} (j : Fin 24) :
    (I → ℝ) →ₗ[ℝ] (I → Fin 24 → ℝ) where
  toFun x t i := if i = j then x t else 0
  map_add' x y := by ext t i; by_cases h : i = j <;> simp [h]
  map_smul' a x := by ext t i; by_cases h : i = j <;> simp [h]

/-- Read a single coordinate column. -/
def tensorColumnRead {I : Type*} (j : Fin 24) :
    (I → Fin 24 → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun x t := x t j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def tensorCoordinateMatrix (i j : Fin 24) : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)

private theorem tensorCoordinateMatrix_apply (i j k : Fin 24) (w : Fin 24 → ℝ) :
    (tensorCoordinateMatrix i j *ᵥ w) k = if k = i then w j else 0 := by
  by_cases hk : k = i
  · rw [hk]
    simp only [tensorCoordinateMatrix, Matrix.mulVec, dotProduct, Matrix.vecMulVec,
      Matrix.of_apply, Pi.single_eq_same, one_mul, ite_true]
    change dotProduct (Pi.single j (1 : ℝ)) w = w j
    rw [single_dotProduct, one_mul]
  · simp [tensorCoordinateMatrix, Matrix.mulVec, dotProduct, Matrix.vecMulVec, hk]

private theorem tensorCoordinateMatrix_self_symm (i : Fin 24) :
    (tensorCoordinateMatrix i i).IsSymm := by
  unfold Matrix.IsSymm tensorCoordinateMatrix
  rw [Matrix.transpose_vecMulVec]

private theorem tensorCoordinateMatrix_swap_symm (i j : Fin 24) :
    (tensorCoordinateMatrix i j + tensorCoordinateMatrix j i).IsSymm := by
  unfold Matrix.IsSymm tensorCoordinateMatrix
  rw [Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec, add_comm]

/-- Commutation with the diagonal projectors makes every output column depend
only on the corresponding input column. -/
theorem tensorMatrixCommutant_column_local {I : Type*}
    (L : Module.End ℝ (I → Fin 24 → ℝ))
    (hL : ∀ A : Matrix (Fin 24) (Fin 24) ℝ, A.IsSymm →
      ∀ T : I → Fin 24 → ℝ,
        L (fun t => A *ᵥ T t) = fun t => A *ᵥ (L T) t)
    (T : I → Fin 24 → ℝ) (t : I) (i : Fin 24) :
    L T t i = L (tensorColumnInsert i (tensorColumnRead i T)) t i := by
  have h := hL (tensorCoordinateMatrix i i) (tensorCoordinateMatrix_self_symm i) T
  have hproj : (fun u => tensorCoordinateMatrix i i *ᵥ T u) =
      tensorColumnInsert i (tensorColumnRead i T) := by
    funext u j
    rw [tensorCoordinateMatrix_apply]
    rfl
  rw [hproj] at h
  have hi := congrFun (congrFun h t) i
  rw [tensorCoordinateMatrix_apply] at hi
  simpa only [ite_true] using hi.symm

/-- The off-diagonal symmetric elementary matrices identify the operator on each column. -/
theorem tensorMatrixCommutant_column_same {I : Type*}
    (L : Module.End ℝ (I → Fin 24 → ℝ))
    (hL : ∀ A : Matrix (Fin 24) (Fin 24) ℝ, A.IsSymm →
      ∀ T : I → Fin 24 → ℝ,
        L (fun t => A *ᵥ T t) = fun t => A *ᵥ (L T) t)
    (x : I → ℝ) (t : I) (i : Fin 24) :
    L (tensorColumnInsert i x) t i = L (tensorColumnInsert 0 x) t 0 := by
  by_cases hi : i = 0
  · simp only [hi]
  let A := tensorCoordinateMatrix i 0 + tensorCoordinateMatrix 0 i
  have h := hL A (tensorCoordinateMatrix_swap_symm i 0) (tensorColumnInsert 0 x)
  have hswap : (fun u => A *ᵥ (tensorColumnInsert 0 x) u) =
      tensorColumnInsert i x := by
    funext u j
    simp only [A, Matrix.add_mulVec, Pi.add_apply, tensorCoordinateMatrix_apply,
      tensorColumnInsert, LinearMap.coe_mk, AddHom.coe_mk, ite_true, hi, ite_false]
    simp only [ite_self, add_zero]
  rw [hswap] at h
  have hj := congrFun (congrFun h t) i
  simp only [A, Matrix.add_mulVec, Pi.add_apply, tensorCoordinateMatrix_apply,
    ite_true, hi, ite_false, add_zero] at hj
  exact hj

/-- Every real linear map commuting with every ordinary symmetric coordinate
matrix is a single tensor-index operator, applied identically in all 24 columns. -/
theorem tensorMatrixCommutant {I : Type*}
    (L : Module.End ℝ (I → Fin 24 → ℝ))
    (hL : ∀ A : Matrix (Fin 24) (Fin 24) ℝ, A.IsSymm →
      ∀ T : I → Fin 24 → ℝ,
        L (fun t => A *ᵥ T t) = fun t => A *ᵥ (L T) t) :
    ∃ S : Module.End ℝ (I → ℝ), ∀ T t i,
      L T t i = S (fun u => T u i) t := by
  refine ⟨(tensorColumnRead 0).comp (L.comp (tensorColumnInsert 0)), ?_⟩
  intro T t i
  rw [tensorMatrixCommutant_column_local L hL T t i,
    tensorMatrixCommutant_column_same L hL (tensorColumnRead i T) t i]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
