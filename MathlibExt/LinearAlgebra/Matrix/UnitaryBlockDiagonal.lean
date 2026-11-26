/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Block diagonal and reindexing of unitary matrices

Let R be a commutative star ring and n,m finite index types. If U∈U(n,R), V∈U(m,R), then
diag(U,V) is unitary on n⊕m. Reindexing a unitary along n≃m also preserves unitarity.
-/

@[expose] public section

namespace Matrix

universe u v w

variable {n : Type u} {m : Type v} {R : Type w}
variable [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable [CommRing R] [StarRing R]

/-- **Block diagonal of two unitaries.**

Let R be a commutative star ring, n,m finite index types and U,V unitary matrices over R of
those sizes. Then [[U,0],[0,V]] belongs to U(n⊕m,R).
-/
theorem fromBlocks_diagonal_mem_unitaryGroup
    {U : Matrix n n R} {V : Matrix m m R}
    (hU : U ∈ Matrix.unitaryGroup n R)
    (hV : V ∈ Matrix.unitaryGroup m R) :
    Matrix.fromBlocks U 0 0 V ∈ Matrix.unitaryGroup (n ⊕ m) R := by
  rw [Matrix.mem_unitaryGroup_iff] at hU hV ⊢
  have hConj : (Matrix.fromBlocks U 0 0 V)ᴴ =
      Matrix.fromBlocks Uᴴ 0 0 Vᴴ := by
    rw [Matrix.fromBlocks_conjTranspose]
    simp
  have hStar : star (Matrix.fromBlocks U 0 0 V) =
      Matrix.fromBlocks (star U) 0 0 (star V) := by
    calc star (Matrix.fromBlocks U 0 0 V)
        = (Matrix.fromBlocks U 0 0 V)ᴴ := rfl
      _ = Matrix.fromBlocks Uᴴ 0 0 Vᴴ := hConj
      _ = Matrix.fromBlocks (star U) 0 0 (star V) := rfl
  rw [hStar, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]
  rw [hU, hV, Matrix.fromBlocks_one]

/-- **Unitarity under an index equivalence.**

Let R be a commutative star ring, n,m finite index types, e:n≃m and U∈U(n,R). The matrix
reindex_e(U) with entry U(e⁻¹(i),e⁻¹(j)) belongs to U(m,R).
-/
theorem reindex_mem_unitaryGroup (e : n ≃ m)
    {U : Matrix n n R} (hU : U ∈ Matrix.unitaryGroup n R) :
    Matrix.reindex e e U ∈ Matrix.unitaryGroup m R := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  have hConj : (Matrix.reindex e e U)ᴴ =
      Matrix.reindex e e Uᴴ :=
    Matrix.conjTranspose_reindex e e U
  have hStar : star (Matrix.reindex e e U) =
      Matrix.reindex e e (star U) := by
    calc star (Matrix.reindex e e U)
        = (Matrix.reindex e e U)ᴴ := rfl
      _ = Matrix.reindex e e Uᴴ := hConj
      _ = Matrix.reindex e e (star U) := rfl
  rw [hStar]
  have hMul : Matrix.reindex e e U *
      Matrix.reindex e e (star U) =
      Matrix.reindex e e (U * star U) := by
    simp only [Matrix.reindex_apply]
    rw [← Matrix.submatrix_mul_equiv (e₂ := e.symm)]
  rw [hMul, hU]
  simp only [Matrix.reindex_apply, Matrix.submatrix_one_equiv]

end Matrix
