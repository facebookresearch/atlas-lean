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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Mathlib.Data.Matrix.Basis

/-!
# Elementary transvections over arbitrary rings

Let R be a ring and n a finite index type. Write GL(n,R) for the group of invertible n×n
matrices, and E_ij(a)=I+a*e_ij for i≠j, where e_ij is the single-entry matrix. The matrix
E_ij(a) is invertible with inverse E_ij(-a). The ring need not be commutative.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [Ring R]

/-- **Invertible elementary transvection matrix.**

Let R be a ring and n a finite index type. Write GL(n,R) for the group of invertible n×n
matrices, and E_ij(a)=I+a*e_ij for i≠j, where e_ij is the single-entry matrix. The element
elementary i j hij a∈GL(n,R) is E_ij(a), with inverse I-a*e_ij.
-/
def elementary (i j : n) (hij : i ≠ j) (a : R) : GL n R where
  val := 1 + Matrix.single i j a
  inv := 1 + Matrix.single i j (-a)
  val_inv := by
    simp [mul_add, add_mul, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, ← single_neg]
  inv_val := by
    simp [mul_add, add_mul, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, ← single_neg]

@[simp]
lemma coe_elementary (i j : n) (hij : i ≠ j) (a : R) :
    (↑(elementary i j hij a) : Matrix n n R) = 1 + Matrix.single i j a :=
  rfl

@[simp]
lemma elementary_zero (i j : n) (hij : i ≠ j) :
    elementary i j hij (0 : R) = 1 := by
  apply Units.ext
  simp

@[simp]
lemma elementary_mul_same (i j : n) (hij : i ≠ j) (a b : R) :
    elementary i j hij a * elementary i j hij b = elementary i j hij (a + b) := by
  apply Units.ext
  simp [mul_add, add_mul, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, single_add, add_assoc]

@[simp]
lemma elementary_inv (i j : n) (hij : i ≠ j) (a : R) :
    (elementary i j hij a)⁻¹ = elementary i j hij (-a) := by
  apply Units.ext
  rfl

section Map

variable {S : Type*} [Ring S]

@[simp]
theorem mapRingHom_elementary (f : R →+* S) (i j : n) (hij : i ≠ j) (a : R) :
    mapRingHom (n := n) f (elementary i j hij a) = elementary i j hij (f a) := by
  apply Units.ext
  simp only [coe_mapRingHom, coe_elementary]
  calc (1 + Matrix.single i j a).map f
      = f.mapMatrix (1 + Matrix.single i j a) := rfl
    _ = f.mapMatrix 1 + f.mapMatrix (Matrix.single i j a) := by rw [RingHom.map_add]
    _ = 1 + f.mapMatrix (Matrix.single i j a) := by rw [RingHom.map_one]
    _ = 1 + (Matrix.single i j a).map f := rfl
    _ = 1 + Matrix.single i j (f a) := by rw [map_single]

end Map

section Reindex

variable {m : Type*} [DecidableEq m] [Fintype m]

@[simp]
theorem reindexMulEquiv_elementary (e : n ≃ m) (i j : n) (hij : i ≠ j) (a : R) :
    reindexMulEquiv (A := R) e (elementary i j hij a) =
      elementary (e i) (e j) (fun h => hij (e.injective h)) a := by
  apply Units.ext
  rw [coe_reindexMulEquiv, coe_elementary, coe_elementary]
  have h_add := (reindexRingEquiv R e).map_add (1 : Matrix n n R) (Matrix.single i j a)
  have h_one := (reindexRingEquiv R e).map_one
  rw [coe_reindexRingEquiv] at h_add h_one
  calc Matrix.reindex e e (1 + Matrix.single i j a)
      = Matrix.reindex e e (1 : Matrix n n R) + Matrix.reindex e e (Matrix.single i j a) := h_add
    _ = 1 + Matrix.reindex e e (Matrix.single i j a) := by rw [h_one]
    _ = 1 + Matrix.single (e i) (e j) a := by
        simp [Matrix.reindex_apply, submatrix_single_equiv]

end Reindex

section Block

variable {m : Type*} [DecidableEq m] [Fintype m]

omit [Fintype n] [Fintype m] in
private lemma fromBlocks_single_inl (i j : n) (a : R) :
    fromBlocks (Matrix.single i j a) (0 : Matrix n m R) (0 : Matrix m n R)
        (0 : Matrix m m R) =
      Matrix.single (Sum.inl (α := n) (β := m) i) (Sum.inl j) a := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> simp [fromBlocks, Matrix.single]

@[simp]
theorem blockDiagonalOne_elementary (i j : n) (hij : i ≠ j) (a : R) :
    blockDiagonalOne (n := n) (m := m) (R := R) (elementary i j hij a) =
      elementary (Sum.inl (α := n) (β := m) i) (Sum.inl (α := n) (β := m) j)
        (by intro h; apply hij; cases h; rfl) a := by
  apply Units.ext
  rw [coe_blockDiagonalOne, coe_elementary, coe_elementary]
  have h_eq :
      fromBlocks (1 + Matrix.single i j a) (0 : Matrix n m R) (0 : Matrix m n R)
          (1 : Matrix m m R) =
        fromBlocks (1 : Matrix n n R) 0 0 1 +
          fromBlocks (Matrix.single i j a) 0 0 (0 : Matrix m m R) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp [fromBlocks, Matrix.add_apply]
  calc fromBlocks (1 + Matrix.single i j a) (0 : Matrix n m R) (0 : Matrix m n R)
          (1 : Matrix m m R)
      = fromBlocks (1 : Matrix n n R) 0 0 1 +
          fromBlocks (Matrix.single i j a) 0 0 (0 : Matrix m m R) := h_eq
    _ = (1 : Matrix (n ⊕ m) (n ⊕ m) R) +
          Matrix.single (Sum.inl i) (Sum.inl j) a := by
        rw [fromBlocks_one, fromBlocks_single_inl]

end Block

section Stabilization

@[simp]
theorem stabilization_elementary {k : ℕ} (i j : Fin k) (hij : i ≠ j) (a : R) :
    stabilization R (n := k) (elementary i j hij a) =
      elementary (finSumFinEquiv (m := k) (n := 1) (Sum.inl i))
        (finSumFinEquiv (m := k) (n := 1) (Sum.inl j))
        (by
          intro h
          apply hij
          have h' : Sum.inl (α := Fin k) (β := Fin 1) i =
              Sum.inl (α := Fin k) (β := Fin 1) j :=
            (finSumFinEquiv (m := k) (n := 1)).injective h
          cases h'
          rfl) a := by
  calc stabilization R (n := k) (elementary i j hij a)
      = reindexMulEquiv (finSumFinEquiv (m := k) (n := 1))
          (blockDiagonalOne (Fin k) (Fin 1) R (elementary i j hij a)) := rfl
    _ = reindexMulEquiv (finSumFinEquiv (m := k) (n := 1))
          (elementary (Sum.inl i) (Sum.inl j) _ a) := by rw [blockDiagonalOne_elementary]
    _ = elementary (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) _ a := by
        rw [reindexMulEquiv_elementary]

end Stabilization

end Matrix.GeneralLinearGroup
