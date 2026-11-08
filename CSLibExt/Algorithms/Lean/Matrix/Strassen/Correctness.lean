/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Strassen.Basic
public import Mathlib.Data.Matrix.Mul
import all CSLibExt.Algorithms.Lean.Matrix.Strassen.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NoncommRing

/-!
# Correctness of Strassen's saved matrix accumulator

Induction on `k` identifies each of the seven actual recursive returned
products. Canonical Matrix block multiplication and four noncommutative
bilinear identities assemble the saved `C + A * B`.
Only a non-unital, non-associative ring is required: multiplication need not
commute or associate. The vector-to-Matrix view is private proof scaffolding,
not a second public matrix representation or an executable multiplication.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

universe u

private def asMatrix {R : Type u} {n : Nat} (M : Vector (Vector R n) n) :
    Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (M.get i).get j

private lemma split_matrix {R : Type u} (k : Nat)
    (M : Vector (Vector R (2 ^ (k + 1))) (2 ^ (k + 1))) :
    Matrix.fromBlocks (asMatrix (quadrant k M false false)) (asMatrix (quadrant k M false true))
      (asMatrix (quadrant k M true false)) (asMatrix (quadrant k M true true)) =
        (asMatrix M).submatrix (halfEquiv k) (halfEquiv k) := by
  ext i j
  cases i <;> cases j <;> simp [asMatrix, quadrant, Matrix.fromBlocks]

private lemma join_matrix {R : Type u} (k : Nat)
    (a b c d : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    (asMatrix (joinBlocks k a b c d)).submatrix (halfEquiv k) (halfEquiv k) =
      Matrix.fromBlocks (asMatrix a) (asMatrix b) (asMatrix c) (asMatrix d) := by
  ext i j
  cases i <;> cases j <;> simp [asMatrix, joinBlocks, Matrix.fromBlocks]

private lemma blockMap_matrix {R : Type u} {n : Nat} (op : R → R → R)
    (A B : Vector (Vector R n) n) :
    asMatrix (blockMap op A B).ret = fun i j => op (asMatrix A i j) (asMatrix B i j) := by
  funext i j
  exact blockMap_get op A B i j

private lemma zero_matrix {R : Type u} [Zero R] (n : Nat) :
    asMatrix (Vector.replicate n (Vector.replicate n (0 : R))) = 0 := by
  funext i j
  simp [asMatrix]

private lemma seven_blocks {R : Type u} [NonUnitalNonAssocRing R] {n : Nat}
    (c₁₁ c₁₂ c₂₁ c₂₂ a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : Matrix (Fin n) (Fin n) R) :
    Matrix.fromBlocks
      ((((c₁₁ + (a₁₁ + a₂₂) * (b₁₁ + b₂₂)) + a₂₂ * (b₂₁ - b₁₁)) -
        (a₁₁ + a₁₂) * b₂₂) + (a₁₂ - a₂₂) * (b₂₁ + b₂₂))
      ((c₁₂ + a₁₁ * (b₁₂ - b₂₂)) + (a₁₁ + a₁₂) * b₂₂)
      ((c₂₁ + (a₂₁ + a₂₂) * b₁₁) + a₂₂ * (b₂₁ - b₁₁))
      ((((c₂₂ + (a₁₁ + a₂₂) * (b₁₁ + b₂₂)) + a₁₁ * (b₁₂ - b₂₂)) -
        (a₂₁ + a₂₂) * b₁₁) - (a₁₁ - a₂₁) * (b₁₁ + b₁₂)) =
      Matrix.fromBlocks c₁₁ c₁₂ c₂₁ c₂₂ +
        Matrix.fromBlocks a₁₁ a₁₂ a₂₁ a₂₂ * Matrix.fromBlocks b₁₁ b₁₂ b₂₁ b₂₂ := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  congr 1 <;> noncomm_ring

private lemma run_matrix {R : Type u} [NonUnitalNonAssocRing R] (k : Nat)
    (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    asMatrix (strassenMatrixAccumulate k A B C).ret = asMatrix C + asMatrix A * asMatrix B := by
  induction k with
  | zero =>
    have : Subsingleton (Fin (2 ^ 0)) := by
      simp only [pow_zero]
      infer_instance
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simp [strassenMatrixAccumulate, asMatrix, Matrix.mul_apply]
  | succ k ih =>
    apply (Matrix.reindex (halfEquiv k).symm (halfEquiv k).symm).injective
    change (asMatrix (strassenMatrixAccumulate (k + 1) A B C).ret).submatrix
        (halfEquiv k) (halfEquiv k) =
      (asMatrix C).submatrix (halfEquiv k) (halfEquiv k) +
        (asMatrix A * asMatrix B).submatrix (halfEquiv k) (halfEquiv k)
    rw [← Matrix.submatrix_mul_equiv (asMatrix A) (asMatrix B)
      (halfEquiv k) (halfEquiv k) (halfEquiv k),
      ← split_matrix k C, ← split_matrix k A, ← split_matrix k B]
    simp only [strassenMatrixAccumulate, TimeM.ret_bind, TimeM.ret_pure, join_matrix,
      blockMap_matrix, ih, zero_matrix, zero_add]
    exact seven_blocks _ _ _ _ _ _ _ _ _ _ _ _

/-- Strassen accumulation returns the saved matrix `C` plus the canonical
Matrix product `A * B`, preserving multiplication operand order. -/
public theorem strassenMatrixAccumulate_ret {R : Type u} [NonUnitalNonAssocRing R]
    (k : Nat) (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    (Matrix.of fun i j => ((strassenMatrixAccumulate k A B C).ret.get i).get j) =
      (Matrix.of fun i j => (C.get i).get j) +
        (Matrix.of fun i j => (A.get i).get j) * (Matrix.of fun i j => (B.get i).get j) := by
  exact run_matrix k A B C

/-- Every Strassen output entry is its saved `C` entry plus the finite row-column
product sum, with the left factor drawn from `A` and the right factor from `B`. -/
public theorem strassenMatrixAccumulate_apply {R : Type u} [NonUnitalNonAssocRing R]
    (k : Nat) (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) (i j : Fin (2 ^ k)) :
    ((strassenMatrixAccumulate k A B C).ret.get i).get j =
      (C.get i).get j + ∑ t : Fin (2 ^ k), (A.get i).get t * (B.get t).get j := by
  have h := congrFun (congrFun (strassenMatrixAccumulate_ret k A B C) i) j
  simpa only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply] using h

end Cslib.Algorithms.Lean.Matrix
