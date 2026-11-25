/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.Group.Units.Defs

/-!
# A native block involution from an actual split rectangular pair

For U*V=1, the block matrix [[0,U],[V,1−V*U]] is its own inverse.
The entries stay in an arbitrary noncommutative ring. The construction
uses native Matrix.fromBlocks and multiplication; no inverse matrix or
comparison is supplied as data.
-/

@[expose] public section

noncomputable section

namespace Matrix

universe a n m t

variable {A : Type a} [Ring A]
  {N : Type n} [Fintype N] [DecidableEq N]
  {M : Type m} [Fintype M] [DecidableEq M]
  (U : Matrix N M A) (V : Matrix M N A)

/-- The actual native block matrix for a rectangular pair. -/
def splitInvolution : Matrix (N ⊕ M) (N ⊕ M) A :=
  fromBlocks 0 U V (1 - V * U)
omit [DecidableEq M] in
/-- The complementary block comes from an actual idempotent. -/
theorem splitPair_idempotent (h : U * V = 1) : (V * U) * (V * U) = V * U := by
  calc
    _ = V * (U * (V * U)) := Matrix.mul_assoc _ _ _
    _ = V * ((U * V) * U) :=
      congrArg (fun x : Matrix N M A => V * x) (Matrix.mul_assoc U V U).symm
    _ = (V * (U * V)) * U := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [h, Matrix.mul_one]

/-- The top-right block cancels in the square, in the original product order. -/
theorem splitPair_right_zero (h : U * V = 1) : U * (1 - V * U) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, Matrix.one_mul, sub_self]

/-- The bottom-left block cancels without commuting any ring elements. -/
theorem splitPair_left_zero (h : U * V = 1) : (1 - V * U) * V = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_one, sub_self]

/-- The bottom-right block of the square is the actual identity. -/
theorem splitPair_complement (h : U * V = 1) :
    V * U + (1 - V * U) * (1 - V * U) = 1 := by
  have hp := splitPair_idempotent U V h
  have hq : (1 - V * U) * (1 - V * U) = 1 - V * U := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
      hp, sub_self, sub_zero]
  rw [hq, add_comm, sub_add_cancel]

/-- The complete actual block matrix is an involution. -/
theorem splitInvolution_mul_self (h : U * V = 1) :
    splitInvolution U V * splitInvolution U V = 1 := by
  rw [splitInvolution, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add]
  rw [h, splitPair_right_zero U V h, splitPair_left_zero U V h,
    splitPair_complement U V h, fromBlocks_one]

/-- The native unit has the same explicit matrix as both value and inverse. -/
def splitInvolutionUnit (h : U * V = 1) : (Matrix (N ⊕ M) (N ⊕ M) A)ˣ where
  val := splitInvolution U V
  inv := splitInvolution U V
  val_inv := splitInvolution_mul_self U V h
  inv_val := splitInvolution_mul_self U V h

@[simp]
theorem splitInvolutionUnit_val (h : U * V = 1) :
    (splitInvolutionUnit U V h).val = splitInvolution U V := rfl

-- keeps the stored inverse-field getter for rw; Units.inv_eq_val_inv simplifies its left-hand
-- side
@[simp, nolint simpNF]
theorem splitInvolutionUnit_inv (h : U * V = 1) :
    (splitInvolutionUnit U V h).inv = splitInvolution U V := rfl

section Row

variable {J : Type m} [Fintype J] [DecidableEq J] (u v : J → A)

/-- The actual one-row matrix of the normalized family. -/
def normalizedRow : Matrix PUnit J A := Matrix.of (fun _ j => u j)

/-- The actual one-column matrix, with no transposed product convention. -/
def normalizedColumn : Matrix J PUnit A := Matrix.of (fun j _ => v j)
omit [DecidableEq J] in
theorem normalizedRow_mul_column (h : (∑ j, u j * v j) = 1) :
    normalizedRow u * normalizedColumn v = 1 := by
  ext i j
  cases i
  cases j
  rw [Matrix.mul_apply]
  change (∑ t : J, u t * v t) = 1
  exact h

/-- The normalized family gives a concrete unit indexed by PUnit⊕J, even if J is empty. -/
def normalizedFrameUnit (h : (∑ j, u j * v j) = 1) :
    (Matrix (PUnit ⊕ J) (PUnit ⊕ J) A)ˣ :=
  splitInvolutionUnit (normalizedRow u) (normalizedColumn v)
    (normalizedRow_mul_column u v h)

@[simp]
theorem normalizedFrameUnit_val (h : (∑ j, u j * v j) = 1) :
    (normalizedFrameUnit u v h).val =
      fromBlocks 0 (normalizedRow u) (normalizedColumn v)
        (1 - normalizedColumn v * normalizedRow u) := rfl

-- keeps the stored inverse-field getter for rw; Units.inv_eq_val_inv simplifies its left-hand
-- side
@[simp, nolint simpNF]
theorem normalizedFrameUnit_inv (h : (∑ j, u j * v j) = 1) :
    (normalizedFrameUnit u v h).inv =
      fromBlocks 0 (normalizedRow u) (normalizedColumn v)
        (1 - normalizedColumn v * normalizedRow u) := rfl

@[simp]
theorem normalizedFrameUnit_val_inl_inl (h : (∑ j, u j * v j) = 1)
    (i j : PUnit.{t + 1}) :
    (normalizedFrameUnit.{a, m, t} u v h).val (Sum.inl i) (Sum.inl j) = 0 := rfl

@[simp]
theorem normalizedFrameUnit_val_inl_inr (h : (∑ j, u j * v j) = 1)
    (i : PUnit.{t + 1}) (j : J) :
    (normalizedFrameUnit.{a, m, t} u v h).val (Sum.inl i) (Sum.inr j) = u j := rfl

@[simp]
theorem normalizedFrameUnit_val_inr_inl (h : (∑ j, u j * v j) = 1)
    (i : J) (j : PUnit.{t + 1}) :
    (normalizedFrameUnit.{a, m, t} u v h).val (Sum.inr i) (Sum.inl j) = v i := rfl

@[simp]
theorem normalizedFrameUnit_inv_inl_inl (h : (∑ j, u j * v j) = 1)
    (i j : PUnit.{t + 1}) :
    (normalizedFrameUnit.{a, m, t} u v h).inv (Sum.inl i) (Sum.inl j) = 0 := rfl

@[simp]
theorem normalizedFrameUnit_inv_inl_inr (h : (∑ j, u j * v j) = 1)
    (i : PUnit.{t + 1}) (j : J) :
    (normalizedFrameUnit.{a, m, t} u v h).inv (Sum.inl i) (Sum.inr j) = u j := rfl

@[simp]
theorem normalizedFrameUnit_inv_inr_inl (h : (∑ j, u j * v j) = 1)
    (i : J) (j : PUnit.{t + 1}) :
    (normalizedFrameUnit.{a, m, t} u v h).inv (Sum.inr i) (Sum.inl j) = v i := rfl

/-- The actual PUnit corner before conjugation. -/
def normalizedFrameCorner (x : A) : Matrix (PUnit ⊕ J) (PUnit ⊕ J) A :=
  fromBlocks (Matrix.of (fun _ _ : PUnit => x)) 0 0 0

/-- Actual conjugation sends the PUnit corner to the computed Peirce block v_i*x*u_j. -/
theorem normalizedFrameUnit_conjugateCorner (h : (∑ j, u j * v j) = 1) (x : A) :
    (normalizedFrameUnit.{a, m, t} u v h).inv *
        normalizedFrameCorner.{a, m, t} (J := J) x *
        (normalizedFrameUnit.{a, m, t} u v h).val =
      fromBlocks 0 0 0 (Matrix.of (fun i j : J => v i * x * u j)) := by
  rw [normalizedFrameUnit_inv.{a, m, t, t}, normalizedFrameUnit_val.{a, m, t, t},
    normalizedFrameCorner,
    fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  apply congrArg (fun X : Matrix J J A =>
    fromBlocks (0 : Matrix PUnit PUnit A) (0 : Matrix PUnit J A) (0 : Matrix J PUnit A) X)
  ext i j
  rw [Matrix.mul_apply]
  simp only [normalizedRow, normalizedColumn, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_unique]

end Row

end Matrix
