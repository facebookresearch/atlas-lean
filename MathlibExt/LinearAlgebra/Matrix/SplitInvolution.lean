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
# A block involution from a rectangular split pair

Let A be an arbitrary ring and U:N×M, V:M×N be matrices on finite index sets with UV=I_N. Then
VU is idempotent, U(I_M−VU)=0 and (I_M−VU)V=0. The block matrix W=[[0,U],[V,I_M−VU]] therefore
satisfies W²=I_{N⊕M} and defines a matrix unit whose inverse is W itself.

For families u,v:J → A with ∑ⱼuⱼvⱼ=1, take U to be the singleton row u and V the singleton
column v. Conjugating the scalar singleton corner x by W gives a matrix supported on J×J with
entry vᵢxuⱼ. Ring elements are never commuted in these formulas; the ring, row/column index sets
and singleton index retain their arbitrary universes.
-/

@[expose] public section

noncomputable section

namespace Matrix

universe a n m t

variable {A : Type a} [Ring A]
  {N : Type n} [Fintype N] [DecidableEq N]
  {M : Type m} [Fintype M] [DecidableEq M]
  (U : Matrix N M A) (V : Matrix M N A)

/-- Let A be an arbitrary ring, M,N finite index sets, U an N×M matrix and V an M×N matrix over A.
splitInvolution U V is the (N⊕M)-square block matrix W=[[0,U],[V,I_M−VU]]. Its definition does
not require the relation UV=I_N. -/
def splitInvolution : Matrix (N ⊕ M) (N ⊕ M) A :=
  fromBlocks 0 U V (1 - V * U)
omit [DecidableEq M] in
/-- Let A be an arbitrary ring, M,N finite index sets, U an N×M matrix and V an M×N matrix over A.
If UV=I_N, then (VU)²=VU as an M×M matrix, so VU is idempotent. -/
theorem splitPair_idempotent (h : U * V = 1) : (V * U) * (V * U) = V * U := by
  calc
    _ = V * (U * (V * U)) := Matrix.mul_assoc _ _ _
    _ = V * ((U * V) * U) :=
      congrArg (fun x : Matrix N M A => V * x) (Matrix.mul_assoc U V U).symm
    _ = (V * (U * V)) * U := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [h, Matrix.mul_one]

/-- Let A be an arbitrary ring, M,N finite index sets, U an N×M matrix and V an M×N matrix over A.
Under UV=I_N, one has U(I_M−VU)=0, with the indicated multiplication order. -/
theorem splitPair_right_zero (h : U * V = 1) : U * (1 - V * U) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, Matrix.one_mul, sub_self]

/-- Let A be an arbitrary ring, M,N finite index sets, U an N×M matrix and V an M×N matrix over A.
Under UV=I_N, one has (I_M−VU)V=0. No commutativity assumption on A is needed. -/
theorem splitPair_left_zero (h : U * V = 1) : (1 - V * U) * V = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_one, sub_self]

/-- Let A be an arbitrary ring, M,N finite index sets, U an N×M matrix and V an M×N matrix over A.
If UV=I_N, then VU+(I_M−VU)²=I_M. This is the lower-right block identity in W². -/
theorem splitPair_complement (h : U * V = 1) :
    V * U + (1 - V * U) * (1 - V * U) = 1 := by
  have hp := splitPair_idempotent U V h
  have hq : (1 - V * U) * (1 - V * U) = 1 - V * U := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
      hp, sub_self, sub_zero]
  rw [hq, add_comm, sub_add_cancel]

/-- Let A be an arbitrary ring, M,N finite index sets, U an N×M matrix and V an M×N matrix over A.
If UV=I_N, then W²=I_{N⊕M} for W=[[0,U],[V,I_M−VU]]. This holds over a noncommutative ring A. -/
theorem splitInvolution_mul_self (h : U * V = 1) :
    splitInvolution U V * splitInvolution U V = 1 := by
  rw [splitInvolution, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add]
  rw [h, splitPair_right_zero U V h, splitPair_left_zero U V h,
    splitPair_complement U V h, fromBlocks_one]

/-- Let A be an arbitrary ring, M,N finite index sets, U an N×M matrix and V an M×N matrix over A.
Under UV=I_N, splitInvolutionUnit is the unit of the square matrix ring with both value and
inverse equal to W=[[0,U],[V,I_M−VU]]. -/
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

/-- For a family u:J → A, normalizedRow u is the singleton-by-J matrix with entry (⋆,j)=u(j). -/
def normalizedRow : Matrix PUnit J A := Matrix.of (fun _ j => u j)

/-- For a family v:J → A, normalizedColumn v is the J-by-singleton matrix with entry (j,⋆)=v(j). -/
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

/-- Let A be a ring, J a finite index set and u,v:J → A satisfy ∑ⱼuⱼvⱼ=1. The singleton-by-J row
U=(uⱼ) and J-by-singleton column V=(vᵢ) give the unit W=[[0,U],[V,I_J−VU]] in matrices indexed
by {⋆}⊕J, with W⁻¹=W. The singleton index may occupy a universe independent of J, and no
nonemptiness assumption on J is added. -/
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

/-- Let A be a ring, J an index set and x ∈ A. normalizedFrameCorner x is the matrix on {⋆}⊕J with
the singleton corner equal to x and all other blocks zero: [[x,0],[0,0]]. -/
def normalizedFrameCorner (x : A) : Matrix (PUnit ⊕ J) (PUnit ⊕ J) A :=
  fromBlocks (Matrix.of (fun _ _ : PUnit => x)) 0 0 0

/-- Let A be a ring, J finite and u,v:J → A satisfy ∑ⱼuⱼvⱼ=1. For the associated unit W and x ∈ A,
W⁻¹·corner(x)·W has all blocks zero except the J×J block, whose (i,j)-entry is vᵢxuⱼ. The factor
order is preserved in a noncommutative A. -/
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
