/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Block involutions from split rectangular maps

Let A be a ring, N and M finite index types, U ∈ Mat(N,M;A) and V ∈ Mat(M,N;A). If UV = I_N,
then W = [[0,U],[V,I_M − VU]] satisfies W² = I. For a normalized family ∑ⱼ uⱼvⱼ = 1, this
gives an involution on 1 ⊕ J which conjugates the singleton corner x to the J × J matrix with
entries vᵢ x uⱼ. All formulas retain the displayed order of multiplication.
-/

@[expose] public section

noncomputable section

namespace Matrix

universe a n m t

variable {A : Type a} [Ring A]
  {N : Type n} [Fintype N] [DecidableEq N]
  {M : Type m} [Fintype M] [DecidableEq M]
  (U : Matrix N M A) (V : Matrix M N A)

/-- **The block matrix of a split pair.**

Let A be a ring, N and M finite index types, U ∈ Mat(N,M;A) and V ∈ Mat(M,N;A). Define W =
[[0,U],[V,I_M − VU]] on N ⊕ M. The definition is available before imposing UV = I_N.
-/
def splitInvolution : Matrix (N ⊕ M) (N ⊕ M) A :=
  fromBlocks 0 U V (1 - V * U)
omit [DecidableEq M] in
/-- **Idempotence of the split-pair projection.**

Let A be a ring, N and M finite index types, U ∈ Mat(N,M;A) and V ∈ Mat(M,N;A). If UV = I_N,
then (VU)² = VU.
-/
theorem splitPair_idempotent (h : U * V = 1) : (V * U) * (V * U) = V * U := by
  calc
    _ = V * (U * (V * U)) := Matrix.mul_assoc _ _ _
    _ = V * ((U * V) * U) :=
      congrArg (fun x : Matrix N M A => V * x) (Matrix.mul_assoc U V U).symm
    _ = (V * (U * V)) * U := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [h, Matrix.mul_one]

/-- **The right annihilation identity.**

Let A be a ring, N and M finite index types, U ∈ Mat(N,M;A) and V ∈ Mat(M,N;A). If UV = I_N,
then U(I_M − VU) = 0.
-/
theorem splitPair_right_zero (h : U * V = 1) : U * (1 - V * U) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, Matrix.one_mul, sub_self]

/-- **The left annihilation identity.**

Let A be a ring, N and M finite index types, U ∈ Mat(N,M;A) and V ∈ Mat(M,N;A). If UV = I_N,
then (I_M − VU)V = 0.
-/
theorem splitPair_left_zero (h : U * V = 1) : (1 - V * U) * V = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_one, sub_self]

/-- **The complementary block identity.**

Let A be a ring, N and M finite index types, U ∈ Mat(N,M;A) and V ∈ Mat(M,N;A). If UV = I_N,
then VU + (I_M − VU)² = I_M.
-/
theorem splitPair_complement (h : U * V = 1) :
    V * U + (1 - V * U) * (1 - V * U) = 1 := by
  have hp := splitPair_idempotent U V h
  have hq : (1 - V * U) * (1 - V * U) = 1 - V * U := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
      hp, sub_self, sub_zero]
  rw [hq, add_comm, sub_add_cancel]

/-- **The split-pair matrix is an involution.**

Let A be a ring, N and M finite index types, U ∈ Mat(N,M;A) and V ∈ Mat(M,N;A). If UV = I_N,
the matrix W = [[0,U],[V,I_M − VU]] satisfies W W = I_(N ⊕ M).
-/
theorem splitInvolution_mul_self (h : U * V = 1) :
    splitInvolution U V * splitInvolution U V = 1 := by
  rw [splitInvolution, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add]
  rw [h, splitPair_right_zero U V h, splitPair_left_zero U V h,
    splitPair_complement U V h, fromBlocks_one]

/-- **A matrix unit from a split pair.**

Let A be a ring, N and M finite index types, U ∈ Mat(N,M;A) and V ∈ Mat(M,N;A). Given UV =
I_N, the invertible matrix W = [[0,U],[V,I_M − VU]] has inverse W itself.
-/
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

/-- **The row of a normalized family.**

Let A be a ring, J a finite index type, and u,v : J → A. The singleton row U ∈ Mat(1,J;A) is
U(*,j) = uⱼ.
-/
def normalizedRow : Matrix PUnit J A := Matrix.of (fun _ j => u j)

/-- **The column of a normalized family.**

Let A be a ring, J a finite index type, and u,v : J → A. The singleton column V ∈ Mat(J,1;A)
is V(i,*) = vᵢ.
-/
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

/-- **An involution from a normalized family.**

Let A be a ring, J a finite index type, and u,v : J → A. Assume ∑ⱼ uⱼvⱼ = 1. With U(*,j) = uⱼ
and V(i,*) = vᵢ, the invertible matrix W = [[0,U],[V,I_J − VU]] on 1 ⊕ J satisfies W⁻¹ = W.
The definition also covers an empty J whenever its normalization equation holds.
-/
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

/-- **The singleton matrix corner.**

Let A be a ring, J a finite index type, and u,v : J → A. For x ∈ A, define C(x) on 1 ⊕ J by
C(x) = [[x,0],[0,0]].
-/
def normalizedFrameCorner (x : A) : Matrix (PUnit ⊕ J) (PUnit ⊕ J) A :=
  fromBlocks (Matrix.of (fun _ _ : PUnit => x)) 0 0 0

/-- **Conjugation of the singleton corner.**

Let A be a ring, J a finite index type, and u,v : J → A. Assume ∑ⱼ uⱼvⱼ = 1 and set U(*,j) =
uⱼ, V(i,*) = vᵢ and W = [[0,U],[V,I_J − VU]]. For C(x) = [[x,0],[0,0]], one has W⁻¹ C(x) W =
[[0,0],[0,(vᵢ x uⱼ)ᵢⱼ]].
-/
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
