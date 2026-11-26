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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ElementarySubgroup
public import Mathlib.Data.Matrix.Block

/-!
# Rectangular block unipotents and their ordered products

Let R be any ring and α,β finite index types. For rectangular A:Matrix α β R and C:Matrix β α
R, put U(A)=[[I_α,A],[0,I_β]] and L(C)=[[I_α,0],[C,I_β]] in GL(α⊕β,R). Their inverses are
U(-A) and L(-C). They lie in the elementary subgroup, as do their finite ordered products. The
block dimensions may differ or be zero.
-/

@[expose] public section

namespace Matrix
namespace GeneralLinearGroup
namespace BlockElementary

open Matrix

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
variable {R : Type*} [Ring R]

/-- **Upper block unipotent matrix.**

Let R be any ring and α,β finite index types. For rectangular A:Matrix α β R and C:Matrix β α
R, put U(A)=[[I_α,A],[0,I_β]] and L(C)=[[I_α,0],[C,I_β]] in GL(α⊕β,R). The element upperUnit A
is U(A), with inverse U(-A), for every rectangular A:Matrix α β R.
-/
def upperUnit (A : Matrix α β R) : GL (α ⊕ β) R where
  val := fromBlocks (1 : Matrix α α R) A (0 : Matrix β α R) (1 : Matrix β β R)
  inv := fromBlocks (1 : Matrix α α R) (-A) (0 : Matrix β α R) (1 : Matrix β β R)
  val_inv := by
    calc fromBlocks (1 : Matrix α α R) A (0 : Matrix β α R) (1 : Matrix β β R) *
          fromBlocks (1 : Matrix α α R) (-A) (0 : Matrix β α R)
            (1 : Matrix β β R)
        = fromBlocks
            ((1 : Matrix α α R) * (1 : Matrix α α R) + A * (0 : Matrix β α R))
            ((1 : Matrix α α R) * (-A) + A * (1 : Matrix β β R))
            ((0 : Matrix β α R) * (1 : Matrix α α R) +
              (1 : Matrix β β R) * (0 : Matrix β α R))
            ((0 : Matrix β α R) * (-A) +
              (1 : Matrix β β R) * (1 : Matrix β β R)) := by
          rw [fromBlocks_multiply]
      _ = fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
            (0 : Matrix β α R) (1 : Matrix β β R) := by simp
      _ = 1 := fromBlocks_one
  inv_val := by
    calc fromBlocks (1 : Matrix α α R) (-A) (0 : Matrix β α R)
            (1 : Matrix β β R) *
          fromBlocks (1 : Matrix α α R) A (0 : Matrix β α R)
            (1 : Matrix β β R)
        = fromBlocks
            ((1 : Matrix α α R) * (1 : Matrix α α R) + (-A) * (0 : Matrix β α R))
            ((1 : Matrix α α R) * A + (-A) * (1 : Matrix β β R))
            ((0 : Matrix β α R) * (1 : Matrix α α R) +
              (1 : Matrix β β R) * (0 : Matrix β α R))
            ((0 : Matrix β α R) * A +
              (1 : Matrix β β R) * (1 : Matrix β β R)) := by
          rw [fromBlocks_multiply]
      _ = fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
            (0 : Matrix β α R) (1 : Matrix β β R) := by simp
      _ = 1 := fromBlocks_one

@[simp]
lemma coe_upperUnit (A : Matrix α β R) :
    (↑(upperUnit A) : Matrix (α ⊕ β) (α ⊕ β) R) =
      fromBlocks (1 : Matrix α α R) A (0 : Matrix β α R) (1 : Matrix β β R) :=
  rfl

@[simp]
theorem upperUnit_zero : upperUnit (0 : Matrix α β R) = 1 := by
  apply Units.ext
  simp [coe_upperUnit, fromBlocks_one]

theorem upperUnit_add (A B : Matrix α β R) :
    upperUnit (A + B) = upperUnit A * upperUnit B := by
  have h_prod :
      fromBlocks (1 : Matrix α α R) A (0 : Matrix β α R) (1 : Matrix β β R) *
        fromBlocks (1 : Matrix α α R) B (0 : Matrix β α R) (1 : Matrix β β R) =
        fromBlocks (1 : Matrix α α R) (A + B) (0 : Matrix β α R)
          (1 : Matrix β β R) := by
    calc fromBlocks (1 : Matrix α α R) A (0 : Matrix β α R)
            (1 : Matrix β β R) *
          fromBlocks (1 : Matrix α α R) B (0 : Matrix β α R)
            (1 : Matrix β β R)
        = fromBlocks
            ((1 : Matrix α α R) * (1 : Matrix α α R) + A * (0 : Matrix β α R))
            ((1 : Matrix α α R) * B + A * (1 : Matrix β β R))
            ((0 : Matrix β α R) * (1 : Matrix α α R) +
              (1 : Matrix β β R) * (0 : Matrix β α R))
            ((0 : Matrix β α R) * B +
              (1 : Matrix β β R) * (1 : Matrix β β R)) := by
          rw [fromBlocks_multiply]
      _ = fromBlocks (1 : Matrix α α R) (B + A) (0 : Matrix β α R)
            (1 : Matrix β β R) := by simp
      _ = fromBlocks (1 : Matrix α α R) (A + B) (0 : Matrix β α R)
            (1 : Matrix β β R) := by rw [add_comm]
  apply Units.ext
  calc (↑(upperUnit (A + B)) : Matrix (α ⊕ β) (α ⊕ β) R)
      = fromBlocks (1 : Matrix α α R) (A + B) (0 : Matrix β α R)
          (1 : Matrix β β R) := rfl
    _ = fromBlocks (1 : Matrix α α R) A (0 : Matrix β α R) (1 : Matrix β β R) *
          fromBlocks (1 : Matrix α α R) B (0 : Matrix β α R)
            (1 : Matrix β β R) := h_prod.symm
    _ = (↑(upperUnit A) : Matrix (α ⊕ β) (α ⊕ β) R) *
          (↑(upperUnit B) : Matrix (α ⊕ β) (α ⊕ β) R) := by
        rw [coe_upperUnit, coe_upperUnit]
    _ = (↑(upperUnit A * upperUnit B) : Matrix (α ⊕ β) (α ⊕ β) R) := rfl

theorem upperUnit_single (i : α) (j : β) (a : R) :
    upperUnit (Matrix.single i j a) =
      _root_.Matrix.GeneralLinearGroup.elementary
        (Sum.inl (α := α) (β := β) i) (Sum.inr (α := α) (β := β) j)
        Sum.inl_ne_inr a := by
  apply Units.ext
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [coe_upperUnit,
      _root_.Matrix.GeneralLinearGroup.coe_elementary, fromBlocks,
      Matrix.single, Matrix.one_apply, Matrix.add_apply]

/-- **Lower block unipotent matrix.**

Let R be any ring and α,β finite index types. For rectangular A:Matrix α β R and C:Matrix β α
R, put U(A)=[[I_α,A],[0,I_β]] and L(C)=[[I_α,0],[C,I_β]] in GL(α⊕β,R). The element lowerUnit C
is L(C), with inverse L(-C), for every rectangular C:Matrix β α R.
-/
def lowerUnit (A : Matrix β α R) : GL (α ⊕ β) R where
  val := fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) A (1 : Matrix β β R)
  inv := fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) (-A) (1 : Matrix β β R)
  val_inv := by
    calc fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) A
            (1 : Matrix β β R) *
          fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) (-A)
            (1 : Matrix β β R)
        = fromBlocks
            ((1 : Matrix α α R) * (1 : Matrix α α R) +
              (0 : Matrix α β R) * (-A))
            ((1 : Matrix α α R) * (0 : Matrix α β R) +
              (0 : Matrix α β R) * (1 : Matrix β β R))
            (A * (1 : Matrix α α R) + (1 : Matrix β β R) * (-A))
            (A * (0 : Matrix α β R) +
              (1 : Matrix β β R) * (1 : Matrix β β R)) := by
          rw [fromBlocks_multiply]
      _ = fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
            (0 : Matrix β α R) (1 : Matrix β β R) := by simp
      _ = 1 := fromBlocks_one
  inv_val := by
    calc fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) (-A)
            (1 : Matrix β β R) *
          fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) A
            (1 : Matrix β β R)
        = fromBlocks
            ((1 : Matrix α α R) * (1 : Matrix α α R) +
              (0 : Matrix α β R) * A)
            ((1 : Matrix α α R) * (0 : Matrix α β R) +
              (0 : Matrix α β R) * (1 : Matrix β β R))
            ((-A) * (1 : Matrix α α R) + (1 : Matrix β β R) * A)
            ((-A) * (0 : Matrix α β R) +
              (1 : Matrix β β R) * (1 : Matrix β β R)) := by
          rw [fromBlocks_multiply]
      _ = fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
            (0 : Matrix β α R) (1 : Matrix β β R) := by simp
      _ = 1 := fromBlocks_one

@[simp]
lemma coe_lowerUnit (A : Matrix β α R) :
    (↑(lowerUnit A) : Matrix (α ⊕ β) (α ⊕ β) R) =
      fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) A (1 : Matrix β β R) :=
  rfl

@[simp]
theorem lowerUnit_zero : lowerUnit (0 : Matrix β α R) = 1 := by
  apply Units.ext
  simp [coe_lowerUnit, fromBlocks_one]

theorem lowerUnit_add (A B : Matrix β α R) :
    lowerUnit (A + B) = lowerUnit A * lowerUnit B := by
  have h_prod :
      fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) A
          (1 : Matrix β β R) *
        fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) B
          (1 : Matrix β β R) =
        fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) (A + B)
          (1 : Matrix β β R) := by
    calc fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) A
            (1 : Matrix β β R) *
          fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) B
            (1 : Matrix β β R)
        = fromBlocks
            ((1 : Matrix α α R) * (1 : Matrix α α R) +
              (0 : Matrix α β R) * B)
            ((1 : Matrix α α R) * (0 : Matrix α β R) +
              (0 : Matrix α β R) * (1 : Matrix β β R))
            (A * (1 : Matrix α α R) + (1 : Matrix β β R) * B)
            (A * (0 : Matrix α β R) + (1 : Matrix β β R) * (1 : Matrix β β R)) := by
          rw [fromBlocks_multiply]
      _ = fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) (A + B)
            (1 : Matrix β β R) := by simp
  apply Units.ext
  calc (↑(lowerUnit (A + B)) : Matrix (α ⊕ β) (α ⊕ β) R)
      = fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) (A + B)
          (1 : Matrix β β R) := rfl
    _ = fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) A
            (1 : Matrix β β R) *
          fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) B
            (1 : Matrix β β R) := h_prod.symm
    _ = (↑(lowerUnit A) : Matrix (α ⊕ β) (α ⊕ β) R) *
          (↑(lowerUnit B) : Matrix (α ⊕ β) (α ⊕ β) R) := by
        rw [coe_lowerUnit, coe_lowerUnit]
    _ = (↑(lowerUnit A * lowerUnit B) : Matrix (α ⊕ β) (α ⊕ β) R) := rfl

theorem lowerUnit_single (i : β) (j : α) (a : R) :
    lowerUnit (Matrix.single i j a) =
      _root_.Matrix.GeneralLinearGroup.elementary
        (Sum.inr (α := α) (β := β) i) (Sum.inl (α := α) (β := β) j)
        Sum.inr_ne_inl a := by
  apply Units.ext
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [coe_lowerUnit,
      _root_.Matrix.GeneralLinearGroup.coe_elementary, fromBlocks,
      Matrix.single, Matrix.one_apply, Matrix.add_apply]

theorem upperUnit_mem_elementarySubgroup (A : Matrix α β R) :
    upperUnit A ∈
      _root_.Matrix.GeneralLinearGroup.elementarySubgroup (α ⊕ β) R := by
  let P : Matrix α β R → Prop := fun M =>
    upperUnit M ∈ _root_.Matrix.GeneralLinearGroup.elementarySubgroup (α ⊕ β) R
  have h_zero : P 0 := by
    dsimp [P]
    rw [upperUnit_zero]
    exact Subgroup.one_mem _
  have h_add : ∀ p q, P p → P q → P (p + q) := by
    intro p q hp hq
    dsimp [P] at hp hq ⊢
    have h_eq : upperUnit (p + q) = upperUnit p * upperUnit q :=
      upperUnit_add p q
    rw [h_eq]
    exact Subgroup.mul_mem _ hp hq
  have h_single : ∀ i j a, P (Matrix.single i j a) := by
    intro i j a
    dsimp [P]
    rw [upperUnit_single]
    exact _root_.Matrix.GeneralLinearGroup.elementary_mem_elementarySubgroup
      _ _ _ _
  exact Matrix.induction_on' A h_zero h_add h_single

theorem lowerUnit_mem_elementarySubgroup (A : Matrix β α R) :
    lowerUnit A ∈
      _root_.Matrix.GeneralLinearGroup.elementarySubgroup (α ⊕ β) R := by
  let P : Matrix β α R → Prop := fun M =>
    lowerUnit M ∈ _root_.Matrix.GeneralLinearGroup.elementarySubgroup (α ⊕ β) R
  have h_zero : P 0 := by
    dsimp [P]
    rw [lowerUnit_zero]
    exact Subgroup.one_mem _
  have h_add : ∀ p q, P p → P q → P (p + q) := by
    intro p q hp hq
    dsimp [P] at hp hq ⊢
    have h_eq : lowerUnit (p + q) = lowerUnit p * lowerUnit q :=
      lowerUnit_add p q
    rw [h_eq]
    exact Subgroup.mul_mem _ hp hq
  have h_single : ∀ i j a, P (Matrix.single i j a) := by
    intro i j a
    dsimp [P]
    rw [lowerUnit_single]
    exact _root_.Matrix.GeneralLinearGroup.elementary_mem_elementarySubgroup
      _ _ _ _
  exact Matrix.induction_on' A h_zero h_add h_single

/-- **Ordered product of upper and lower block unipotents.**

Let R be any ring and α,β finite index types. For rectangular A:Matrix α β R and C:Matrix β α
R, put U(A)=[[I_α,A],[0,I_β]] and L(C)=[[I_α,0],[C,I_β]] in GL(α⊕β,R). For a list ℒ of either
α×β or β×α matrices, blockAltProd ℒ replaces a left-tagged A by U(A) and a right-tagged C by
L(C), then multiplies in list order. Thus blockAltProd []=I and
blockAltProd(a::ℒ)=E(a)*blockAltProd ℒ, where E selects U or L. Consecutive factors may have
the same tag.
-/
noncomputable def blockAltProd
    (L : List (Matrix α β R ⊕ Matrix β α R)) : GL (α ⊕ β) R :=
  (L.map (Sum.elim upperUnit lowerUnit)).prod

@[simp]
theorem blockAltProd_nil :
    blockAltProd ([] : List (Matrix α β R ⊕ Matrix β α R)) = 1 := rfl

theorem blockAltProd_cons_inl
    (A : Matrix α β R) (L : List (Matrix α β R ⊕ Matrix β α R)) :
    (↑(blockAltProd (Sum.inl A :: L)) : Matrix (α ⊕ β) (α ⊕ β) R) =
      fromBlocks
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₁ +
          A * (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₁)
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₂ +
          A * (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₂)
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₁)
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₂) := by
  have h_prod : blockAltProd (Sum.inl A :: L) = upperUnit A * blockAltProd L := by
    simp [blockAltProd]
  calc (↑(blockAltProd (Sum.inl A :: L)) : Matrix (α ⊕ β) (α ⊕ β) R)
      = (↑(upperUnit A * blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R) := by
        rw [h_prod]
    _ = (↑(upperUnit A) : Matrix (α ⊕ β) (α ⊕ β) R) *
        (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R) := rfl
    _ = fromBlocks (1 : Matrix α α R) A (0 : Matrix β α R)
          (1 : Matrix β β R) *
        (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R) := by
        rw [coe_upperUnit]
    _ = fromBlocks (1 : Matrix α α R) A (0 : Matrix β α R)
          (1 : Matrix β β R) *
        fromBlocks ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₁)
          ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₂)
          ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₁)
          ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₂) := by
        conv => lhs; rw [(Matrix.fromBlocks_toBlocks
            (M := (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R))).symm]
    _ = fromBlocks
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₁ +
          A * (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₁)
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₂ +
          A * (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₂)
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₁)
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₂) := by
        rw [Matrix.fromBlocks_multiply]
        simp

theorem blockAltProd_cons_inr
    (C : Matrix β α R) (L : List (Matrix α β R ⊕ Matrix β α R)) :
    (↑(blockAltProd (Sum.inr C :: L)) : Matrix (α ⊕ β) (α ⊕ β) R) =
      fromBlocks
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₁)
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₂)
        (C * (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₁ +
          (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₁)
        (C * (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₂ +
          (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₂) := by
  have h_prod : blockAltProd (Sum.inr C :: L) = lowerUnit C * blockAltProd L := by
    simp [blockAltProd]
  calc (↑(blockAltProd (Sum.inr C :: L)) : Matrix (α ⊕ β) (α ⊕ β) R)
      = (↑(lowerUnit C * blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R) := by
        rw [h_prod]
    _ = (↑(lowerUnit C) : Matrix (α ⊕ β) (α ⊕ β) R) *
        (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R) := rfl
    _ = fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) C
          (1 : Matrix β β R) *
        (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R) := by
        rw [coe_lowerUnit]
    _ = fromBlocks (1 : Matrix α α R) (0 : Matrix α β R) C
          (1 : Matrix β β R) *
        fromBlocks ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₁)
          ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₂)
          ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₁)
          ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₂) := by
        conv => lhs; rw [(Matrix.fromBlocks_toBlocks
            (M := (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R))).symm]
    _ = fromBlocks
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₁)
        ((↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₂)
        (C * (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₁ +
          (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₁)
        (C * (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₂ +
          (↑(blockAltProd L) : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₂) := by
        rw [Matrix.fromBlocks_multiply]
        simp

end BlockElementary
end GeneralLinearGroup
end Matrix
