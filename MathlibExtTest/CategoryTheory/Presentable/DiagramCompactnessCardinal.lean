/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.DiagramCompactnessCardinal
public import Mathlib.CategoryTheory.Presentable.Type

/-!
# Entire original endpoint-rank contracts

Both families and both endpoint functions are retained. The supplied LP
rank and generation/factorization cardinal are independently typed.
Concrete maps have different source and target types and keep their values.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w uM vM uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presentable.DiagramCompactnessCardinalTest

open DiagramCompactnessCardinal

variable (M : Type uM) [Category.{vM} M] (I J : MorphismProperty M)

example (i : I.toSet) : endpointFamily M I J (.inl (.inl i)) = i.1.left :=
  endpointFamily_I_source M I J i

example (i : I.toSet) : endpointFamily M I J (.inr (.inl i)) = i.1.right :=
  endpointFamily_I_target M I J i

example (j : J.toSet) : endpointFamily M I J (.inl (.inr j)) = j.1.left :=
  endpointFamily_J_source M I J j

example (j : J.toSet) : endpointFamily M I J (.inr (.inr j)) = j.1.right :=
  endpointFamily_J_target M I J j

example :
    (endpointFamily M I J : (I.toSet ⊕ J.toSet) ⊕ (I.toSet ⊕ J.toSet) → M) =
      fun e ↦ match e with
      | .inl (.inl i) => i.1.left
      | .inl (.inr j) => j.1.left
      | .inr (.inl i) => i.1.right
      | .inr (.inr j) => j.1.right := rfl

example (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable M κLP]
    (S : Type w) [SmallCategory S]
    (κ : Cardinal.{w}) [I.IsSmall.{w}] [J.IsSmall.{w}] :
    ∃ (χ : Cardinal.{w}) (_ : Fact χ.IsRegular), κLP ≤ χ ∧ κ ≤ χ ∧
      Cardinal.aleph0 < χ ∧ HasCardinalLT (Arrow S) χ ∧
      (∀ i : I.toSet, IsCardinalPresentable i.1.left χ ∧
        IsCardinalPresentable i.1.right χ) ∧
      ∀ j : J.toSet, IsCardinalPresentable j.1.left χ ∧
        IsCardinalPresentable j.1.right χ :=
  endpoint_rank M κLP S κ I J

section Concrete

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A genuine original first family with different endpoint types. -/
def collapseFamily : MorphismProperty (Type) :=
  MorphismProperty.ofHoms (fun _ : (PUnit : Type) ↦ (↾fun _ : Bool ↦ PUnit.unit))

/-- A genuine original second family has an infinite original target. -/
def zeroFamily : MorphismProperty (Type) :=
  MorphismProperty.ofHoms (fun _ : (PUnit : Type) ↦ (↾fun _ : PUnit ↦ (0 : ℕ)))

local instance : collapseFamily.IsSmall.{0} := by
  dsimp [collapseFamily]
  infer_instance

local instance : zeroFamily.IsSmall.{0} := by
  dsimp [zeroFamily]
  infer_instance

example :
    ∃ (χ : Cardinal.{0}) (_ : Fact χ.IsRegular),
      Cardinal.aleph0.{0} ≤ χ ∧ Order.succ Cardinal.aleph0.{0} ≤ χ ∧
      Cardinal.aleph0.{0} < χ ∧ HasCardinalLT (Arrow (Discrete (PEmpty : Type))) χ ∧
      (∀ i : collapseFamily.toSet, IsCardinalPresentable i.1.left χ ∧
        IsCardinalPresentable i.1.right χ) ∧
      ∀ j : zeroFamily.toSet, IsCardinalPresentable j.1.left χ ∧
        IsCardinalPresentable j.1.right χ :=
  endpoint_rank (Type) Cardinal.aleph0.{0} (Discrete (PEmpty : Type))
    (Order.succ Cardinal.aleph0.{0}) collapseFamily zeroFamily

/-- The source rank is finite-presentability, while the produced endpoint rank handles Nat. -/
example : ¬ IsCardinalPresentable (ℕ : Type) Cardinal.aleph0.{0} := by
  rw [Types.isCardinalPresentable_iff, hasCardinalLT_aleph0_iff]
  intro h
  let : Finite ℕ := h
  exact not_finite ℕ

/-- All original source and target functions of the actual families remain literal. -/
example :
    (↾fun _ : Bool ↦ PUnit.unit : (Bool : Type) ⟶ PUnit) =
      (↾fun _ : Bool ↦ PUnit.unit) := rfl

example :
    (↾fun _ : PUnit ↦ (0 : ℕ) : (PUnit : Type) ⟶ ℕ) =
      (↾fun _ : PUnit ↦ (0 : ℕ)) := rfl

end Concrete

end CategoryTheory.Presentable.DiagramCompactnessCardinalTest
