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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialCofree
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Split transitions of injective inverse sequences

Let C have finite products and zero morphisms. An injective inverse sequence
splits its cofree unit as a morphism of diagrams. Naturality transfers the
sections of the cofree transitions to sections of its own successor
transitions. The assumption concerns the given sequence's injectivity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe u v

variable (C : Type u) [Category.{v} C] [HasFiniteProducts C]
variable (J : ℕᵒᵖ ⥤ C) [Injective J]

/-- Injectivity supplies a genuinely natural retraction of the cofree unit. -/
def sequentialInjectiveCofreeRetraction :
    (sequentialCofreeFunctor C).obj J ⟶ J :=
  Injective.factorThru (𝟙 J) ((sequentialCofreeUnit C).app J)

/-- The injective factorization retracts the unit as a morphism of diagrams. -/
theorem sequentialInjectiveCofreeUnit_retraction :
    (sequentialCofreeUnit C).app J ≫ sequentialInjectiveCofreeRetraction C J = 𝟙 J :=
  Injective.comp_factorThru (𝟙 J) ((sequentialCofreeUnit C).app J)

variable [HasZeroMorphisms C]

/-- The cofree transition section transports through the natural retraction. -/
def sequentialInjectiveTransitionSection (n : ℕ) :
    J.obj (op n) ⟶ J.obj (op (n + 1)) :=
  ((sequentialCofreeUnit C).app J).app (op n) ≫
    sequentialCofreeTransitionSection C J n ≫
      (sequentialInjectiveCofreeRetraction C J).app (op (n + 1))

/-- Every transition of an injective sequential diagram is split epimorphic. -/
def sequentialInjectiveTransitionSplitEpi (n : ℕ) :
    SplitEpi (J.map (homOfLE (Nat.le_succ n)).op) where
  section_ := sequentialInjectiveTransitionSection C J n
  id := by
    have hunit := congr_app (sequentialInjectiveCofreeUnit_retraction C J) (op n)
    simp only [NatTrans.comp_app, NatTrans.id_app, Functor.id_obj] at hunit
    have hco : sequentialCofreeTransitionSection C J n ≫
        ((sequentialCofreeFunctor C).obj J).map (homOfLE (Nat.le_succ n)).op =
        𝟙 (((sequentialCofreeFunctor C).obj J).obj (op n)) :=
      (sequentialCofreeTransitionSplitEpi C J n).id
    simp only [sequentialInjectiveTransitionSection, Category.assoc]
    rw [← (sequentialInjectiveCofreeRetraction C J).naturality]
    rw [← Category.assoc (sequentialCofreeTransitionSection C J n)
      (((sequentialCofreeFunctor C).obj J).map (homOfLE (Nat.le_succ n)).op)
      ((sequentialInjectiveCofreeRetraction C J).app (op n)),
      hco, Category.id_comp]
    exact hunit

/-- Finite products and zero morphisms make every successor transition of an injective inverse
sequence a split epimorphism. -/
instance sequentialInjectiveTransitionIsSplitEpi (n : ℕ) :
    IsSplitEpi (J.map (homOfLE (Nat.le_succ n)).op) :=
  IsSplitEpi.mk' (sequentialInjectiveTransitionSplitEpi C J n)

end CategoryTheory.Limits
