/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.NatTrans.TerminalArrow

@[expose] public section

noncomputable section

namespace CategoryTheory.Limits.TerminalArrowTest

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasTerminal C] [HasInitial C]

example (X : C) : (terminal.fromNatTrans C).app X = terminal.from X := by simp

example (X : C) : (initial.toNatTrans C).app X = initial.to X := by simp

example (X : C) :
    ((terminal.arrowFunctor C).obj X).left = X ∧
      ((terminal.arrowFunctor C).obj X).right = (⊤_ C) ∧
      ((terminal.arrowFunctor C).obj X).hom = terminal.from X := by simp

example {X Y : C} (f : X ⟶ Y) :
    ((terminal.arrowFunctor C).map f).left = f ∧
      ((terminal.arrowFunctor C).map f).right = 𝟙 (⊤_ C) := by simp

example (X : C) :
    ((initial.arrowFunctor C).obj X).left = (⊥_ C) ∧
      ((initial.arrowFunctor C).obj X).right = X ∧
      ((initial.arrowFunctor C).obj X).hom = initial.to X := by simp

example {X Y : C} (f : X ⟶ Y) :
    ((initial.arrowFunctor C).map f).left = 𝟙 (⊥_ C) ∧
      ((initial.arrowFunctor C).map f).right = f := by simp

variable {D : Type u₂} [Category.{v₂} D] [HasTerminal D] [HasInitial D]
variable (F : C ⥤ D)

example (X : C) :
    ((terminal.arrowFunctorComparisonNatTrans F).app X).left = 𝟙 (F.obj X) ∧
      ((terminal.arrowFunctorComparisonNatTrans F).app X).right =
        terminalComparison F := by simp

example (X : C) :
    ((initial.arrowFunctorComparisonNatTrans F).app X).left = initialComparison F ∧
      ((initial.arrowFunctorComparisonNatTrans F).app X).right = 𝟙 (F.obj X) := by simp

section Preserves

variable [PreservesLimit (Functor.empty.{0} C) F]
    [PreservesColimit (Functor.empty.{0} C) F]

example : (terminal.arrowFunctorComparisonNatIso F).hom =
    terminal.arrowFunctorComparisonNatTrans F := by simp

example (X : C) :
    ((terminal.arrowFunctorComparisonNatIso F).hom.app X).left = 𝟙 (F.obj X) ∧
      ((terminal.arrowFunctorComparisonNatIso F).hom.app X).right =
        (PreservesTerminal.iso F).hom ∧
      ((terminal.arrowFunctorComparisonNatIso F).inv.app X).left = 𝟙 (F.obj X) ∧
      ((terminal.arrowFunctorComparisonNatIso F).inv.app X).right =
        (PreservesTerminal.iso F).inv := by simp

example : (initial.arrowFunctorComparisonNatIso F).hom =
    initial.arrowFunctorComparisonNatTrans F := by simp

example (X : C) :
    ((initial.arrowFunctorComparisonNatIso F).hom.app X).left =
        (PreservesInitial.iso F).inv ∧
      ((initial.arrowFunctorComparisonNatIso F).hom.app X).right = 𝟙 (F.obj X) ∧
      ((initial.arrowFunctorComparisonNatIso F).inv.app X).left =
        (PreservesInitial.iso F).hom ∧
      ((initial.arrowFunctorComparisonNatIso F).inv.app X).right = 𝟙 (F.obj X) := by simp

end Preserves

end CategoryTheory.Limits.TerminalArrowTest
