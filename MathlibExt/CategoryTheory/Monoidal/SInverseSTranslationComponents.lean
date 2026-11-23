/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationAction

/-!
# Residual translations on group-completion components

Under the Grothendieck-difference classification of connected components,
translation in the first coordinate adds the translating class and
translation in the second coordinate subtracts it.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject Algebra

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- First-coordinate translation adds the translating class to the
Grothendieck difference. -/
@[simp]
theorem Pair.difference_translateFirstObj (A : C) (X : Pair C) :
    (translateFirstObj A X).difference =
      GrothendieckAddGroup.of (toSkeleton A) + X.difference := by
  unfold Pair.difference translateFirstObj
  rw [Skeleton.toSkeleton_biprod, map_add]
  abel

/-- Second-coordinate translation subtracts the translating class from the
Grothendieck difference. -/
@[simp]
theorem Pair.difference_translateSecondObj (A : C) (X : Pair C) :
    (translateSecondObj A X).difference =
      X.difference - GrothendieckAddGroup.of (toSkeleton A) := by
  unfold Pair.difference translateSecondObj
  rw [Skeleton.toSkeleton_biprod, map_add]
  abel

/-- On connected components, first-coordinate translation is addition by
the translating Grothendieck class. -/
theorem connectedComponentsToGrothendieck_mapConnectedComponents_translateFirst
    (A : C) (x : ConnectedComponents (Pair C)) :
    connectedComponentsToGrothendieck
        ((translateFirstFunctor A).mapConnectedComponents x) =
      GrothendieckAddGroup.of (toSkeleton A) +
        connectedComponentsToGrothendieck x := by
  induction x using Quotient.inductionOn with
  | _ X => exact Pair.difference_translateFirstObj A X

/-- On connected components, second-coordinate translation is subtraction
by the translating Grothendieck class. -/
theorem connectedComponentsToGrothendieck_mapConnectedComponents_translateSecond
    (A : C) (x : ConnectedComponents (Pair C)) :
    connectedComponentsToGrothendieck
        ((translateSecondFunctor A).mapConnectedComponents x) =
      connectedComponentsToGrothendieck x -
        GrothendieckAddGroup.of (toSkeleton A) := by
  induction x using Quotient.inductionOn with
  | _ X => exact Pair.difference_translateSecondObj A X

/-- Translation to zero subtracts the selected object's Grothendieck
difference from every component. -/
theorem connectedComponentsToGrothendieck_mapConnectedComponents_translateToZero
    (X : Pair C) (x : ConnectedComponents (Pair C)) :
    connectedComponentsToGrothendieck
        ((translateToZeroFunctor X).mapConnectedComponents x) =
      connectedComponentsToGrothendieck x - X.difference := by
  induction x using Quotient.inductionOn with
  | _ Y =>
      change
        (translateFirstObj X.snd
          (translateSecondObj X.fst Y)).difference =
          Y.difference - X.difference
      rw [Pair.difference_translateFirstObj,
        Pair.difference_translateSecondObj]
      unfold Pair.difference
      abel

/-- The chosen object's component is sent to the zero Grothendieck
component. -/
theorem translateToZeroFunctor_selected_component (X : Pair C) :
    connectedComponentsToGrothendieck
        ((translateToZeroFunctor X).mapConnectedComponents
          (ConnectedComponents.mk X)) = 0 := by
  rw [connectedComponentsToGrothendieck_mapConnectedComponents_translateToZero,
    connectedComponentsToGrothendieck_mk, sub_self]

end SInverseS
end CategoryTheory

end
