/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AccessibleMorphismProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory

namespace CategoryTheory.MorphismProperty.AccessibleTests

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

example {X Y : C} (f : X ⟶ Y) :
    W.arrowObjectProperty (Arrow.mk f) ↔ W f :=
  Iff.rfl

section Cardinal

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
variable [W.IsCardinalAccessible κ]

example : IsCardinalAccessibleCategory
    W.arrowObjectProperty.FullSubcategory κ :=
  inferInstance

example : Functor.IsCardinalAccessible W.arrowObjectProperty.ι κ :=
  inferInstance

example : W.IsAccessible.{w} where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

example : True := by
  fail_if_success
    have _ : CategoryTheory.MorphismProperty.IsSmall.{w} W := inferInstance
  fail_if_success
    have _ : CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits.{w, w} W :=
      inferInstance
  trivial

end Cardinal

section WrongSubstitutes

variable [CategoryTheory.MorphismProperty.IsSmall.{w} W]

example : True := by
  fail_if_success
    have _ : W.IsAccessible.{w} := inferInstance
  trivial

end WrongSubstitutes

section ClosureOnly

variable [CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits.{w, w} W]

example : True := by
  fail_if_success
    have _ : W.IsAccessible.{w} := inferInstance
  trivial

end ClosureOnly

section UniverseClients

variable {C₁ : Type 1} [Category.{0} C₁]
variable {C₀ : Type} [Category C₀]

example (P : MorphismProperty C₁) : ObjectProperty (Arrow C₁) :=
  P.arrowObjectProperty

example (P : MorphismProperty C₀) : ObjectProperty (Arrow C₀) :=
  P.arrowObjectProperty

end UniverseClients

end CategoryTheory.MorphismProperty.AccessibleTests

#check CategoryTheory.MorphismProperty.arrowObjectProperty
#check CategoryTheory.MorphismProperty.IsCardinalAccessible
#check CategoryTheory.MorphismProperty.IsAccessible

#print axioms CategoryTheory.MorphismProperty.arrowObjectProperty
#print axioms CategoryTheory.MorphismProperty.IsCardinalAccessible
#print axioms CategoryTheory.MorphismProperty.IsAccessible
