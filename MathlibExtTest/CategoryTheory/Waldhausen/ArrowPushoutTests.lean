/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.ArrowPushout
import MathlibExt.CategoryTheory.Waldhausen.Exact

/-!
# Tests for pointwise Waldhausen pushouts in the arrow category

These clients pin the independent universes, component and Arrow pushout
orientations, cocone equations, universal property, and pointwise cobase
cofibration.  The private `Exact` import is used only for one abstract
universe-zero exact-category client; production uses no exact-category
pushout API.

The production module inlines the probe's `Nonempty` construction locally in
the selected constructor because a public transparent definition cannot
depend on a module-private declaration.  No helper is exposed by that
packaging adjustment.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen
namespace ArrowPushoutTests

section AbstractExactCategoryTypeZero

variable (C : Type) [Category.{0} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

local instance abstractExactWaldhausenCategory : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

private theorem abstractExactCategoryClient
    {X Y Z : Arrow C} (i : X ⟶ Y) (g : X ⟶ Z)
    (hi : arrowCofibrations C i) :
    ∃ P : ArrowPushoutPresentation C i g,
      IsPushout g i P.inl P.inr := by
  let P := ArrowPushoutPresentation.ofPointwiseCofibration i g hi
  exact ⟨P, P.isPushout⟩

end AbstractExactCategoryTypeZero

end ArrowPushoutTests
end MathlibExtTest.CategoryTheory.Waldhausen

@[expose] public section

namespace MathlibExtTest.CategoryTheory.Waldhausen
namespace ArrowPushoutTests

section Symbolic

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]
variable {X Y Z : Arrow C}

example (i : X ⟶ Y) (g : X ⟶ Z) : Type (max u v) :=
  ArrowPushoutPresentation C i g

example (i : X ⟶ Y) (g : X ⟶ Z)
    (hi : arrowCofibrations C i) :
    ArrowPushoutPresentation C i g :=
  ArrowPushoutPresentation.ofPointwiseCofibration i g hi

example (i : X ⟶ Y) (g : X ⟶ Z)
    (P : ArrowPushoutPresentation C i g) :
    IsPushout g.left i.left P.inl.left P.inr.left :=
  P.isPushout_left

example (i : X ⟶ Y) (g : X ⟶ Z)
    (P : ArrowPushoutPresentation C i g) :
    IsPushout g.right i.right P.inl.right P.inr.right :=
  P.isPushout_right

example (i : X ⟶ Y) (g : X ⟶ Z)
    (P : ArrowPushoutPresentation C i g) :
    IsPushout g i P.inl P.inr :=
  P.isPushout

example (i : X ⟶ Y) (g : X ⟶ Z)
    (P : ArrowPushoutPresentation C i g) :
    P.inl.left ≫ P.apex.hom = Z.hom ≫ P.inl.right :=
  P.inl.w

example (i : X ⟶ Y) (g : X ⟶ Z)
    (P : ArrowPushoutPresentation C i g) :
    P.inr.left ≫ P.apex.hom = Y.hom ≫ P.inr.right :=
  P.inr.w

example (i : X ⟶ Y) (g : X ⟶ Z)
    (P : ArrowPushoutPresentation C i g)
    (T : Arrow C) (a : Z ⟶ T) (b : Y ⟶ T)
    (h : g ≫ a = i ≫ b) :
    ∃ d : P.apex ⟶ T, P.inl ≫ d = a ∧ P.inr ≫ d = b := by
  let d := P.isPushout.desc a b h
  refine ⟨d, ?_, ?_⟩
  · exact P.isPushout.inl_desc a b h
  · exact P.isPushout.inr_desc a b h

example (i : X ⟶ Y) (g : X ⟶ Z)
    (P : ArrowPushoutPresentation C i g)
    (T : Arrow C) (d d' : P.apex ⟶ T)
    (hZd : P.inl ≫ d = P.inl ≫ d')
    (hYd : P.inr ≫ d = P.inr ≫ d') : d = d' := by
  exact P.isPushout.hom_ext hZd hYd

example (i : X ⟶ Y) (g : X ⟶ Z)
    (P : ArrowPushoutPresentation C i g) :
    IsCofibration P.inl.left :=
  P.inl_cofibration.1

example (i : X ⟶ Y) (g : X ⟶ Z)
    (P : ArrowPushoutPresentation C i g) :
    IsCofibration P.inl.right :=
  P.inl_cofibration.2

example (X : Arrow C) :
    ∃ P : ArrowPushoutPresentation C (𝟙 X) (𝟙 X),
      IsPushout (𝟙 X) (𝟙 X) P.inl P.inr := by
  have hi : arrowCofibrations C (𝟙 X) :=
    (arrowCofibrations C).id_mem X
  let P := ArrowPushoutPresentation.ofPointwiseCofibration
    (𝟙 X) (𝟙 X) hi
  exact ⟨P, P.isPushout⟩

example :
    ∃ P : ArrowPushoutPresentation C
        (𝟙 (arrowZero C)) (𝟙 (arrowZero C)),
      IsPushout (𝟙 (arrowZero C)) (𝟙 (arrowZero C)) P.inl P.inr := by
  have hi : arrowCofibrations C (𝟙 (arrowZero C)) :=
    (arrowCofibrations C).id_mem (arrowZero C)
  let P := ArrowPushoutPresentation.ofPointwiseCofibration
    (𝟙 (arrowZero C)) (𝟙 (arrowZero C)) hi
  exact ⟨P, P.isPushout⟩

end Symbolic

section InstanceAndScopeGuards

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

#guard_msgs (error, substring := true) in
#synth HasPushouts (Arrow C)

#guard_msgs (error, substring := true) in
#synth WaldhausenCategoryWithoutGluing (Arrow C)

#guard_msgs (error, substring := true) in
#synth WaldhausenCategoryWithoutGluing (CofibrationArrow C)

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.ArrowPushoutPresentation.nonempty_of_pointwise

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.ArrowPushoutPresentation.apex_isCofibration

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.ArrowPushoutPresentation.inl_isRelativeCofibration

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.CofibrationArrowPushoutPresentation

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.arrowWaldhausenCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.cofibrationArrowWaldhausenCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.WaldhausenCylinder

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.ArrowPushoutPresentation.stage

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.ArrowPushoutPresentation.approximation

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.ArrowPushoutPresentation.kTheoryEquivalence

end InstanceAndScopeGuards

#print axioms CategoryTheory.Waldhausen.ArrowPushoutPresentation
#print axioms CategoryTheory.Waldhausen.ArrowPushoutPresentation.ofPointwiseCofibration
#print axioms CategoryTheory.Waldhausen.ArrowPushoutPresentation.isPushout

end ArrowPushoutTests
end MathlibExtTest.CategoryTheory.Waldhausen

end
