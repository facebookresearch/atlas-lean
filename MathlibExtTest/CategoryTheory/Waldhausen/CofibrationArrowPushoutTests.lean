/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.CofibrationArrowPushout

import MathlibExt.CategoryTheory.Waldhausen.Exact

/-!
# Tests for pushouts of Waldhausen cofibration arrows

These clients pin the two component pushouts, literal lifted pushout, apex
cofibration, relative cobase leg, descents and uniqueness. They install no
global pushout, Waldhausen, gluing, cylinder, Stage, or Approximation data.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen
namespace CofibrationArrowPushoutTests

section TypeZeroExact

variable (D : Type) [Category.{0} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]

local instance : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

private theorem exactClient
    {X Y Z : CofibrationArrow D} (i : X ⟶ Y) (g : X ⟶ Z)
    (hi : IsRelativeCofibration D i) :
    ∃ P : CofibrationArrowPushoutPresentation D i g,
      IsPushout g i P.inl P.inr ∧ IsRelativeCofibration D P.inl := by
  let P := CofibrationArrowPushoutPresentation.ofRelativeCofibration i g hi
  exact ⟨P, P.isPushout, P.inl_relative⟩

end TypeZeroExact

end CofibrationArrowPushoutTests
end MathlibExtTest.CategoryTheory.Waldhausen

@[expose] public section

namespace MathlibExtTest.CategoryTheory.Waldhausen
namespace CofibrationArrowPushoutTests

section Symbolic

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]
variable {X Y Z T : CofibrationArrow C}
variable (i : X ⟶ Y) (g : X ⟶ Z)

example : Type (max u v) :=
  CofibrationArrowPushoutPresentation C i g

example (hi : IsRelativeCofibration C i) :
    CofibrationArrowPushoutPresentation C i g :=
  CofibrationArrowPushoutPresentation.ofRelativeCofibration i g hi

variable (P : CofibrationArrowPushoutPresentation C i g)

example : IsCofibration P.apex.hom :=
  P.apex.prop

example : IsPushout g.left i.left P.inl.left P.inr.left :=
  P.isPushout_left

example : IsPushout g.right i.right P.inl.right P.inr.right :=
  P.isPushout_right

example : IsPushout g i P.inl P.inr :=
  P.isPushout

example : P.inl.left ≫ P.apex.hom = Z.hom ≫ P.inl.right :=
  P.inl.w

example : P.inr.left ≫ P.apex.hom = Y.hom ≫ P.inr.right :=
  P.inr.w

example : IsRelativeCofibration C P.inl :=
  P.inl_relative

example : IsCofibration P.inl.left ∧ IsCofibration P.inl.right :=
  P.inl_relative.pointwise C

example :
    ∃ (R : C) (inB : Z.right ⟶ R) (inA : P.apex.left ⟶ R)
      (d : R ⟶ P.apex.right),
      IsPushout Z.hom P.inl.left inB inA ∧
        inB ≫ d = P.inl.right ∧
        inA ≫ d = P.apex.hom ∧
        IsCofibration d :=
  P.inl_relative.2

example (a : Z ⟶ T) (b : Y ⟶ T) (hab : g ≫ a = i ≫ b) :
    ∃ d : P.apex ⟶ T, P.inl ≫ d = a ∧ P.inr ≫ d = b := by
  let d := P.isPushout.desc a b hab
  exact ⟨d, P.isPushout.inl_desc _ _ _, P.isPushout.inr_desc _ _ _⟩

example (d d' : P.apex ⟶ T)
    (hl : P.inl ≫ d = P.inl ≫ d')
    (hr : P.inr ≫ d = P.inr ≫ d') : d = d' :=
  P.isPushout.hom_ext hl hr

end Symbolic

section Boundaries

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]
variable {X Z : CofibrationArrow C}

example (g : X ⟶ Z) :
    CofibrationArrowPushoutPresentation C (𝟙 X) g :=
  CofibrationArrowPushoutPresentation.ofRelativeCofibration
    (𝟙 X) g (IsRelativeCofibration.id C X)

example :
    CofibrationArrowPushoutPresentation C
      (𝟙 (cofibrationArrowZero C)) (𝟙 (cofibrationArrowZero C)) :=
  CofibrationArrowPushoutPresentation.ofRelativeCofibration
    (𝟙 (cofibrationArrowZero C)) (𝟙 (cofibrationArrowZero C))
    (IsRelativeCofibration.id C (cofibrationArrowZero C))

end Boundaries

section SurfaceAndNonclaims

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

#check CofibrationArrowPushoutPresentation
#check CofibrationArrowPushoutPresentation.mk
#check CofibrationArrowPushoutPresentation.apex
#check CofibrationArrowPushoutPresentation.inl
#check CofibrationArrowPushoutPresentation.inr
#check CofibrationArrowPushoutPresentation.isPushout_left
#check CofibrationArrowPushoutPresentation.isPushout_right
#check CofibrationArrowPushoutPresentation.inl_relative
#check CofibrationArrowPushoutPresentation.ofRelativeCofibration
#check CofibrationArrowPushoutPresentation.isPushout

#guard_msgs (error, substring := true) in
#synth HasPushouts (CofibrationArrow C)

#guard_msgs (error, substring := true) in
#synth WaldhausenCategoryWithoutGluing (CofibrationArrow C)

#guard_msgs (error, substring := true) in
#check CofibrationArrowPushoutPresentation.nonempty_of_relative

#guard_msgs (error, substring := true) in
#check CofibrationArrowPushoutPresentation.apex_isCofibration

#guard_msgs (error, substring := true) in
#check CofibrationArrowPushoutPresentation.inl_isRelativeCofibration

#guard_msgs (error, substring := true) in
#check cofibrationArrowWaldhausenCategory

#guard_msgs (error, substring := true) in
#check cofibrationArrowGluing

#guard_msgs (error, substring := true) in
#check cofibrationArrowCylinder

#guard_msgs (error, substring := true) in
#check cofibrationArrowCylI

#guard_msgs (error, substring := true) in
#check cofibrationArrowStage

#guard_msgs (error, substring := true) in
#check cofibrationArrowApproximation

end SurfaceAndNonclaims

#print axioms CofibrationArrowPushoutPresentation
#print axioms CofibrationArrowPushoutPresentation.ofRelativeCofibration
#print axioms CofibrationArrowPushoutPresentation.isPushout

end CofibrationArrowPushoutTests
end MathlibExtTest.CategoryTheory.Waldhausen
