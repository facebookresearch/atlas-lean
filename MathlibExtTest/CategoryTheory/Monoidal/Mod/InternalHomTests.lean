/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Monoidal.Mod.InternalHom

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe v u

namespace MathlibExtTest.CategoryTheory.Mod.InternalHom

section PublicSurface

#check Mod.internalHomPre
#check Mod.internalHomPost
#check Mod.internalHomOfEqualizer
#check Mod.internalHomι
#check Mod.internalHom_condition
#check Mod.internalHomIsLimit
#check Mod.internalHomMap

#check @Mod.internalHomPre.{1, 1}
#check @Mod.internalHomPre.{0, 0}
#check @Mod.internalHomPost.{1, 1}
#check @Mod.internalHomPost.{0, 0}
#check @Mod.internalHomOfEqualizer.{1, 1}
#check @Mod.internalHomOfEqualizer.{0, 0}
#check @Mod.internalHomι.{1, 1}
#check @Mod.internalHomι.{0, 0}
#check @Mod.internalHom_condition.{1, 1}
#check @Mod.internalHom_condition.{0, 0}
#check @Mod.internalHomIsLimit.{1, 1}
#check @Mod.internalHomIsLimit.{0, 0}
#check @Mod.internalHomMap.{1, 1}
#check @Mod.internalHomMap.{0, 0}

end PublicSurface

section LiteralEqualizer

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
variable (A : CommMon C) [HasEqualizers C]

example (M N : Mod C A.X) :
    (ihom M.X).obj N.X ⟶ (ihom (A.X ⊗ M.X)).obj N.X :=
  Mod.internalHomPre A M N

example (M N : Mod C A.X) :
    (ihom M.X).obj N.X ⟶ (ihom (A.X ⊗ M.X)).obj N.X :=
  Mod.internalHomPost A M N

example (M : Mod C A.X) : Mod C A.X ⥤ Mod C A.X :=
  Mod.internalHomOfEqualizer A M

example (M N : Mod C A.X) :
    ((Mod.internalHomOfEqualizer A M).obj N).X ⟶ (ihom M.X).obj N.X :=
  Mod.internalHomι A M N

example (M N : Mod C A.X) :
    Mod.internalHomι A M N ≫ Mod.internalHomPre A M N =
      Mod.internalHomι A M N ≫ Mod.internalHomPost A M N :=
  Mod.internalHom_condition A M N

example (M N : Mod C A.X) : IsLimit
    (Fork.ofι (Mod.internalHomι A M N)
      (Mod.internalHom_condition A M N)) :=
  Mod.internalHomIsLimit A M N

example (M : Mod C A.X) {N N' : Mod C A.X} (g : N ⟶ N') :
    ((Mod.internalHomOfEqualizer A M).map g).hom ≫ Mod.internalHomι A M N' =
      Mod.internalHomι A M N ≫ (ihom M.X).map g.hom :=
  Mod.internalHomMap A M g

example (M N : Mod C A.X) :
    (Mod.internalHomOfEqualizer A M).map (𝟙 N) =
      𝟙 ((Mod.internalHomOfEqualizer A M).obj N) := by
  simp

example (M : Mod C A.X) {N₁ N₂ N₃ : Mod C A.X}
    (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃) :
    (Mod.internalHomOfEqualizer A M).map (f ≫ g) =
      (Mod.internalHomOfEqualizer A M).map f ≫ (Mod.internalHomOfEqualizer A M).map g := by
  simp

example (M : Mod C A.X) : Mod C A.X :=
  (Mod.internalHomOfEqualizer A M).obj (Mod.regular A.X)

example : Mod C A.X :=
  (Mod.internalHomOfEqualizer A (Mod.regular A.X)).obj (Mod.regular A.X)

end LiteralEqualizer

section TwoScalars

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C] [HasEqualizers C]

example (A B : CommMon C) (M N : Mod C A.X) (P Q : Mod C B.X) :
    Mod C A.X × Mod C B.X :=
  ((Mod.internalHomOfEqualizer A M).obj N, (Mod.internalHomOfEqualizer B P).obj Q)

example (A B : CommMon C) (M N : Mod C A.X) (P Q : Mod C B.X) :
    C × C :=
  (((Mod.internalHomOfEqualizer A M).obj N).X, ((Mod.internalHomOfEqualizer B P).obj Q).X)

end TwoScalars

section RawHomFalsifier

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
variable (A : CommMon C)

example (_M _N : Mod C A.X) : True := by
  fail_if_success
    let _ : IsModHom A.X (Mod.internalHomPre A _M _N) := inferInstance
  fail_if_success
    let _ : IsModHom A.X (Mod.internalHomPost A _M _N) := inferInstance
  trivial

end RawHomFalsifier

section MissingClosedPremise

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C]
variable (A : CommMon C)

example (_M _N : Mod C A.X) : True := by
  fail_if_success
    let _ := Mod.internalHomPre A _M _N
  fail_if_success
    let _ := Mod.internalHomPost A _M _N
  trivial

end MissingClosedPremise

section MissingEqualizerPremise

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
variable (A : CommMon C)

example (_M _N : Mod C A.X) : True := by
  fail_if_success
    let _ := Mod.internalHomOfEqualizer A _M
  fail_if_success
    let _ := Mod.internalHomι A _M _N
  trivial

end MissingEqualizerPremise

section NoGlobalModuleInstances

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C] [HasEqualizers C]

example (_A : CommMon C) : True := by
  fail_if_success
    let _ : MonoidalCategory (Mod C _A.X) := inferInstance
  fail_if_success
    let _ : SymmetricCategory (Mod C _A.X) := inferInstance
  fail_if_success
    let _ : MonoidalClosed (Mod C _A.X) := inferInstance
  trivial

end NoGlobalModuleInstances

section PrivacyAndNonclaims

#guard_msgs (error, substring := true) in
#check Mod.homModuleObj
#guard_msgs (error, substring := true) in
#check Mod.internalHomPreMod
#guard_msgs (error, substring := true) in
#check Mod.internalHomPostMod
#guard_msgs (error, substring := true) in
#check Mod.homModuleMap
#guard_msgs (error, substring := true) in
#check Mod.internalHomMapLift

#guard_msgs (error, substring := true) in
#check Mod.evaluation
#guard_msgs (error, substring := true) in
#check Mod.coevaluation
#guard_msgs (error, substring := true) in
#check Mod.relativeTensorInternalHomAdjunction
#guard_msgs (error, substring := true) in
#check Mod.instMonoidalClosed

end PrivacyAndNonclaims

#print axioms Mod.internalHomPre
#print axioms Mod.internalHomPost
#print axioms Mod.internalHomOfEqualizer
#print axioms Mod.internalHomι
#print axioms Mod.internalHom_condition
#print axioms Mod.internalHomIsLimit
#print axioms Mod.internalHomMap

end MathlibExtTest.CategoryTheory.Mod.InternalHom
