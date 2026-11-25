/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.Limits
public import Batteries.Tactic.Lint

/-! # Original bimodule limit and colimit clients -/

@[expose] public section

set_option autoImplicit false

universe v u vJ uJ

open CategoryTheory Limits MonoidalCategory

namespace BimodLimitsClients

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (A B : Mon C) {J : Type uJ} [Category.{vJ} J]

example : (Bimod.forget (B := B) A).Faithful := inferInstance

example : (Bimod.forget (B := B) A).ReflectsIsomorphisms := inferInstance

example [HasLimitsOfSize.{vJ, uJ} C] : HasLimitsOfSize.{vJ, uJ} (Bimod A B) :=
  Bimod.hasLimits A B

example [HasColimitsOfSize.{vJ, uJ} C]
    [PreservesColimitsOfSize.{vJ, uJ} (tensorLeft A.X)]
    [PreservesColimitsOfSize.{vJ, uJ} (tensorRight B.X)] :
    HasColimitsOfSize.{vJ, uJ} (Bimod A B) :=
  Bimod.hasColimits A B

example [HasColimitsOfSize.{vJ, uJ} C]
    [PreservesColimitsOfSize.{vJ, uJ} (tensorLeft A.X)]
    [PreservesColimitsOfSize.{vJ, uJ} (tensorRight B.X)] :
    PreservesColimitsOfSize.{vJ, uJ} (Bimod.forget (B := B) A) := inferInstance

variable (F : J ⥤ Bimod A B)

example (c : Cone (F ⋙ Bimod.forget (B := B) A)) (h : IsLimit c) :
    (Bimod.ForgetCreatesLimits.liftedCone F c h).pt.X = c.pt := rfl

example (c : Cone (F ⋙ Bimod.forget (B := B) A)) (h : IsLimit c) (j : J) :
    ((Bimod.ForgetCreatesLimits.liftedCone F c h).π.app j).hom = c.π.app j := rfl

example (c : Cone (F ⋙ Bimod.forget (B := B) A)) (h : IsLimit c) :
    IsLimit (Bimod.ForgetCreatesLimits.liftedCone F c h) :=
  Bimod.ForgetCreatesLimits.liftedConeIsLimit F c h

variable [PreservesColimitsOfShape J (tensorLeft A.X)]
  [PreservesColimitsOfShape J (tensorRight B.X)]

example (c : Cocone (F ⋙ Bimod.forget (B := B) A)) (h : IsColimit c) :
    (Bimod.ForgetCreatesColimits.liftedCocone F c h).pt.X = c.pt := rfl

example (c : Cocone (F ⋙ Bimod.forget (B := B) A)) (h : IsColimit c) (j : J) :
    ((Bimod.ForgetCreatesColimits.liftedCocone F c h).ι.app j).hom = c.ι.app j := rfl

example (c : Cocone (F ⋙ Bimod.forget (B := B) A)) (h : IsColimit c) :
    IsColimit (Bimod.ForgetCreatesColimits.liftedCocone F c h) :=
  Bimod.ForgetCreatesColimits.liftedCoconeIsColimit F c h

#print axioms Bimod.forgetReflectsIsomorphisms
#print axioms Bimod.ForgetCreatesLimits.conePoint
#print axioms Bimod.ForgetCreatesLimits.liftedConeIsLimit
#print axioms Bimod.forgetCreatesLimitsOfSize
#print axioms Bimod.hasLimits
#print axioms Bimod.ForgetCreatesColimits.coconePoint
#print axioms Bimod.ForgetCreatesColimits.liftedCoconeIsColimit
#print axioms Bimod.forgetCreatesColimitsOfSize
#print axioms Bimod.hasColimits

#lint only unusedArguments in MathlibExt.CategoryTheory.Monoidal.Bimod.Limits

end BimodLimitsClients
