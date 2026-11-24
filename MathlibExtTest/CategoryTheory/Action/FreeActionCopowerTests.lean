/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Action.FreeActionCopower

set_option autoImplicit false
noncomputable section
universe u v wH wE

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.ActionFreeCopowerTests

variable {C : Type u} [Category.{v} C]
  (H : Type wH) (E : Type wE) [Group H] [MulAction H E]
  (Z : C) (rho : H →* End Z)
  (hfree : ∀ e : E, Function.Injective (fun a : H => a • e))
  [HasCoproduct (fun _ : MulAction.orbitRel.Quotient H E => Z)]

example : IsColimit (ActionCategory.freeActionCopowerCocone H E Z rho hfree) :=
  ActionCategory.freeActionCopowerIsColimit H E Z rho hfree

variable [HasColimit (ActionCategory.coefficientDiagram H E Z rho)]

example : colimit (ActionCategory.coefficientDiagram H E Z rho) ≅
    ∐ (fun _ : MulAction.orbitRel.Quotient H E => Z) :=
  ActionCategory.freeActionColimitCopowerIso H E Z rho hfree

example (e : E) :
    colimit.ι (ActionCategory.coefficientDiagram H E Z rho) (e : ActionCategory H E) ≫
        (ActionCategory.freeActionColimitCopowerIso H E Z rho hfree).hom =
      (rho (ActionCategory.freeActionTwist H E hfree e)).asHom ≫
        Sigma.ι (fun _ : MulAction.orbitRel.Quotient H E => Z) (Quotient.mk'' e) :=
  ActionCategory.freeActionColimitCopowerIso_generator H E Z rho hfree e

example (Z' : C) (rho' : H →* End Z') (f : Z ⟶ Z')
    (hf : ∀ a : H, (rho a).asHom ≫ f = f ≫ (rho' a).asHom)
    [HasCoproduct (fun _ : MulAction.orbitRel.Quotient H E => Z')]
    [HasColimit (ActionCategory.coefficientDiagram H E Z' rho')] :
    colimMap (ActionCategory.coefficientNatTrans H E Z Z' rho rho' f hf) ≫
        (ActionCategory.freeActionColimitCopowerIso H E Z' rho' hfree).hom =
      (ActionCategory.freeActionColimitCopowerIso H E Z rho hfree).hom ≫
        Limits.Sigma.map (fun _ : MulAction.orbitRel.Quotient H E => f) :=
  ActionCategory.freeActionColimitCopowerIso_naturality H E Z rho hfree Z' rho' f hf

#check @ActionCategory.freeActionColimitCopowerIso.{0, 0, 0, 0}
#check @ActionCategory.freeActionColimitCopowerIso.{1, 0, 0, 1}
#check @ActionCategory.freeActionColimitCopowerIso.{0, 1, 1, 0}
#check @ActionCategory.freeActionColimitCopowerIso.{u, v, wH, wE}
#print axioms ActionCategory.freeActionCopowerIsColimit
#print axioms ActionCategory.freeActionColimitCopowerIso
#print axioms ActionCategory.freeActionColimitCopowerIso_generator
#print axioms ActionCategory.freeActionColimitCopowerIso_naturality

end MathlibExtTest.ActionFreeCopowerTests
