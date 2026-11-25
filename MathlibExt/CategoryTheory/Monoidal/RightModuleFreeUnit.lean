/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeCoefficient

/-!
# Free right modules on coefficients isomorphic to the unit

An actual coefficient-unit isomorphism and the original free-module unitor
give the regular module, retaining both complete carrier maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed

namespace CategoryTheory.RightModuleFree

universe uC vC
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] (S : C) [MonObj S]

/-- Apply the actual stock free functor and actual free-unit unitor to a coefficient-unit map. -/
def freeUnitRegular (P : C) (e : P ≅ 𝟙_ C) :
    (RightModuleFree.functor S).obj P ≅ RightModuleFree.regularObject S :=
  (RightModuleFree.functor S).mapIso e ≪≫ RightModuleFree.freeUnitRegularIso S

/-- The entire forward carrier map is original right tensoring followed by the original unitor. -/
theorem freeUnitRegular_hom (P : C) (e : P ≅ 𝟙_ C) :
    (freeUnitRegular S P e).hom.hom = (e.hom ▷ S) ≫ (λ_ S).hom := by
  change ((RightModuleFree.freeMap S e.hom) ≫ (RightModuleFree.freeUnitRegularIso S).hom).hom = _
  have h : ((RightModuleFree.freeMap S e.hom) ≫ (RightModuleFree.freeUnitRegularIso S).hom).hom =
      (RightModuleFree.freeMap S e.hom).hom ≫ (RightModuleFree.freeUnitRegularIso S).hom.hom := rfl
  exact h.trans (congrArg₂ (fun f g => f ≫ g)
    (RightModuleFree.freeMap_hom S e.hom) (RightModuleFree.freeUnitRegularIso_hom S))

/-- The entire inverse uses the original inverse unitor and inverse right tensor map. -/
theorem freeUnitRegular_inv (P : C) (e : P ≅ 𝟙_ C) :
    (freeUnitRegular S P e).inv.hom = (λ_ S).inv ≫ (e.inv ▷ S) := by
  change ((RightModuleFree.freeUnitRegularIso S).inv ≫ (RightModuleFree.freeMap S e.inv)).hom = _
  have h : ((RightModuleFree.freeUnitRegularIso S).inv ≫ (RightModuleFree.freeMap S e.inv)).hom =
      (RightModuleFree.freeUnitRegularIso S).inv.hom ≫ (RightModuleFree.freeMap S e.inv).hom := rfl
  exact h.trans (congrArg₂ (fun f g => f ≫ g)
    (RightModuleFree.freeUnitRegularIso_inv S) (RightModuleFree.freeMap_hom S e.inv))

end CategoryTheory.RightModuleFree
