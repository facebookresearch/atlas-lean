/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.LevelHo

/-!
# Homotopy-category laws for native level presentations

For an equivalence with a pointed enriched diagram category, identifies the projected objects, unit and counit of the induced level homotopy-category equivalence. The formulas retain both inverse components, their naturality and the inverse triangle identity.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable {C : Type uC} [CategoryTheory.Category.{vC} C]
attribute [local instance] Native.modelCategory

theorem forward_obj_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (forward e).obj ((projection e).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj (e.functor.obj X) := rfl

theorem inverse_obj_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (inverse e).obj ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X) =
      (projection e).obj (e.inverse.obj X) := rfl

/-- The whole projected unit is the actual given source unit, including its inverse. -/
theorem unitIso_app_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (unitIso e).app ((projection e).obj X) = (projection e).mapIso (e.unitIso.app X) :=
  Iso.ext (unitIso_hom_projected e X)

/-- The whole projected counit is the actual given native counit. -/
theorem counitIso_app_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (counitIso e).app ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).mapIso (e.counitIso.app X) :=
  Iso.ext (counitIso_hom_projected e X)

theorem unitIso_inv_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (unitIso e).inv.app ((projection e).obj X) = (projection e).map (e.unitIso.inv.app X) :=
  congrArg Iso.inv (unitIso_app_projected e X)

theorem counitIso_inv_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (counitIso e).inv.app ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map (e.counitIso.inv.app X) :=
  congrArg Iso.inv (counitIso_app_projected e X)

theorem unitIso_inv_naturality (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : HoCategory e} (f : X ⟶ Y) :
    (forward e ⋙ inverse e).map f ≫ (unitIso e).inv.app Y = (unitIso e).inv.app X ≫ f :=
  (unitIso e).inv.naturality f

theorem counitIso_inv_naturality (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f : X ⟶ Y) :
    f ≫ (counitIso e).inv.app Y = (counitIso e).inv.app X ≫ (inverse e ⋙ forward e).map f :=
  (counitIso e).inv.naturality f

/-- The second whole triangle uses the same original lifted unit and counit. -/
theorem inverse_unit_counit (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Functor.whiskerLeft (inverse e) (unitIso e).hom ≫
      Functor.whiskerRight (counitIso e).hom (inverse e) = 𝟙 (inverse e) := by
  ext X
  exact (equivalence e).unit_inverse_comp X

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo
