/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Germ coordinates of the skyscraper adjunction unit

For a point of a Grothendieck topology and a coefficient category with products and colimits
of the point universe, the skyscraper-adjunction unit sends sections to their family of stalk
germs. Its section component followed by projection at a fiber element is exactly the
corresponding germ map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w vC uC uA vA p
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable (Φ : Point.{p} J) {A : Type uA} [Category.{vA} A]
variable [HasProducts.{p} A] [HasColimitsOfSize.{p, p} A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- V1 failed implicit instance checks for the same sheaf/presheaf stalk aliases.
/-- Point adjunction unit projects to the geometric germ.

At object `U` and point-fiber element `z`, the unit section map followed by the product
projection at `z` equals `Φ.toPresheafFiber U z Q.obj`. -/
theorem skyscraperSheafAdjunction_unit_app_π
    (Q : Sheaf J A) (U : C) (z : Φ.fiber.obj U) :
    (Φ.skyscraperSheafAdjunction.unit.app Q).hom.app (op U) ≫
        Pi.π (fun (_ : Φ.fiber.obj U) => Φ.sheafFiber.obj Q) z =
      Φ.toPresheafFiber U z Q.obj := by
  have hhom : (Φ.skyscraperSheafAdjunction.unit.app Q).hom =
      Φ.skyscraperPresheafHomEquiv (𝟙 (Φ.sheafFiber.obj Q)) := by
    have hh := Φ.skyscraperSheafAdjunction_homEquiv_apply_hom (𝟙 (Φ.sheafFiber.obj Q))
    change ((Φ.skyscraperSheafAdjunction.homEquiv Q (Φ.sheafFiber.obj Q))
      (𝟙 (Φ.sheafFiber.obj Q))).hom = _ at hh
    have hi := congrArg (fun t : Q ⟶ Φ.skyscraperSheafFunctor.obj (Φ.sheafFiber.obj Q) => t.hom)
      (Φ.skyscraperSheafAdjunction.homEquiv_id Q)
    exact hi.symm.trans hh
  erw [hhom, skyscraperPresheafHomEquiv_app_π]
  exact Category.comp_id _

end CategoryTheory.GrothendieckTopology.Point

end
