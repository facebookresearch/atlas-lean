/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.HomCongr

/-!
# Commutative squares under vertex isomorphisms

For a commutative square f ≫ h = g ≫ i in a category C, choose isomorphisms e_W,e_X,e_Y,e_Z
from its four vertices to new vertices. Transport an edge a : U → V to e_U.inv ≫ a ≫ e_V.hom.

The four transported edges form a commutative square. The internal vertex isomorphisms cancel
in each composite, leaving the transport of the original square equation. Object and morphism
universes are independent.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.CommSq

variable {C : Type u} [Category.{v} C]

/-- Commutative-square transport by four vertex isomorphisms.

For CommSq f g h i and vertex isomorphisms e_W,e_X,e_Y,e_Z, the edges e_W.inv ≫ f ≫ e_X.hom,
e_W.inv ≫ g ≫ e_Y.hom, e_X.inv ≫ h ≫ e_Z.hom and e_Y.inv ≫ i ≫ e_Z.hom form a commutative
square. -/
theorem homCongr {W X Y Z W' X' Y' Z' : C}
    {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i)
    (eW : W ≅ W') (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z') :
    CommSq (eW.homCongr eX f) (eW.homCongr eY g)
      (eX.homCongr eZ h) (eY.homCongr eZ i) := by
  exact ⟨(Iso.homCongr_comp eW eX eZ f h).symm.trans
    ((congrArg (eW.homCongr eZ) sq.w).trans (Iso.homCongr_comp eW eY eZ g i))⟩

end CategoryTheory.CommSq
