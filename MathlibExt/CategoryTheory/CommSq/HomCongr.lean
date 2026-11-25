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
# Transport of commutative squares by vertex isomorphisms

Four independent isomorphisms of the vertices transport the edges of a
commutative square by precomposition and postcomposition. The resulting
square commutes.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.CommSq

variable {C : Type u} [Category.{v} C]

/-- Isomorphisms of all four vertices transport a commutative square. -/
theorem homCongr {W X Y Z W' X' Y' Z' : C}
    {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : CommSq f g h i)
    (eW : W ≅ W') (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z') :
    CommSq (eW.homCongr eX f) (eW.homCongr eY g)
      (eX.homCongr eZ h) (eY.homCongr eZ i) := by
  exact ⟨(Iso.homCongr_comp eW eX eZ f h).symm.trans
    ((congrArg (eW.homCongr eZ) sq.w).trans (Iso.homCongr_comp eW eY eZ g i))⟩

end CategoryTheory.CommSq
