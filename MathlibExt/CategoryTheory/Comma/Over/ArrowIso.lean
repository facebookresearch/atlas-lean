/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Original arrow isomorphisms over the supplied base

An original arrow isomorphism whose target component commutes with the
supplied base maps lifts to the same original arrow isomorphism in the
slice. Both components and the original whole arrow square are retained.
Object, Hom and base universes impose no new smallness assumptions.
-/

noncomputable section
universe u v
open CategoryTheory

namespace CategoryTheory.Arrow

/-- Keep the original two arrow components and base triangle when lifting an actual arrow
isomorphism into
  the supplied slice. -/
def isoOver {C : Type u} [Category.{v} C] {A D A' D' Z : C}
    {f : A ⟶ D} {g : A' ⟶ D'} (e : Arrow.mk f ≅ Arrow.mk g)
    (r : D ⟶ Z) (r' : D' ⟶ Z) (hr : e.hom.right ≫ r' = r) :
    Arrow.mk (Over.homMk f rfl : Over.mk (f ≫ r) ⟶ Over.mk r) ≅
      Arrow.mk (Over.homMk g rfl : Over.mk (g ≫ r') ⟶ Over.mk r') := by
  let el : Over.mk (f ≫ r) ≅ Over.mk (g ≫ r') :=
    Over.isoMk (Arrow.leftFunc.mapIso e) (by
      calc
        e.hom.left ≫ (g ≫ r') = (e.hom.left ≫ g) ≫ r' := (Category.assoc _ _ _).symm
        _ = (f ≫ e.hom.right) ≫ r' := congrArg (fun z => z ≫ r') e.hom.w
        _ = f ≫ r := (Category.assoc _ _ _).trans (congrArg (fun z => f ≫ z) hr))
  let er : Over.mk r ≅ Over.mk r' := Over.isoMk (Arrow.rightFunc.mapIso e) hr
  exact Arrow.isoMk el er (by apply Over.OverMorphism.ext; exact e.hom.w)

/-- The lifted source component keeps exactly the original whole source map. -/
@[simp]
theorem isoOver_hom_left {C : Type u} [Category.{v} C] {A D A' D' Z : C}
    {f : A ⟶ D} {g : A' ⟶ D'} (e : Arrow.mk f ≅ Arrow.mk g)
    (r : D ⟶ Z) (r' : D' ⟶ Z) (hr : e.hom.right ≫ r' = r) :
    ((isoOver e r r' hr).hom.left).left = e.hom.left := rfl

/-- The original target map remains the actual lifted target component. -/
@[simp]
theorem isoOver_hom_right {C : Type u} [Category.{v} C] {A D A' D' Z : C}
    {f : A ⟶ D} {g : A' ⟶ D'} (e : Arrow.mk f ≅ Arrow.mk g)
    (r : D ⟶ Z) (r' : D' ⟶ Z) (hr : e.hom.right ≫ r' = r) :
    ((isoOver e r r' hr).hom.right).left = e.hom.right := rfl

end CategoryTheory.Arrow
