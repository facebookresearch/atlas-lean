/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Arrow comparisons at initial and terminal objects

A functor and a supplied isomorphism to an initial or terminal object give an Arrow
isomorphism between the mapped arrow and the corresponding arrow with that endpoint. The
unaffected endpoint is retained, and the square equation follows from the relevant
universal property.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A genuine initial-source comparison retains the original complete Arrow maps. -/
def originalInitialArrowIso (F : C ⥤ D) {Z : C} {Z' : D}
    (hZ' : IsInitial Z') (c : F.obj Z ≅ Z') {X : C}
    (f : Z ⟶ X) (g : Z' ⟶ F.obj X) : Arrow.mk (F.map f) ≅ Arrow.mk g :=
  Arrow.isoMk c (Iso.refl _) (by
    apply (cancel_epi c.inv).mp
    exact hZ'.hom_ext _ _)

/-- A genuine terminal-source comparison retains the original full target Arrow square. -/
def originalTerminalArrowIso (F : C ⥤ D) {Z : C} {Z' : D}
    (hZ' : IsTerminal Z') (c : F.obj Z ≅ Z') {X : C}
    (f : X ⟶ Z) (g : F.obj X ⟶ Z') : Arrow.mk (F.map f) ≅ Arrow.mk g :=
  Arrow.isoMk (Iso.refl _) c (hZ'.hom_ext _ _)

end CategoryTheory
