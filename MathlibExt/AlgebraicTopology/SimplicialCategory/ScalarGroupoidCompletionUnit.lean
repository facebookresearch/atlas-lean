/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionEnrichment

/-!
# The same full unit into canonical scalar groupoid completion

Every object is kept literally. On every Hom
simplex the unit is Mathlib's native FreeGroupoid.of map of the same
canonical ScalarObject category. All operators, identities and
compositions are retained by the full simplicial enriched map.

-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

variable (C : Carrier.{u})

/-- The same canonical scalar category maps to its native completion. -/
abbrev scalarUnit (q : SimplexCategoryᵒᵖ) : SSet.ScalarObject C q ⥤ category C q :=
  FreeGroupoid.of (SSet.ScalarObject C q)

/-- Each Hom simplex is included by the same native canonical scalar unit. -/
def unitHom (x y : C) : (x ⟶[SSet.{u}] y) ⟶ hom C x y where
  app q := ↾fun a => (scalarUnit C q).map (X := SSet.ScalarObject.mk (Δ := q) x)
    (Y := SSet.ScalarObject.mk (Δ := q) y) a
  naturality q r f := by
    ext a
    rfl

/-- The complete unit is an enriched functor on the same objects
and Homs. -/
def unit : C ⟶ object C where
  obj x := x
  map := unitHom C
  map_id x := by
    ext q a
    exact (scalarUnit C q).map_id (SSet.ScalarObject.mk (Δ := q) x)
  map_comp x y z := by
    ext q a
    exact (scalarUnit C q).map_comp (X := SSet.ScalarObject.mk (Δ := q) x)
      (Y := SSet.ScalarObject.mk (Δ := q) y) (Z := SSet.ScalarObject.mk (Δ := q) z) a.1 a.2

/-- The same full completion unit retains every individual object literally. -/
theorem unit_obj (x : C) : (unit C).obj x = x := rfl

/-- Every full unit Hom is its same native scalar inclusion in every degree. -/
theorem unitHom_apply (q : SimplexCategoryᵒᵖ) (x y : C) (a : (x ⟶[SSet.{u}] y).obj q) :
    ((unit C).map x y).app q a =
      (scalarUnit C q).map (X := SSet.ScalarObject.mk (Δ := q) x)
        (Y := SSet.ScalarObject.mk (Δ := q) y) a := rfl

/-- Every same ordinal operator commutes with the unit Hom. -/
theorem unitHom_operator {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) (x y : C)
    (a : (x ⟶[SSet.{u}] y).obj q) :
    (unitHom C x y).app r ((x ⟶[SSet.{u}] y).map f a) =
      mapHom C f ((unitHom C x y).app q a) := rfl

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
