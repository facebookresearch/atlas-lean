/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionEnrichment

/-!
# The same original full unit into canonical scalar groupoid completion

Every original object is kept literally. On every full original Hom
simplex the unit is Mathlib's native FreeGroupoid.of map of the SAME
canonical ScalarObject category. All original operators, identities and
compositions are retained by the actual full simplicial enriched map.
No scalar weakness of this unit is a hypothesis or a conclusion here.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

variable (C : Carrier.{u})

/-- The SAME canonical original scalar category maps to its genuine native completion. -/
abbrev scalarUnit (q : SimplexCategoryᵒᵖ) : SSet.ScalarObject C q ⥤ category C q :=
  FreeGroupoid.of (SSet.ScalarObject C q)

/-- Each entire original Hom simplex is included by the SAME native canonical scalar unit. -/
def unitHom (x y : C) : (x ⟶[SSet.{u}] y) ⟶ hom C x y where
  app q := ↾fun a => (scalarUnit C q).map (X := SSet.ScalarObject.mk (Δ := q) x)
    (Y := SSet.ScalarObject.mk (Δ := q) y) a
  naturality q r f := by
    ext a
    rfl

/-- The actual complete original unit is an enriched functor on the SAME original objects
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

/-- The SAME full original completion unit retains every individual object literally. -/
theorem unit_obj (x : C) : (unit C).obj x = x := rfl

/-- Every actual full original unit Hom is its SAME native scalar inclusion in every degree. -/
theorem unitHom_apply (q : SimplexCategoryᵒᵖ) (x y : C) (a : (x ⟶[SSet.{u}] y).obj q) :
    ((unit C).map x y).app q a =
      (scalarUnit C q).map (X := SSet.ScalarObject.mk (Δ := q) x)
        (Y := SSet.ScalarObject.mk (Δ := q) y) a := rfl

/-- Every SAME original ordinal operator commutes with the actual entire unit Hom. -/
theorem unitHom_operator {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) (x y : C)
    (a : (x ⟶[SSet.{u}] y).obj q) :
    (unitHom C x y).app r ((x ⟶[SSet.{u}] y).map f a) =
      mapHom C f ((unitHom C x y).app q a) := rfl

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
