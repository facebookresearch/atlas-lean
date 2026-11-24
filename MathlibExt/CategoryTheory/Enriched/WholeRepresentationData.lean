/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
# Whole Hom actions of enriched representations

A representation retains the complete Hom object of the enriched category.
Its morphisms commute with these entire action maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  (C : Type uC) [EnrichedCategory V C]

/-- A representation whose action uses every complete enriched Hom object. -/
structure WholeRepresentation where
  /-- The value object at each original enriched object. -/
  obj : C → V
  /-- The entire enriched Hom object acts on its source value object. -/
  action (x y : C) : obj x ⊗ (x ⟶[V] y) ⟶ obj y
  /-- The enriched identity acts through the actual value-category unitor. -/
  unit (x : C) : (obj x ◁ eId V x) ≫ action x x = (ρ_ (obj x)).hom
  /-- The full enriched composition acts associatively. -/
  assoc (x y z : C) :
    (α_ (obj x) (x ⟶[V] y) (y ⟶[V] z)).inv ≫ action x y ▷ (y ⟶[V] z) ≫ action y z =
      (obj x ◁ eComp V x y z) ≫ action x z

namespace WholeRepresentation

variable {V C}

/-- A whole enriched transformation commutes with the complete Hom action. -/
@[ext]
structure Hom (X Y : WholeRepresentation V C) where
  /-- The original component map at each enriched object. -/
  app (x : C) : X.obj x ⟶ Y.obj x
  /-- All Hom objects retain their entire enriched naturality square. -/
  comm (x y : C) :
    (app x ▷ (x ⟶[V] y)) ≫ Y.action x y = X.action x y ≫ app y

/-- Whole representations and whole action transformations form a category. -/
instance : Category (WholeRepresentation V C) where
  Hom := Hom
  id X :=
    { app x := 𝟙 (X.obj x)
      comm x y := by simp }
  comp f g :=
    { app x := f.app x ≫ g.app x
      comm x y := by
        rw [comp_whiskerRight, Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc] }
  id_comp f := by ext x; exact Category.id_comp _
  comp_id f := by ext x; exact Category.comp_id _
  assoc f g h := by ext x; exact Category.assoc _ _ _

/-- Every original component is retained by the categorical identity. -/
theorem id_app (X : WholeRepresentation V C) (x : C) : (𝟙 X : X ⟶ X).app x = 𝟙 (X.obj x) := rfl

/-- Every original component is retained by categorical composition. -/
theorem comp_app {X Y Z : WholeRepresentation V C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : C) :
    (f ≫ g).app x = f.app x ≫ g.app x := rfl

/-- A whole enriched transformation is determined by all its original components. -/
theorem hom_ext {X Y : WholeRepresentation V C} {f g : X ⟶ Y}
    (h : ∀ x, f.app x = g.app x) : f = g := Hom.ext (funext h)

end WholeRepresentation

end CategoryTheory
