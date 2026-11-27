/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationCurry

/-!
# Actual enriched functors with whole enriched naturality

Objects carry Mathlib's genuine enriched functor, including every full Hom
map. Morphisms satisfy the complete internal-Hom naturality equation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  (C : Type uC) [EnrichedCategory V C]

/-- Genuine enriched functors with morphisms retaining whole Hom naturality. -/
structure WholeEnrichedFunctor where
  /-- The actual enriched functor and all of its original Hom maps. -/
  functor : EnrichedFunctor V C V

namespace WholeEnrichedFunctor

variable {V C}

/-- A true enriched natural transformation retains the entire Hom-object equation. -/
@[ext]
structure Hom (F G : WholeEnrichedFunctor V C) where
  /-- The original value-category component at each enriched object. -/
  app (x : C) : F.functor.obj x ⟶ G.functor.obj x
  /-- The complete enriched naturality equation in the internal Hom object. -/
  naturality (x y : C) :
    F.functor.map x y ≫ (ihom (F.functor.obj x)).map (app y) =
      G.functor.map x y ≫ (MonoidalClosed.pre (app x)).app (G.functor.obj y)

namespace Hom

/-- Whole enriched naturality evaluates to the entire original action square. -/
theorem comm {F G : WholeEnrichedFunctor V C} (f : Hom F G) (x y : C) :
    f.app x ▷ (x ⟶[V] y) ≫ MonoidalClosed.uncurry (G.functor.map x y) =
      MonoidalClosed.uncurry (F.functor.map x y) ≫ f.app y := by
  have h := congrArg MonoidalClosed.uncurry (f.naturality x y)
  simpa only [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app] using h.symm

/-- Every whole action square gives the true internal-Hom naturality equation. -/
def ofAction {F G : WholeEnrichedFunctor V C}
    (app : ∀ x, F.functor.obj x ⟶ G.functor.obj x)
    (comm : ∀ x y, app x ▷ (x ⟶[V] y) ≫ MonoidalClosed.uncurry (G.functor.map x y) =
      MonoidalClosed.uncurry (F.functor.map x y) ≫ app y) : Hom F G where
  app := app
  naturality x y := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app]
    exact (comm x y).symm

end Hom

/-- Genuine enriched functors and whole enriched transformations form a category. -/
instance : Category (WholeEnrichedFunctor V C) where
  Hom := Hom
  id F := Hom.ofAction (fun x => 𝟙 (F.functor.obj x)) (fun x y => by simp)
  comp f g := Hom.ofAction (fun x => f.app x ≫ g.app x) (fun x y => by
    rw [comp_whiskerRight, Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc])
  id_comp f := by ext x; exact Category.id_comp _
  comp_id f := by ext x; exact Category.comp_id _
  assoc f g h := by ext x; exact Category.assoc _ _ _

/-- The identity keeps the actual value-category components. -/
theorem id_app (F : WholeEnrichedFunctor V C) (x : C) :
    (𝟙 F : F ⟶ F).app x = 𝟙 (F.functor.obj x) := rfl

/-- Composition keeps every original value-category component. -/
theorem comp_app {F G H : WholeEnrichedFunctor V C} (f : F ⟶ G) (g : G ⟶ H) (x : C) :
    (f ≫ g).app x = f.app x ≫ g.app x := rfl

/-- All original components determine a true enriched transformation. -/
theorem hom_ext {F G : WholeEnrichedFunctor V C} {f g : F ⟶ G}
    (h : ∀ x, f.app x = g.app x) : f = g := Hom.ext (funext h)

end WholeEnrichedFunctor

end CategoryTheory
