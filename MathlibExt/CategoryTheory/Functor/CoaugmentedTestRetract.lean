/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: @toskua
-/

module

public import Mathlib.CategoryTheory.NatIso

/-!
# Hom retractions at fixed targets of a coaugmented functor

The unit of a coaugmented endofunctor gives a retraction on full Hom sets
at every target where that unit is invertible. Naturality makes these
retractions commute with all source maps and fixed-target maps. They prove
that each map inverted by the functor passes all such target-Hom tests.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory

namespace CategoryTheory.Functor.CoaugmentedTestRetract

variable {A : Type u} [Category.{v} A] (T : A ⥤ A) (η : 𝟭 A ⟶ T)

/-- The complete target-Hom retraction uses the original source unit and inverse target unit. -/
def homRetraction (X E : A) [IsIso (η.app E)] (g : T.obj X ⟶ T.obj E) : X ⟶ E :=
  η.app X ≫ g ≫ CategoryTheory.inv (η.app E)

/-- The original functor map has this actual Hom retraction at every fixed target. -/
theorem homRetraction_map (X E : A) [IsIso (η.app E)] (g : X ⟶ E) :
    homRetraction T η X E (T.map g) = g := by
  change η.app X ≫ T.map g ≫ CategoryTheory.inv (η.app E) = g
  rw [← Category.assoc, ← η.naturality, Functor.id_map, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- Every entire source map commutes with the same original Hom retraction. -/
theorem homRetraction_source {X Y E : A} [IsIso (η.app E)]
    (f : X ⟶ Y) (g : T.obj Y ⟶ T.obj E) :
    homRetraction T η X E (T.map f ≫ g) = f ≫ homRetraction T η Y E g := by
  change η.app X ≫ (T.map f ≫ g) ≫ CategoryTheory.inv (η.app E) =
    f ≫ (η.app Y ≫ g ≫ CategoryTheory.inv (η.app E))
  have hf : η.app X ≫ T.map f = f ≫ η.app Y := by
    simpa only [Functor.id_map] using (η.naturality f).symm
  calc
    η.app X ≫ (T.map f ≫ g) ≫ CategoryTheory.inv (η.app E) =
        ((η.app X ≫ T.map f) ≫ g) ≫ CategoryTheory.inv (η.app E) := by
      simp only [Category.assoc]
    _ = ((f ≫ η.app Y) ≫ g) ≫ CategoryTheory.inv (η.app E) := by rw [hf]
    _ = f ≫ (η.app Y ≫ g ≫ CategoryTheory.inv (η.app E)) := by
      simp only [Category.assoc]

/-- Every entire fixed-target map commutes with the actual inverse-unit retraction. -/
theorem homRetraction_target (X : A) {E E' : A}
    [IsIso (η.app E)] [IsIso (η.app E')] (p : E ⟶ E') (g : T.obj X ⟶ T.obj E) :
    homRetraction T η X E' (g ≫ T.map p) = homRetraction T η X E g ≫ p := by
  have hi : T.map p ≫ CategoryTheory.inv (η.app E') = CategoryTheory.inv (η.app E) ≫ p := by
    apply (cancel_epi (η.app E)).mp
    rw [← Category.assoc, ← η.naturality, Functor.id_map,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id, IsIso.hom_inv_id_assoc]
  change η.app X ≫ (g ≫ T.map p) ≫ CategoryTheory.inv (η.app E') =
    (η.app X ≫ g ≫ CategoryTheory.inv (η.app E)) ≫ p
  simp only [Category.assoc]
  rw [hi]

/-- A map inverted by the actual coaugmented functor has bijective original Hom tests.
Only the unit at this test target is inverted; no global reflection property is assumed. -/
theorem precomp_bijective_of_map_isIso {X Y E : A} (f : X ⟶ Y)
    [IsIso (T.map f)] [IsIso (η.app E)] :
    Function.Bijective (fun g : Y ⟶ E => f ≫ g) := by
  constructor
  · intro g h hgh
    have hT : T.map f ≫ T.map g = T.map f ≫ T.map h := by
      simpa only [← T.map_comp] using T.congr_map hgh
    have hMap : T.map g = T.map h := (cancel_epi (T.map f)).mp hT
    have hSame := congrArg (homRetraction T η Y E) hMap
    simpa only [homRetraction_map] using hSame
  · intro g
    refine ⟨homRetraction T η Y E (CategoryTheory.inv (T.map f) ≫ T.map g), ?_⟩
    change f ≫ homRetraction T η Y E (CategoryTheory.inv (T.map f) ≫ T.map g) = g
    rw [← homRetraction_source,
      show T.map f ≫ (CategoryTheory.inv (T.map f) ≫ T.map g) = T.map g from
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ T.map g) (IsIso.hom_inv_id (T.map f))).trans
            (Category.id_comp _)), homRetraction_map]

end CategoryTheory.Functor.CoaugmentedTestRetract
