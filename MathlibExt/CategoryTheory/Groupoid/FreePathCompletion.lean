/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The native completion of the original path category

The free groupoid of the SAME full native path category and the native
free groupoid of its original quiver have inverse full functors.
Every original generating arrow and complete path is retained.
Objects and generating Hom universes are independent. This is an
actual category equivalence; no nerve weak theorem is asserted here.
-/

noncomputable section
universe u v u' v'
open CategoryTheory

namespace CategoryTheory.FreePathCompletion

variable (V : Type u) [Quiver.{v} V]

/-- The SAME complete original paths evaluated in the native original quiver free groupoid. -/
def pathToQuiverGroupoid : Paths V ⥤ Quiver.FreeGroupoid V :=
  Paths.lift (Quiver.FreeGroupoid.of V)

/-- Complete the SAME original path evaluation through the native categorical groupoid unit. -/
def toQuiverGroupoid : FreeGroupoid (Paths V) ⥤ Quiver.FreeGroupoid V :=
  FreeGroupoid.lift (pathToQuiverGroupoid V)

/-- The SAME original generating arrows included as full native completed singleton paths. -/
def generatorsToPathGroupoid : V ⥤q FreeGroupoid (Paths V) :=
  (Paths.of V).comp (FreeGroupoid.of (Paths V)).toPrefunctor

/-- Extend the actual singleton-path inclusion through the native original quiver free groupoid. -/
def toPathGroupoid : Quiver.FreeGroupoid V ⥤ FreeGroupoid (Paths V) :=
  Quiver.FreeGroupoid.lift (generatorsToPathGroupoid V)

/-- The whole native categorical unit retains the SAME full original path evaluation. -/
theorem unit_toQuiverGroupoid :
    FreeGroupoid.of (Paths V) ⋙ toQuiverGroupoid V = pathToQuiverGroupoid V :=
  FreeGroupoid.lift_spec _

/-- Every SAME original generator retains its actual completed singleton path. -/
theorem generators_toPathGroupoid :
    (Quiver.FreeGroupoid.of V).comp (toPathGroupoid V).toPrefunctor = generatorsToPathGroupoid V :=
  Quiver.FreeGroupoid.lift_spec _

/-- The two original full path functors agree on EVERY complete original path. -/
theorem pathToQuiver_toPath :
    pathToQuiverGroupoid V ⋙ toPathGroupoid V = FreeGroupoid.of (Paths V) := by
  refine Paths.ext_functor rfl ?_
  intro x y a
  change (toPathGroupoid V).map ((Paths.lift (Quiver.FreeGroupoid.of V)).map a.toPath) =
    (FreeGroupoid.of (Paths V)).map a.toPath
  rw [Paths.lift_toPath]
  have h := Prefunctor.congr_hom (generators_toPathGroupoid V) a
  exact eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))

/-- Both full native completion functors recover EVERY original completed path morphism. -/
theorem toQuiver_toPath : toQuiverGroupoid V ⋙ toPathGroupoid V = 𝟭 (FreeGroupoid (Paths V)) := by
  apply FreeGroupoid.lift_unique'
  rw [← Functor.assoc, unit_toQuiverGroupoid, pathToQuiver_toPath, Functor.comp_id]

/-- Both full native completion functors recover EVERY original reduced quiver word. -/
theorem toPath_toQuiver : toPathGroupoid V ⋙ toQuiverGroupoid V = 𝟭 (Quiver.FreeGroupoid V) := by
  apply (Quiver.FreeGroupoid.lift_unique (Quiver.FreeGroupoid.of V) _ ?_).trans
    (Quiver.FreeGroupoid.lift_unique (Quiver.FreeGroupoid.of V) (𝟭 _) (by rfl)).symm
  rw [← Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc, generators_toPathGroupoid]
  change (Paths.of V).comp (FreeGroupoid.of (Paths V) ⋙ toQuiverGroupoid V).toPrefunctor =
    Quiver.FreeGroupoid.of V
  rw [unit_toQuiverGroupoid]
  exact Paths.lift_spec _

/-- The native categorical completion of all original paths is equivalent
to the SAME native free groupoid of the original quiver, with actual inverse functors. -/
def equivalence : FreeGroupoid (Paths V) ≌ Quiver.FreeGroupoid V :=
  Equivalence.mk (toQuiverGroupoid V) (toPathGroupoid V)
    (eqToIso (toQuiver_toPath V).symm) (eqToIso (toPath_toQuiver V))

/-- Every original singleton generating arrow maps to the SAME full native quiver generator. -/
lemma toQuiverGroupoid_generator {x y : V} (a : x ⟶ y) :
    (toQuiverGroupoid V).map ((FreeGroupoid.of (Paths V)).map ((Paths.of V).map a)) =
      (Quiver.FreeGroupoid.of V).map a := by
  exact (FreeGroupoid.lift_map_homMk _ _).trans (Paths.lift_toPath _ a)

end CategoryTheory.FreePathCompletion
