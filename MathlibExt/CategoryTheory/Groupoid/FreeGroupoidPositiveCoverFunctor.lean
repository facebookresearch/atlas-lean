/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverQuiver
import MathlibExt.CategoryTheory.Groupoid.FreePathCompletion
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Full original positive-cover paths map to the actual native completion comma

Each original cover vertex is its individual target and SAME full native
completed path from the fixed base. Every actual original generating
edge supplies the full native StructuredArrow triangle. Extending by
native Paths.lift retains all entire original positive paths and maps.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver for the native full path functor. -/
private local instance coverQuiverForPositiveFunctor : Quiver.{v} (CoverVertex V z) :=
  coverQuiver V z

/-- The actual native comma of original full positive paths evaluated in their SAME free
groupoid. -/
abbrev PositiveCoverComma := StructuredArrow ((Quiver.FreeGroupoid.of V).obj z)
  (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V)

/-- Every SAME original cover vertex gives its actual individual-target full native
structured arrow. -/
def coverVertexToComma (a : CoverVertex V z) : PositiveCoverComma V z :=
  StructuredArrow.mk (C := Paths V) (D := Quiver.FreeGroupoid V)
    (T := CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V) (Y :=
      (a.target : Paths V)) a.path

/-- The actual full original generator gives its SAME native completion triangle. -/
def coverGeneratorToComma : CoverVertex V z ⥤q PositiveCoverComma V z where
  obj := coverVertexToComma V z
  map {a b} f := StructuredArrow.homMk (C := Paths V) (D := Quiver.FreeGroupoid V)
    (T := CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V)
    (f.arrow.toPath : @Quiver.Path V inferInstance a.target b.target)
    (by
      change a.path ≫ (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V).map
        f.arrow.toPath = b.path
      exact (congrArg (fun h => a.path ≫ h) (Paths.lift_toPath (Quiver.FreeGroupoid.of V)
        f.arrow)).trans f.path_eq)

/-- The full original positive-cover path functor extends every SAME original generator and
native triangle. -/
def coverPathsToComma : Paths (CoverVertex V z) ⥤ PositiveCoverComma V z :=
  Paths.lift (coverGeneratorToComma V z)

/-- The native full original positive-cover projection into the SAME original path category. -/
def coverPathsProjection : Paths (CoverVertex V z) ⥤ Paths V :=
  Paths.lift ((coverProjection V z).comp (Paths.of V))

/-- Every original cover generator keeps its actual original full singleton path under the
native comma projection. -/
lemma coverPathsToComma_generator {a b : CoverVertex V z} (f : CoverArrow V z a b) :
    ((coverPathsToComma V z).map (@Quiver.Hom.toPath (CoverVertex V z) (coverQuiver V z) a b
      f)).right =
      f.arrow.toPath := by
  have he := Paths.lift_toPath (V := CoverVertex V z) (coverGeneratorToComma V z) f
  exact congrArg (fun h : coverVertexToComma V z a ⟶ coverVertexToComma V z b => h.right) he

/-- The whole actual native comma functor retains the SAME entire original positive-path
projection. -/
theorem coverPathsToComma_projection :
    coverPathsToComma V z ⋙ StructuredArrow.proj ((Quiver.FreeGroupoid.of V).obj z)
      (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V) = coverPathsProjection V z := by
  refine Paths.ext_functor rfl ?_
  intro a b f
  change ((coverPathsToComma V z).map (@Quiver.Hom.toPath (CoverVertex V z) (coverQuiver V
    z) a b f)).right =
    eqToHom rfl ≫ (coverPathsProjection V z).map f.toPath ≫ eqToHom rfl
  have hid : eqToHom rfl ≫ (coverPathsProjection V z).map f.toPath ≫ eqToHom rfl =
      (coverPathsProjection V z).map f.toPath :=
    (Category.id_comp _).trans (Category.comp_id _)
  have hfirst := coverPathsToComma_generator V z f
  have hsecond := Paths.lift_toPath (V := CoverVertex V z) ((coverProjection V z).comp
    (Paths.of V)) f
  exact hfirst.trans (hsecond.symm.trans hid.symm)

/-- Every native original cover vertex is read back as its SAME full path/target structured
arrow. -/
lemma coverPathsToComma_obj (a : CoverVertex V z) :
    (coverPathsToComma V z).obj a = StructuredArrow.mk (C := Paths V) (D := Quiver.FreeGroupoid V)
    (T := CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V) (Y :=
      (a.target : Paths V)) a.path := rfl

end Quiver.FreeGroupoid.OriginalWords
