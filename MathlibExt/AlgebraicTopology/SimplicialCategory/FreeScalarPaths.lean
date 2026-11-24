/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeQuiver
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategoryFunctoriality
import MathlibExt.CategoryTheory.Groupoid.FreePathCompletion

/-!
# Full original free scalar categories and native paths

Every scalar category of the original free simplicial enrichment is
the native path category of its SAME original generating quiver.
The full inverse functors retain each vertex, complete path, identity,
composition and original scalar operator. Completion retains the same
original generator inclusion through the native path completion.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialQuiver.FreeScalarPaths

variable {O : Type u} (Q : Data O)

/-- The exact original generating path category in the specified scalar degree. -/
structure pathCategory (Q : Data O) (q : SimplexCategoryᵒᵖ) : Type u where
  /-- The SAME individual original generating-quiver object. -/
  obj : O

instance pathCategoryCategory (q : SimplexCategoryᵒᵖ) : Category (pathCategory Q q) where
  Hom x y := Path Q q x.obj y.obj
  id x := @Quiver.Path.nil O (quiverAt Q q) x.obj
  comp a b := @Quiver.Path.comp O (quiverAt Q q) _ _ _ a b
  id_comp a := @Quiver.Path.nil_comp O (quiverAt Q q) _ _ a
  comp_id a := @Quiver.Path.comp_nil O (quiverAt Q q) _ _ a
  assoc a b c := @Quiver.Path.comp_assoc O (quiverAt Q q) _ _ _ _ a b c

/-- The original full free scalar category forgets only the scalar-object wrapper. -/
def toPaths (q : SimplexCategoryᵒᵖ) : SSet.ScalarObject (free Q) q ⥤ pathCategory Q q where
  obj x := ⟨x.obj⟩
  map a := a
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every full native original path is the SAME original scalar Hom simplex. -/
def fromPaths (q : SimplexCategoryᵒᵖ) : pathCategory Q q ⥤ SSet.ScalarObject (free Q) q where
  obj x := SSet.ScalarObject.mk x.obj
  map a := a
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Both original full path functors recover every original scalar object and Hom simplex. -/
theorem toPaths_fromPaths (q : SimplexCategoryᵒᵖ) : toPaths Q q ⋙ fromPaths Q q =
    𝟭 (SSet.ScalarObject (free Q) q) :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- Both original full path functors recover every complete native original path. -/
theorem fromPaths_toPaths (q : SimplexCategoryᵒᵖ) : fromPaths Q q ⋙ toPaths Q q =
    𝟭 (pathCategory Q q) := Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The whole original scalar free category is equivalent to the SAME native path category. -/
def equivalence (q : SimplexCategoryᵒᵖ) : SSet.ScalarObject (free Q) q ≌ pathCategory Q q :=
  Equivalence.mk (toPaths Q q) (fromPaths Q q)
    (eqToIso (toPaths_fromPaths Q q).symm) (eqToIso (fromPaths_toPaths Q q))

/-- The SAME original scalar operator maps EVERY complete original path. -/
def pathOperator {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) : pathCategory Q q ⥤ pathCategory Q r where
  obj x := ⟨x.obj⟩
  map a := mapPath Q f a
  map_id _ := rfl
  map_comp a b := (@Prefunctor.mapPath_comp O (quiverAt Q q) O (quiverAt Q r) (operator Q f) _ _ a _ b)

/-- Both original complete path coordinate functors retain EVERY same scalar operator. -/
lemma toPaths_operator {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    SSet.scalarOperator (C := free Q) f ⋙ toPaths Q r = toPaths Q q ⋙ pathOperator Q f := rfl

/-- The exact native original path category keeps the SAME original
quiver typeclass rather than a second path encoding. -/
def nativePathEquivalence (q : SimplexCategoryᵒᵖ) :
    letI := quiverAt Q q
    pathCategory Q q ≌ Paths O := by
  letI := quiverAt Q q
  let F : pathCategory Q q ⥤ Paths O := { obj x := x.obj, map a := a }
  let G : Paths O ⥤ pathCategory Q q := { obj x := ⟨x⟩, map a := a }
  have hF : F ⋙ G = 𝟭 _ := Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)
  have hG : G ⋙ F = 𝟭 _ := rfl
  exact Equivalence.mk F G (eqToIso hF.symm) (eqToIso hG)

/-- The actual complete native path-coordinate functor and its inverse
retain both original free-groupoid composition equations. -/
def completionCoordinateEquivalence (q : SimplexCategoryᵒᵖ) :
    FreeGroupoid (SSet.ScalarObject (free Q) q) ≌ FreeGroupoid (pathCategory Q q) :=
  Equivalence.mk (FreeGroupoid.map (toPaths Q q)) (FreeGroupoid.map (fromPaths Q q))
    (eqToIso (by rw [← FreeGroupoid.map_comp, toPaths_fromPaths, FreeGroupoid.map_id]))
    (eqToIso (by rw [← FreeGroupoid.map_comp, fromPaths_toPaths, FreeGroupoid.map_id]))

end CategoryTheory.SimplicialQuiver.FreeScalarPaths
