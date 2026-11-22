/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadNondegenerateOperators
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentFirstJointProperties
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadUnits

/-!
# Original reduced flanked nondegenerate path data

The arrows retain whole original nondegenerate input beads, both original
labels, endpoint-only first flags, full last flags and positive original
dimensions. Their paths use the native Quiver.Path and map into the same
original coherent generating paths.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.NormalForms

open SimplicialEnrichment SimplicialQuiver
open TerminalFlag

/-- The whole same original coefficient with its literal native path-nerve type. -/
def coefficient {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (b : Bead K x y q) : (coefficientObject.{u} b.dimension).obj q := b.coefficient

/-- An actual original positive nondegenerate bead with both complete original flanking flags. -/
structure NormalBead (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) where
  /-- The entire original input bead and coefficient. -/
  bead : Bead K x y q
  /-- The original bead is genuinely positive-dimensional. -/
  positive : 0 < bead.dimension
  /-- The same original input simplex is genuinely nondegenerate. -/
  nondegenerate : bead.simplex ∈ K.nonDegenerate bead.dimension
  /-- The complete original first flag is exactly its two original endpoints. -/
  first : ((coefficient bead).obj 0).I =
    {ULift.up.{u} (0 : Fin (bead.dimension + 1)), ULift.up.{u} (Fin.last bead.dimension)}
  /-- The complete original last flag is exactly all its actual original vertices. -/
  last : ((coefficient bead).obj (Fin.last q.unop.len)).I = Set.univ

/-- The native original vertex quiver of all actual reduced flanked nondegenerate beads. -/
@[instance_reducible]
def quiver (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) : Quiver (K _⦋0⦌) where
  Hom x y := NormalBead K x y q

/-- Actual paths of the same original reduced flanked nondegenerate beads. -/
abbrev Path (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x y : K _⦋0⦌) :=
  @Quiver.Path (K _⦋0⦌) (quiver K q) x y

/-- The same original vertex and full generating-arrow inclusion. -/
def inclusion (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    @Prefunctor (K _⦋0⦌) (quiver K q) (K _⦋0⦌) (quiverAt (generatingQuiver K) q) :=
  @Prefunctor.mk (K _⦋0⦌) (quiver K q) (K _⦋0⦌) (quiverAt (generatingQuiver K) q)
    (fun x => x) (fun {x y} (b : NormalBead K x y q) => b.bead.toArrow)

variable {K : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The same whole original coherent generating path, with no quotient of its vertex labels. -/
def originalPath (p : Path K q x y) : SimplicialQuiver.Path (generatingQuiver K) q x y :=
  @Prefunctor.mapPath (K _⦋0⦌) (quiver K q) (K _⦋0⦌) (quiverAt (generatingQuiver K) q)
    (inclusion K q) x y p

/-- The actual original raw coherent Hom value of the entire original reduced path. -/
def evaluation (p : Path K q x y) : (hom K x y).obj q :=
  _root_.Quotient.mk (congruence (relations K) q x y) (originalPath p)

/-- The actual original reduced empty path. -/
def empty (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x : K _⦋0⦌) : Path K q x x :=
  @Quiver.Path.nil (K _⦋0⦌) (quiver K q) x

/-- The actual original one-bead reduced path. -/
def singleton (b : NormalBead K x y q) : Path K q x y :=
  @Quiver.Hom.toPath (K _⦋0⦌) (quiver K q) x y b

/-- Native concatenation retains both entire original reduced paths. -/
def concat (p : Path K q x y) (r : Path K q y z) : Path K q x z :=
  @Quiver.Path.comp (K _⦋0⦌) (quiver K q) x y z p r

/-- The same original singleton path has precisely the original whole bead evaluation. -/
theorem evaluation_singleton (b : NormalBead K x y q) :
    evaluation (singleton b) = b.bead.evaluation := rfl

/-- The same original empty path is precisely the actual original presented identity representative. -/
theorem evaluation_empty (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x : K _⦋0⦌) :
    evaluation (empty K q x) =
      _root_.Quotient.mk (congruence (relations K) q x x)
        (@Quiver.Path.nil (K _⦋0⦌) (quiverAt (generatingQuiver K) q) x) := rfl

/-- Both entire original reduced paths evaluate to the same genuine original coherent composition. -/
theorem evaluation_concat (p : Path K q x y) (r : Path K q y z) :
    evaluation (concat p r) =
      (eComp SSet.{u} (C := realization K) x y z).app q (evaluation p, evaluation r) := by
  have h := @Prefunctor.mapPath_comp (K _⦋0⦌) (quiver K q)
    (K _⦋0⦌) (quiverAt (generatingQuiver K) q) (inclusion K q) x y p z r
  exact congrArg (_root_.Quotient.mk (congruence (relations K) q x z)) h

end CategoryTheory.CoherentRealization.OriginalBead.NormalForms
