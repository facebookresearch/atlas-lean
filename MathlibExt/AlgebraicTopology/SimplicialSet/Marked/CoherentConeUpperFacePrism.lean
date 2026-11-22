/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NervePreorderSubtype
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateFaces
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughPrism

/-!
# Actual marked upper-coordinate face and original free prism

The whole original upper-coordinate face is exactly the nerve of the
original through-subsets. The actual path/cone split therefore identifies
that entire marked face with the genuine coherent Hom/free coefficient
prism. Its original inclusion is precisely the full cone action, not a
chosen representative or desired colimit comparison.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The entire original through-subset nerve support is exactly its original upper coordinate face. -/
theorem throughSubcomplex_eq_upperFace {n : ℕ} (i j : Vertex.{u} n) :
    preorderSubtypeSubcomplex (fun a : ConeSubset i => j ∈ a.vertices) = coneCoordinateFace i j true := by
  ext q x
  simp only [preorderSubtypeSubcomplex, coneCoordinateFace, Set.mem_ofPred_eq, iff_true]

/-- The original through-subset nerve is the exact whole upper-face simplicial carrier. -/
def throughUpperFaceNerveIso {n : ℕ} (i j : Vertex.{u} n) :
    (coneThroughWeight i j).toSSet ≅ (coneCoordinateFace i j true : SSet.{u}) :=
  nervePreorderSubtypeIso (fun a : ConeSubset i => j ∈ a.vertices) ≪≫
    Subcomplex.eqToIso (throughSubcomplex_eq_upperFace i j)

/-- The entire actual upper coordinate face carries precisely its pulled-back original cone marking. -/
def coneUpperFaceMarked {n : ℕ} (i j : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight i) (coneCoordinateFace i j true).ι

/-- The original through-subset and upper-coordinate carriers are genuinely isomorphic as whole marked
  simplicial sets. -/
def throughUpperFaceIso {n : ℕ} (i j : Vertex.{u} n) :
    coneThroughWeight i j ≅ coneUpperFaceMarked i j :=
  isoMk (throughUpperFaceNerveIso i j) (fun _ => Iff.rfl)

/-- The actual full original upper-face inclusion retains every original simplex and its marking. -/
def coneUpperFaceInclusion {n : ℕ} (i j : Vertex.{u} n) : coneUpperFaceMarked i j ⟶ coneWeight i :=
  comapHom (coneWeight i) (coneCoordinateFace i j true).ι

/-- The genuine through-face source isomorphism retains exactly the original whole subset inclusion. -/
theorem throughUpperFaceIso_inclusion {n : ℕ} (i j : Vertex.{u} n) :
    (throughUpperFaceIso i j).hom ≫ coneUpperFaceInclusion i j = throughWeightInclusion i j := by
  apply Hom.ext
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- Every actual original upper coordinate face is its whole marked original coherent Hom/free upper-cone prism. -/
def coneUpperFacePrismIso {n : ℕ} (i j : Vertex.{u} n) :
    coneUpperFaceMarked i j ≅ prod (max (nerve (SimplicialThickening.Path i j))) (coneWeight j) :=
  (throughUpperFaceIso i j).symm ≪≫ throughPrismIso i j

/-- The inverse original upper-face prism followed by its complete original inclusion is exactly the full
  native cone path action. -/
theorem coneUpperFacePrism_inv_inclusion {n : ℕ} (i j : Vertex.{u} n) :
    (coneUpperFacePrismIso i j).inv ≫ coneUpperFaceInclusion i j = coneAction i j := by
  change ((throughPrismIso i j).inv ≫ (throughUpperFaceIso i j).hom) ≫ coneUpperFaceInclusion i j = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (throughPrismIso i j).inv ≫ f) (throughUpperFaceIso_inclusion i j)).trans
      (throughPrism_inv_inclusion i j))

end SSet.Marked.CoherentWeight
