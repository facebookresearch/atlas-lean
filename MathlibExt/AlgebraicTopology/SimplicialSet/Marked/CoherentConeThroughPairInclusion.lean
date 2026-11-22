/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NervePreorderSubtype
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeUpperFacePrism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughPairPrism

/-!
# Actual whole upper-face intersections and native double action

The original two-pivot subset nerve is precisely the actual intersection
of the two original upper coordinate faces. The whole marked triple
prism keeps both original path coordinates. Its inverse followed by
original inclusion is exactly the two consecutive native cone actions,
retaining every original subset, mark and scalar operator.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual full original two-pivot support is exactly the original two-upper-face intersection. -/
theorem throughPairSubcomplex_eq_intersection {n : ℕ} (i j k : Vertex.{u} n) :
    preorderSubtypeSubcomplex (fun a : ConeSubset i => j ∈ a.vertices ∧ k ∈ a.vertices) =
      coneCoordinateFace i j true ⊓ coneCoordinateFace i k true := by
  ext q x
  change (∀ t, j ∈ (x.obj t).vertices ∧ k ∈ (x.obj t).vertices) ↔
    (∀ t, (j ∈ (x.obj t).vertices) ↔ true = true) ∧
      (∀ t, (k ∈ (x.obj t).vertices) ↔ true = true)
  simp only [iff_true, forall_and]

/-- The complete original marked upper-pair intersection retains its original cone marking. -/
def coneUpperPairMarked {n : ℕ} (i j k : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight i) (coneCoordinateFace i j true ⊓ coneCoordinateFace i k true).ι

/-- The entire original two-pivot nerve is the actual original upper-face intersection carrier. -/
def throughPairIntersectionNerveIso {n : ℕ} (i j k : Vertex.{u} n) :
    (coneThroughPairWeight i j k).toSSet ≅
      ((coneCoordinateFace i j true ⊓ coneCoordinateFace i k true : (nerve (ConeSubset i)).Subcomplex) : SSet.{u}) :=
  nervePreorderSubtypeIso (fun a : ConeSubset i => j ∈ a.vertices ∧ k ∈ a.vertices) ≪≫
    Subcomplex.eqToIso (throughPairSubcomplex_eq_intersection i j k)

/-- The actual whole original marked intersection is its unchanged full two-pivot subset carrier. -/
def throughPairIntersectionIso {n : ℕ} (i j k : Vertex.{u} n) :
    coneThroughPairWeight i j k ≅ coneUpperPairMarked i j k :=
  isoMk (throughPairIntersectionNerveIso i j k) (fun _ => Iff.rfl)

/-- The complete original two-pivot cone includes by its same whole marked subset map. -/
def throughPairWeightInclusion {n : ℕ} (i j k : Vertex.{u} n) : coneThroughPairWeight i j k ⟶ coneWeight i :=
  comapHom (coneWeight i) (nerveMap (throughPairForgetFunctor i j k))

/-- The entire inverse first-path/remaining-through prism includes by exactly the original cone action on
  the same remaining original subset. -/
theorem throughPairPrism_inv_inclusion {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    (throughPairPrismIso hjk).inv ≫ throughPairWeightInclusion i j k =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path i j)))) (throughWeightInclusion j k) ≫ coneAction i j := by
  apply Hom.ext
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- The original whole inverse triple prism includes by the actual consecutive original cone actions, with
  both full path coordinates and marks retained. -/
theorem throughPairTriplePrism_inv_inclusion {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    (throughPairTriplePrismIso hjk).inv ≫ throughPairWeightInclusion i j k =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path i j)))) (coneAction j k) ≫ coneAction i j := by
  let A := max (nerve (SimplicialThickening.Path i j))
  change (prodMap (𝟙 A) (throughPrismIso j k).inv ≫ (throughPairPrismIso hjk).inv) ≫
    throughPairWeightInclusion i j k = _
  rw [Category.assoc, throughPairPrism_inv_inclusion, ← Category.assoc, ← prodMap_comp,
    Category.id_comp, throughPrism_inv_inclusion]

/-- The entire actual ordered upper-face intersection is the genuine original marked two-path/upper-cone prism. -/
def coneUpperPairPrismIso {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    coneUpperPairMarked i j k ≅
      prod (max (nerve (SimplicialThickening.Path i j)))
        (prod (max (nerve (SimplicialThickening.Path j k))) (coneWeight k)) :=
  (throughPairIntersectionIso i j k).symm ≪≫ throughPairTriplePrismIso hjk

end SSet.Marked.CoherentWeight
