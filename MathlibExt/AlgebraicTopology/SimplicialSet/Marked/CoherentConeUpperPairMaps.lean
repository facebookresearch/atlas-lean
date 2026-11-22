/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughPairInclusion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SubcomplexFunctor

/-!
# Original intersection maps under the whole marked prism charts

The two original upper-face intersection maps become the actual cone
action and the actual free-diagram Hom composition, respectively.
Both equations retain the complete original path parameters, all
subset words and markings. They identify the maps of the marked
face diagram itself, rather than only their composites into the cone.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original entire upper-face inclusion is monic on its same marked carrier. -/
theorem coneUpperFaceInclusion_mono {n : ℕ} (i j : Vertex.{u} n) : Mono (coneUpperFaceInclusion i j) := by
  apply (mono_iff_underlying _).mpr
  change Mono (coneCoordinateFace i j true).ι
  infer_instance

/-- The whole original two-upper-face intersection includes in the original marked cone. -/
def coneUpperPairInclusion {n : ℕ} (i j k : Vertex.{u} n) :
    coneUpperPairMarked i j k ⟶ coneWeight i :=
  comapHom (coneWeight i) (coneCoordinateFace i j true ⊓ coneCoordinateFace i k true).ι

/-- The first original marked intersection map is the actual subcomplex inclusion into its first upper face. -/
def coneUpperPairFirst {n : ℕ} (i j k : Vertex.{u} n) :
    coneUpperPairMarked i j k ⟶ coneUpperFaceMarked i j :=
  (subcomplexFunctor (coneWeight i)).map (homOfLE inf_le_left)

/-- The second original marked intersection map is the actual inclusion into its second upper face. -/
def coneUpperPairSecond {n : ℕ} (i j k : Vertex.{u} n) :
    coneUpperPairMarked i j k ⟶ coneUpperFaceMarked i k :=
  (subcomplexFunctor (coneWeight i)).map (homOfLE inf_le_right)

/-- The whole first intersection map followed by its original face inclusion is the same original pair inclusion. -/
theorem coneUpperPairFirst_inclusion {n : ℕ} (i j k : Vertex.{u} n) :
    coneUpperPairFirst i j k ≫ coneUpperFaceInclusion i j = coneUpperPairInclusion i j k := by
  apply Hom.ext
  rfl

/-- The whole second intersection map followed by its original face inclusion retains the same pair inclusion. -/
theorem coneUpperPairSecond_inclusion {n : ℕ} (i j k : Vertex.{u} n) :
    coneUpperPairSecond i j k ≫ coneUpperFaceInclusion i k = coneUpperPairInclusion i j k := by
  apply Hom.ext
  rfl

/-- The actual pair-support isomorphism followed by the full cone inclusion is the original two-pivot subset map. -/
theorem throughPairIntersectionIso_inclusion {n : ℕ} (i j k : Vertex.{u} n) :
    (throughPairIntersectionIso i j k).hom ≫ coneUpperPairInclusion i j k =
      throughPairWeightInclusion i j k := by
  apply Hom.ext
  rfl

/-- The complete ordered pair prism includes by the actual two consecutive original cone actions. -/
theorem coneUpperPairPrism_inv_inclusion {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    (coneUpperPairPrismIso (i := i) hjk).inv ≫ coneUpperPairInclusion i j k =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path i j)))) (coneAction j k) ≫ coneAction i j := by
  change ((throughPairTriplePrismIso hjk).inv ≫ (throughPairIntersectionIso i j k).hom) ≫
    coneUpperPairInclusion i j k = _
  rw [Category.assoc, throughPairIntersectionIso_inclusion, throughPairTriplePrism_inv_inclusion]

/-- The original free-diagram action retains both complete coherent paths and the original last cone coefficient. -/
def coneFreeTwoPathAction {n : ℕ} (i j k : Vertex.{u} n) :
    prod (max (nerve (SimplicialThickening.Path i j)))
      (prod (max (nerve (SimplicialThickening.Path j k))) (coneWeight k)) ⟶
    prod (max (nerve (SimplicialThickening.Path i k))) (coneWeight k) :=
  enrichedDiagramAction
    (enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk k)) (coneWeight k))
    (op (SimplicialThickening.mk j)) (op (SimplicialThickening.mk i))

/-- Full original free Hom composition followed by the cone action is exactly the two original consecutive
  cone actions. -/
theorem coneFreeTwoPathAction_inclusion {n : ℕ} (i j k : Vertex.{u} n) :
    coneFreeTwoPathAction i j k ≫ coneAction i k =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path i j)))) (coneAction j k) ≫ coneAction i j := by
  apply Hom.ext
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  exact (ConeSubset.prepend_comp (x.1.obj t) (x.2.1.obj t) (x.2.2.obj t)).symm

/-- The first whole original intersection map is precisely the cone-action map between its marked prism charts. -/
theorem coneUpperPairPrism_inv_first {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    (coneUpperPairPrismIso (i := i) hjk).inv ≫ coneUpperPairFirst i j k =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path i j)))) (coneAction j k) ≫
        (coneUpperFacePrismIso i j).inv := by
  let _ : Mono (coneUpperFaceInclusion i j) := coneUpperFaceInclusion_mono i j
  apply (cancel_mono (coneUpperFaceInclusion i j)).mp
  rw [Category.assoc, coneUpperPairFirst_inclusion, coneUpperPairPrism_inv_inclusion,
    Category.assoc, coneUpperFacePrism_inv_inclusion]

/-- The second whole original intersection map is precisely the full free Hom-composition map between its
  marked prism charts. -/
theorem coneUpperPairPrism_inv_second {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    (coneUpperPairPrismIso (i := i) hjk).inv ≫ coneUpperPairSecond i j k =
      coneFreeTwoPathAction i j k ≫ (coneUpperFacePrismIso i k).inv := by
  let _ : Mono (coneUpperFaceInclusion i k) := coneUpperFaceInclusion_mono i k
  apply (cancel_mono (coneUpperFaceInclusion i k)).mp
  rw [Category.assoc, coneUpperPairSecond_inclusion, coneUpperPairPrism_inv_inclusion,
    Category.assoc, coneUpperFacePrism_inv_inclusion, coneFreeTwoPathAction_inclusion]

end SSet.Marked.CoherentWeight
