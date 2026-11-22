/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornBoundaryInclusion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeProperBoundaryOperator

/-!
# Every original eligible coface enters the SAME supported enriched horn

The full original coface image omits its literal original coordinate.
When it lands at root that coordinate is positive and is an eligible
original lower horn coordinate. Above root the supported horn retains
the whole original cone. Its marked image, original path action and full
attaching square are therefore retained in the SAME supported diagram.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- At an actual original root coefficient, each eligible original lower-coordinate image lies in the SAME complete
supported horn. -/
theorem coneRootHornSupport_mem_lower_of_root {n : ℕ} (k : Fin (n + 2))
    (r j : Vertex.{u} (n + 1)) (hr : r = ⊥) (hj : r < j) (hjk : j ≠ ULift.up k)
    (q : SimplexCategoryᵒᵖ) (a : (nerve (ConeSubset r)).obj q)
    (ha : a ∈ (coneCoordinateFace r j false).obj q) : a ∈ (coneRootHornSupport k r).obj q := by
  subst r
  apply (congrArg (fun A => a ∈ A.obj q) (coneRootHornSupport_root k)).to_iff.mpr
  apply (mem_coneRootCoordinateHorn_iff k q a).mpr
  right
  exact ⟨⟨j, hj, hjk⟩, (mem_coneCoordinateFace_false ⊥ j a).mp ha⟩

/-- Every entire original eligible coface image lies in the SAME original supported horn coefficient, through its
actual omitted coordinate. -/
theorem coneRootHornCofaceImage_mem {n : ℕ} (k j : Fin (n + 2)) (hjk : j ≠ k) (i : Vertex.{u} n)
    {q : SimplexCategoryᵒᵖ} (a : (nerve (ConeSubset i)).obj q) :
    (coneImage (coneCofaceEmbedding j).toOrderHom i).hom.app q a ∈
      (coneRootHornSupport k (coneCofaceEmbedding j i)).obj q := by
  let f := (coneCofaceEmbedding.{u} j).toOrderHom
  have hj : ∀ r, f r ≠ (ULift.up j : Vertex.{u} (n + 1)) := by
    intro r h
    exact Fin.succAbove_ne j r.down (congrArg ULift.down h)
  by_cases hi : f i = ⊥
  · have hj0 : (ULift.up j : Vertex.{u} (n + 1)) ≠ ⊥ := fun h => hj i (hi.trans h.symm)
    have hpos : (⊥ : Vertex.{u} (n + 1)) < ULift.up j := lt_of_le_of_ne bot_le (Ne.symm hj0)
    have hjk' : (ULift.up j : Vertex.{u} (n + 1)) ≠ ULift.up k :=
      fun h => hjk (congrArg ULift.down h)
    exact coneRootHornSupport_mem_lower_of_root k (f i) (ULift.up j) hi (hi.symm ▸ hpos) hjk' q
      ((coneImage f i).hom.app q a) (coneImage_omittedCoordinate f i (ULift.up j) hj a)
  · change (coneImage f i).hom.app q a ∈ (coneRootHornSupport k (f i)).obj q
    rw [coneRootHornSupport, ite_eq_right hi]
    exact Set.mem_univ _

/-- The SAME full original eligible coface image retains every original scalar word and inherited maximum mark in
the actual supported horn coefficient. -/
def coneRootHornCofaceImage {n : ℕ} (k j : Fin (n + 2)) (hjk : j ≠ k) (i : Vertex.{u} n) :
    coneWeight i ⟶ coneRootHornMarked k (coneCofaceEmbedding j i) where
  hom :=
    { app q := ↾fun a => ⟨(coneImage (coneCofaceEmbedding j).toOrderHom i).hom.app q a,
        coneRootHornCofaceImage_mem k j hjk i a⟩
      naturality q r f := by
        apply ConcreteCategory.hom_ext
        intro a
        apply Subtype.ext
        exact congr($((coneImage (coneCofaceEmbedding j).toOrderHom i).hom.naturality f) a) }
  preserve he := (coneImage (coneCofaceEmbedding j).toOrderHom i).preserve he

/-- The actual original eligible coface retains precisely its SAME complete original full-cone image map. -/
theorem coneRootHornCofaceImage_inclusion {n : ℕ} (k j : Fin (n + 2)) (hjk : j ≠ k) (i : Vertex.{u} n) :
    coneRootHornCofaceImage k j hjk i ≫ coneRootHornInclusion k (coneCofaceEmbedding j i) =
      coneImage (coneCofaceEmbedding j).toOrderHom i := Hom.ext rfl

/-- The SAME actual original horn coface image retains the complete original proper-boundary image under the literal
original support comparison. -/
theorem coneRootHornCofaceImage_boundary {n : ℕ} (k j : Fin (n + 2)) (hjk : j ≠ k) (i : Vertex.{u} n) :
    coneRootHornCofaceImage k j hjk i ≫ coneRootHornToBoundary k (coneCofaceEmbedding j i) =
      coneProperBoundaryImage (coneCofaceEmbedding j).toOrderHom (coneCofaceEmbedding_not_surjective j) i :=
  Hom.ext rfl

/-- Restrict the SAME original whole supported horn along its unchanged actual coface index operator. -/
def coneRootHornCofaceRestricted {n : ℕ} (k j : Fin (n + 2)) : EnrichedDiagram (Index.{u} n)ᵒᵖ :=
  (EnrichedFunctor.opposite (indexMap (coneCofaceEmbedding j).toOrderHom)).comp SSet.{u} (coneRootHornDiagram k)

/-- Every whole original eligible coface lifts to the SAME actual supported horn with all its original path actions. -/
def coneRootHornCofaceOperator {n : ℕ} (k j : Fin (n + 2)) (hjk : j ≠ k) :
    coneDiagram n ⟶ coneRootHornCofaceRestricted.{u} k j where
  app i := coneRootHornCofaceImage k j hjk i.unop.as
  naturality i r := by
    ext q h
    apply Hom.ext
    ext t a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun v => ConeSubset.image_prepend (coneCofaceEmbedding j).toOrderHom _ _)
      (fun _ _ _ => Subsingleton.elim _ _)

/-- The full original supported-horn coface followed by its unchanged root-boundary inclusion is exactly the SAME
original whole supported-boundary coface. -/
theorem coneRootHornCofaceOperator_boundary {n : ℕ} (k j : Fin (n + 2)) (hjk : j ≠ k) :
    coneRootHornCofaceOperator.{u} k j hjk ≫
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (coneCofaceEmbedding j).toOrderHom))).map
        (coneRootHornToBoundaryDiagramMap k) = coneRootBoundaryCoface j := by
  apply EnrichedDiagramMap.ext
  funext i
  exact coneRootHornCofaceImage_boundary k j hjk i.unop.as

end SSet.Marked.CoherentWeight
