/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryChart
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramProjectiveMonomorphisms

/-!
# Actual native weak attachments of the SAME supported enriched root horn

The actual original supported horn inclusion has its genuine full
weak-mono projective left class from its original marked free-root
pushout. Left extension over the SAME original full base simplex retains
that class and gives a genuine trivial cofibration in the actually
constructed coherent model over arbitrary original non-Kan bases. Every
full original component and whole original universal unit mate remain.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq
  coefficientMarkedModelCategory

/-- The SAME actual original supported horn diagram is left-extended over its entire unchanged original base simplex. -/
def nativeSupportedRootHornChart {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    EnrichedDiagram (realization B)ᵒᵖ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).obj (coneRootHornDiagram k)

/-- The SAME original left-extended supported inclusion enters the actual full original simplex chart by its
unchanged full map. -/
def nativeSupportedRootHornChartMap {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    nativeSupportedRootHornChart B σ k ⟶ nativeSimplexChart B (n + 1) σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneRootHornDiagramInclusion k)

/-- The SAME entire original supported horn inclusion left-extends over its unchanged original full base simplex,
retaining both entire original enriched carriers. -/
def nativeRootHornAttachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    Arrow (EnrichedDiagram (realization B)ᵒᵖ) :=
  Arrow.mk (nativeSupportedRootHornChartMap B σ k)

/-- The SAME original supported horn free-root square is its complete original marked enriched square left-extended
over the unchanged actual base simplex. -/
def nativeSupportedRootHornCocone {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    Cocone ((span (coneRootHornCellFreeMap k) (coneRootHornFreeLeg k)) ⋙
      EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))) :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).mapCocone (coneRootHornEnrichedCocone k)

/-- The SAME complete original native supported-horn free-root square is a genuine full marked enriched colimit over
every original base. -/
def nativeSupportedRootHornIsColimit {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    IsColimit (nativeSupportedRootHornCocone B σ k) := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let L := EnrichedLeftKan.leftExtension j
  let _ : PreservesColimitsOfShape WalkingSpan L :=
    ((EnrichedLeftKan.adjunction j).leftAdjoint_preservesColimits :
      PreservesColimitsOfSize.{0, 0} L).preservesColimitsOfShape
  let hPres : PreservesColimit (span (coneRootHornCellFreeMap k) (coneRootHornFreeLeg k)) L :=
    (inferInstance : PreservesColimitsOfShape WalkingSpan L).preservesColimit
  exact (hPres.preserves (coneRootHornEnrichedIsColimit k)).some

/-- Actual original native left extension retains the full original supported horn weak-mono projective left class
over every unchanged original simplicial base. -/
theorem nativeRootHornAttachment_projectiveWeakLeft {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      (nativeRootHornAttachment B σ k).hom :=
  enrichedLeftKan_freeLeft (EnrichedFunctor.opposite (simplexInto B σ)) coefficientGeneratingWeakMonos
    (coneRootHornDiagramInclusion k) (coneRootHornInclusion_projectiveWeakLeft k hk hk')

/-- The SAME original native supported-horn attaching map is genuinely a trivial cofibration in the actual original
coherent model for arbitrary original B. -/
theorem nativeRootHornAttachment_trivialCofibration {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ) (nativeRootHornAttachment B σ k).hom := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeRootHornAttachment_projectiveWeakLeft B σ k hk hk'

/-- Every complete original native supported-horn coefficient component is an actual coefficient trivial
cofibration, retaining its SAME full original map. -/
theorem nativeRootHornAttachment_component_trivialCofibration {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) (x : (realization B)ᵒᵖ) :
    trivialCofibrations Marked.{u} ((nativeRootHornAttachment B σ k).hom.app x) := by
  let _ := coherentDiagramModelCategory B
  let f := (nativeRootHornAttachment B σ k).hom
  have ht := nativeRootHornAttachment_trivialCofibration B σ k hk hk'
  have hc : (coherentDiagramGeneratingMonos B).rlp.llp f := ht.1
  have hw : coherentDiagramWeakEquivalences B f := ht.2
  exact ⟨coherentDiagram_projectiveLeft_evaluation_cofibration B f hc x,
    (EvaluationTransfer.evaluationProperty_iff
      (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c)
      (weakEquivalences Marked.{u}) f).mp hw x⟩

/-- The SAME actual native supported horn attachment retains its exact original whole universal unit mate over the
unchanged original full base simplex. -/
theorem nativeRootHornAttachment_unit {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
      (coneRootHornDiagram k) (nativeRootHornAttachment B σ k).right (nativeRootHornAttachment B σ k).hom =
        coneRootHornDiagramInclusion k ≫ EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ))
          (coneDiagram (n + 1)) :=
  EnrichedLeftKan.map_homEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootHornDiagramInclusion k)

end SSet.Marked
