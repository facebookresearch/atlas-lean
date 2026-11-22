/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornCofaceOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootHornBoundaryComparison

/-!
# Original eligible native coface maps into the SAME supported horn source

Every original eligible coface operator retains its whole marked image
in the actual supported horn. The SAME original left-extension unit and
coherent base-restriction transport give its native map. Original unit
naturality retains the full original simplex attaching map, and actual
boundary monicity reads exactly the unchanged original whole supported
boundary coface under the same source comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual full original eligible coface-image square retains its SAME original cone operator and complete
supported-horn inclusion. -/
theorem coneRootHornCofaceImageSquare {n : ℕ} (k j : Fin (n + 2)) (hjk : j ≠ k) :
    CommSq (coneOperator (SimplexCategory.δ j).toOrderHom.uliftMap) (coneRootHornCofaceOperator.{u} k j hjk)
      (𝟙 ((enrichedDiagramRestrict (EnrichedFunctor.opposite
        (indexMap (SimplexCategory.δ j).toOrderHom.uliftMap))).obj (coneDiagram (n + 1))))
      ((enrichedDiagramRestrict (EnrichedFunctor.opposite
        (indexMap (SimplexCategory.δ j).toOrderHom.uliftMap))).map (coneRootHornDiagramInclusion k)) := by
  constructor
  apply EnrichedDiagramMap.ext
  funext i
  apply Hom.ext
  rfl

/-- The SAME actual original supported-horn native unit square retains all original whole coefficient and
target-unit maps. -/
theorem nativeSupportedRootHornUnitSquare {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    CommSq (coneRootHornDiagramInclusion k)
      (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootHornDiagram k))
      (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram (n + 1)))
      ((enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).map
        (nativeSupportedRootHornChartMap B σ k)) :=
  ⟨(EnrichedLeftKan.adjunction (EnrichedFunctor.opposite (simplexInto B σ))).unit.naturality
    (coneRootHornDiagramInclusion k)⟩

/-- The SAME entire original base-restriction equality commutes with the unchanged original native supported-horn
attaching map. -/
theorem nativeSupportedRootHornBaseTransportSquare {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) :
    CommSq
      ((enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (SimplexCategory.δ j).toOrderHom.uliftMap))).map
        ((enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).map
          (nativeSupportedRootHornChartMap B σ k)))
      ((eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ j) σ)).app (nativeSupportedRootHornChart B σ k))
      ((eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ j) σ)).app (nativeSimplexChart B (n + 1) σ))
      ((enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))).map
        (nativeSupportedRootHornChartMap B σ k)) :=
  ⟨(eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ j) σ)).naturality
    (nativeSupportedRootHornChartMap B σ k)⟩

/-- The SAME original eligible coface section retains its full original supported operator, original native unit and
complete unchanged base-restriction transport. -/
def nativeHornProperFaceSection {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k j : Fin (n + 2))
    (hjk : j ≠ k) :
    coneDiagram n ⟶ (enrichedDiagramRestrict (EnrichedFunctor.opposite
      (simplexInto B (B.map (SimplexCategory.δ j).op σ)))).obj (nativeSupportedRootHornChart B σ k) :=
  (coneRootHornCofaceOperator k j hjk ≫
    (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (SimplexCategory.δ j).toOrderHom.uliftMap))).map
      (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootHornDiagram k))) ≫
    (eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ j) σ)).app (nativeSupportedRootHornChart B σ k)

/-- Each SAME actual original eligible native coherent coface chart maps to the entire original supported-horn chart
through its genuine original unit mate. -/
def nativeHornProperFaceMap {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k j : Fin (n + 2)) (hjk : j ≠ k) :
    nativeSimplexChart B n (B.map (SimplexCategory.δ j).op σ) ⟶ nativeSupportedRootHornChart B σ k :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))
    (coneDiagram n) (nativeSupportedRootHornChart B σ k)).symm (nativeHornProperFaceSection B σ k j hjk)

/-- The actual original eligible coface unit mate reads precisely its SAME full supported-horn section. -/
theorem nativeHornProperFaceMap_homEquiv {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) (hjk : j ≠ k) :
    EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))
      (coneDiagram n) (nativeSupportedRootHornChart B σ k) (nativeHornProperFaceMap B σ k j hjk) =
        nativeHornProperFaceSection B σ k j hjk :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))
    (coneDiagram n) (nativeSupportedRootHornChart B σ k)).apply_symm_apply _

/-- The SAME original entire eligible coface section retains the original full-cone unit and complete actual base
transport under its unchanged attaching map. -/
theorem nativeHornProperFaceSection_attachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) (hjk : j ≠ k) :
    nativeHornProperFaceSection B σ k j hjk ≫
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))).map
        (nativeSupportedRootHornChartMap B σ k) =
      (coneOperator (SimplexCategory.δ j).toOrderHom.uliftMap ≫
        (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (SimplexCategory.δ j).toOrderHom.uliftMap))).map
          (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram (n + 1)))) ≫
        eqToHom (nativeChartWholeOperatorTargetEq B (SimplexCategory.δ j) σ) := by
  let b := EnrichedFunctor.opposite (simplexInto B σ)
  let r := enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (SimplexCategory.δ j).toOrderHom.uliftMap))
  let R := enrichedDiagramRestrict b
  let Rf := enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))
  let η := EnrichedLeftKan.unit b (coneDiagram (n + 1))
  let h := nativeChartBase_restriction_comp B (SimplexCategory.δ j) σ
  let t := (eqToHom h).app (nativeSimplexChart B (n + 1) σ)
  let Rsrc := r.obj (R.obj (nativeSimplexChart B (n + 1) σ))
  let Rdst := Rf.obj (nativeSimplexChart B (n + 1) σ)
  have pasted : CommSq (coneOperator (SimplexCategory.δ j).toOrderHom.uliftMap)
      ((coneRootHornCofaceOperator k j hjk ≫ r.map (EnrichedLeftKan.unit b (coneRootHornDiagram k))) ≫
        (eqToHom h).app (nativeSupportedRootHornChart B σ k))
      ((𝟙 (r.obj (coneDiagram (n + 1))) ≫ r.map η) ≫ t)
      (Rf.map (nativeSupportedRootHornChartMap B σ k)) :=
    ((coneRootHornCofaceImageSquare k j hjk).vert_comp
      (r.map_commSq (nativeSupportedRootHornUnitSquare B σ k))).vert_comp
        (nativeSupportedRootHornBaseTransportSquare B σ k j)
  have hremove := congrArg
    (fun v : r.obj (coneDiagram (n + 1)) ⟶ Rsrc =>
      coneOperator (SimplexCategory.δ j).toOrderHom.uliftMap ≫ (v ≫ t)) (Category.id_comp (r.map η))
  have happ : t = eqToHom (nativeChartWholeOperatorTargetEq B (SimplexCategory.δ j) σ) := eqToHom_app h _
  have htransport := congrArg (fun v : Rsrc ⟶ Rdst =>
    (coneOperator (SimplexCategory.δ j).toOrderHom.uliftMap ≫ r.map η) ≫ v) happ
  have hassoc : coneOperator (SimplexCategory.δ j).toOrderHom.uliftMap ≫ (r.map η ≫ t) =
      (coneOperator (SimplexCategory.δ j).toOrderHom.uliftMap ≫ r.map η) ≫ t := by
    apply EnrichedDiagramMap.ext
    funext x
    apply Hom.ext
    rfl
  have hs := pasted.w.symm.trans (hremove.trans (hassoc.trans htransport))
  apply EnrichedDiagramMap.ext
  funext x
  exact congrArg (fun v : coneDiagram n ⟶ Rdst => v.app x) hs

/-- Every SAME original eligible native supported-horn coface attaching composite is the unchanged entire original
native simplex restriction. -/
theorem nativeHornProperFaceMap_attachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) (hjk : j ≠ k) :
    nativeHornProperFaceMap B σ k j hjk ≫ nativeSupportedRootHornChartMap B σ k =
      nativeSimplexChartRestriction B (SimplexCategory.δ j) σ := by
  apply (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))
    (coneDiagram n) (nativeSimplexChart B (n + 1) σ)).injective
  exact (EnrichedLeftKan.universalHomEquiv_natural_right
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))) (coneDiagram n)
      (nativeHornProperFaceMap B σ k j hjk) (nativeSupportedRootHornChartMap B σ k)).trans
        ((congrArg (fun t => t ≫ (enrichedDiagramRestrict
          (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ)))).map
            (nativeSupportedRootHornChartMap B σ k)) (nativeHornProperFaceMap_homEquiv B σ k j hjk)).trans
              ((nativeHornProperFaceSection_attachment B σ k j hjk).trans
                (nativeChartRestriction_whole_operator B (SimplexCategory.δ j) σ)))

/-- The SAME entire original eligible supported-horn native coface retains its unchanged original full root-boundary
coface under the actual support comparison. -/
theorem nativeHornProperFaceMap_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k j : Fin (n + 2)) (hjk : j ≠ k) :
    nativeHornProperFaceMap B σ k j hjk ≫ nativeSupportedRootHornToBoundary B σ k =
      nativeRootBoundaryCofaceMap B n σ j := by
  apply (cancel_mono (nativeRootBoundaryChartMap B (n + 1) σ)).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => nativeHornProperFaceMap B σ k j hjk ≫ f)
      (nativeSupportedRootHornToBoundary_attachment B σ k)).trans
        ((nativeHornProperFaceMap_attachment B σ k j hjk).trans
          (nativeRootBoundaryCofaceMap_attachment B n σ j).symm))

end SSet.Marked
