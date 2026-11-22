/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryUnitSquares

/-!
# Every original proper native simplex chart enters the same boundary chart

The whole supported proper cone operator is followed by the actual
native boundary unit and the original coherent base restriction
transport. Its original left-extension mate is the native proper-face
map. Unit naturality proves that its unchanged attaching composite is
exactly the original native simplex restriction, for every proper
operator and every original base.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The full proper-face section keeps the original supported operator, actual native unit, and whole original
base-restriction transport. -/
def nativeProperBoundaryFaceSection (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : B _⦋m⦌) (hf : ¬ Function.Surjective f.toOrderHom.uliftMap) :
    coneDiagram n ⟶
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))).obj
        (nativeRootBoundaryChart B m σ) :=
  (coneProperBoundaryOperator f.toOrderHom.uliftMap hf ≫
    (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap))).map
      (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram m))) ≫
    (eqToHom (nativeChartBase_restriction_comp B f σ)).app (nativeRootBoundaryChart B m σ)

/-- Every whole original proper native simplex chart enters the same actual left-extended complete root boundary by
its genuine unit mate. -/
def nativeProperBoundaryFaceMap (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : B _⦋m⦌) (hf : ¬ Function.Surjective f.toOrderHom.uliftMap) :
    nativeSimplexChart B n (B.map f.op σ) ⟶ nativeRootBoundaryChart B m σ :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
    (coneDiagram n) (nativeRootBoundaryChart B m σ)).symm
      (nativeProperBoundaryFaceSection B f σ hf)

/-- The actual native proper-face map reads precisely the same full supported operator and original unit transport. -/
theorem nativeProperBoundaryFaceMap_homEquiv (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (hf : ¬ Function.Surjective f.toOrderHom.uliftMap) :
    EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
      (coneDiagram n) (nativeRootBoundaryChart B m σ) (nativeProperBoundaryFaceMap B f σ hf) =
        nativeProperBoundaryFaceSection B f σ hf :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
    (coneDiagram n) (nativeRootBoundaryChart B m σ)).apply_symm_apply _

/-- The original whole supported proper-face section keeps the unchanged full-cone unit under the actual attaching
map and base transport. -/
theorem nativeProperBoundaryFaceSection_attachment (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (hf : ¬ Function.Surjective f.toOrderHom.uliftMap) :
    nativeProperBoundaryFaceSection B f σ hf ≫
        (enrichedDiagramRestrict
          (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))).map
          (nativeRootBoundaryChartMap B m σ) =
      (coneOperator f.toOrderHom.uliftMap ≫
        (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap))).map
          (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram m))) ≫
        eqToHom (nativeChartWholeOperatorTargetEq B f σ) := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let r := enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap))
  let R := enrichedDiagramRestrict j
  let Rf := enrichedDiagramRestrict
    (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
  let η₁ := EnrichedLeftKan.unit j (coneDiagram m)
  let h := nativeChartBase_restriction_comp B f σ
  let t₁ := (eqToHom h).app (nativeSimplexChart B m σ)
  let Rsrc := r.obj (R.obj (nativeSimplexChart B m σ))
  let Rdst := Rf.obj (nativeSimplexChart B m σ)
  have pasted : CommSq (coneOperator f.toOrderHom.uliftMap)
      ((coneProperBoundaryOperator f.toOrderHom.uliftMap hf ≫ r.map
        (EnrichedLeftKan.unit j (coneRootBoundaryDiagram m))) ≫
          (eqToHom h).app (nativeRootBoundaryChart B m σ))
      ((𝟙 (r.obj (coneDiagram m)) ≫ r.map η₁) ≫ t₁)
      (Rf.map (nativeRootBoundaryChartMap B m σ)) :=
    ((coneProperBoundaryImageSquare f.toOrderHom.uliftMap hf).vert_comp
      (r.map_commSq (nativeRootBoundaryUnitSquare B m σ))).vert_comp
        (nativeRootBoundaryBaseTransportSquare B f σ)
  have hremove := congrArg
    (fun v : r.obj (coneDiagram m) ⟶ Rsrc => coneOperator f.toOrderHom.uliftMap ≫ (v ≫ t₁))
      (Category.id_comp (r.map η₁))
  have happ : t₁ = eqToHom (nativeChartWholeOperatorTargetEq B f σ) := eqToHom_app h _
  have htransport := congrArg (fun v : Rsrc ⟶ Rdst =>
    (coneOperator f.toOrderHom.uliftMap ≫ r.map η₁) ≫ v) happ
  have hassoc : coneOperator f.toOrderHom.uliftMap ≫ (r.map η₁ ≫ t₁) =
      (coneOperator f.toOrderHom.uliftMap ≫ r.map η₁) ≫ t₁ := by
    apply EnrichedDiagramMap.ext
    funext x
    apply Hom.ext
    rfl
  have hlast := hassoc.trans htransport
  have hnormal := hremove.trans hlast
  have hs := pasted.w.symm.trans hnormal
  apply EnrichedDiagramMap.ext
  funext x
  exact congrArg (fun v : coneDiagram n ⟶ Rdst => v.app x)
    hs

/-- Every actual proper-face attaching composite is the original whole native simplex restriction, retaining all
original units and base maps. -/
theorem nativeProperBoundaryFaceMap_attachment (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (hf : ¬ Function.Surjective f.toOrderHom.uliftMap) :
    nativeProperBoundaryFaceMap B f σ hf ≫ nativeRootBoundaryChartMap B m σ =
      nativeSimplexChartRestriction B f σ := by
  apply (EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
      (coneDiagram n) (nativeSimplexChart B m σ)).injective
  exact (EnrichedLeftKan.universalHomEquiv_natural_right
    (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ))) (coneDiagram n)
      (nativeProperBoundaryFaceMap B f σ hf) (nativeRootBoundaryChartMap B m σ)).trans
        ((congrArg (fun t => t ≫ (enrichedDiagramRestrict
          (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))).map
            (nativeRootBoundaryChartMap B m σ)) (nativeProperBoundaryFaceMap_homEquiv B f σ hf)).trans
              ((nativeProperBoundaryFaceSection_attachment B f σ hf).trans
                (nativeChartRestriction_whole_operator B f σ)))

/-- Every ordered original coface gives its actual whole native map into the same supported boundary chart. -/
def nativeRootBoundaryCofaceMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    nativeSimplexChart B n (B.map (SimplexCategory.δ i).op σ) ⟶ nativeRootBoundaryChart B (n + 1) σ :=
  nativeProperBoundaryFaceMap B (SimplexCategory.δ i) σ (coneCofaceEmbedding_not_surjective i)

/-- Each original native coface map keeps exactly the same whole native simplex attaching map. -/
theorem nativeRootBoundaryCofaceMap_attachment (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    nativeRootBoundaryCofaceMap B n σ i ≫ nativeRootBoundaryChartMap B (n + 1) σ =
      nativeSimplexChartRestriction B (SimplexCategory.δ i) σ :=
  nativeProperBoundaryFaceMap_attachment B (SimplexCategory.δ i) σ
    (coneCofaceEmbedding_not_surjective i)

end SSet.Marked
