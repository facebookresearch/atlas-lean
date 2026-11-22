/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerRootBoundaryCoordinates

/-!
# Genuine original lower root-coordinate maps into the native boundary source

The complete marked coface-root isomorphism and the actual original
native coface unit construct the entire lower root-coordinate map.
Its target is transported only along the proved original root/base
equality. The original all-face source comparison reads the same
proper-coface section at that original root. Full lower/upper gluing
and the complete source isomorphism remain separate proofs.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The whole actual original lower root-coordinate face maps into the genuine native all-face boundary source
through its original coface unit and same root/base transport. -/
def nativeLowerRootBoundaryInverse {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) :
    coneLowerRootFaceWeight.{u} j ⟶ nativeBoundarySourceRootValue B (n + 1) σ :=
  ((coneLowerRootFaceIso j hj).inv ≫ nativeLowerCofaceRootSection B σ j) ≫
    eqToHom (nativeLowerCofaceRootTarget B σ j hj
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))))

/-- The same all-face source comparison reads the exact original whole proper-coface section at its original smaller
root coefficient. -/
theorem nativeLowerCofaceRootSection_source {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) :
    nativeLowerCofaceRootSection B σ j ≫
        (nativeBoundaryRootSourceMap B n σ).app
          ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))).obj
            (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) =
      (nativeProperBoundaryFaceSection B (SimplexCategory.δ j) σ
        (coneCofaceEmbedding_not_surjective j)).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) := by
  let k := EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))
  let F := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  let G := nativeRootBoundaryChart B (n + 1) σ
  let U := EnrichedLeftKan.universalHomEquiv k (coneDiagram n) G
  have hn := EnrichedLeftKan.universalHomEquiv_natural_right k (coneDiagram n)
    (nativeBoundaryCofaceChartMap B n σ j) (nativeBoundaryRootSourceMap B n σ)
  have hc := congrArg U (nativeBoundaryCofaceChartMap_root B n σ j)
  have hr := nativeProperBoundaryFaceMap_homEquiv B (SimplexCategory.δ j) σ
    (coneCofaceEmbedding_not_surjective j)
  have hs : EnrichedLeftKan.universalHomEquiv k (coneDiagram n) F (nativeBoundaryCofaceChartMap B n σ j) ≫
      (enrichedDiagramRestrict k).map (nativeBoundaryRootSourceMap B n σ) =
        nativeProperBoundaryFaceSection B (SimplexCategory.δ j) σ
          (coneCofaceEmbedding_not_surjective j) := hn.symm.trans (hc.trans hr)
  exact congrArg (fun a => a.app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) hs

end SSet.Marked
