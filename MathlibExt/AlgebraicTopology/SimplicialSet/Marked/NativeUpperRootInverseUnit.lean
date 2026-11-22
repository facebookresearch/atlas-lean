/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeUpperRootBoundaryUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryPositiveInverse
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerRootBoundaryCoordinates

/-!
# Exact original upper root-coordinate inverse identities

The genuine whole positive-chart inverse supplies the same original
native positive coefficient section at the root. Restricting through
each existing original marked upper face constructs its complete
coordinate inverse into the true all-face boundary source. The same
source map recovers the original upper inclusion and unchanged unit.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The entire actual original positive-chart inverse reads its same original positive-cone coefficient section in
the true native boundary source. -/
def nativePositiveRootBoundarySection {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) :
    coneAfterDiagram (⊥ : Vertex.{u} (n + 1)) ⟶
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).obj
        (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) :=
  EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
    (coneAfterDiagram (⊥ : Vertex.{u} (n + 1)))
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) (nativeBoundaryPositiveInverse B n σ)

/-- The original all-face source map keeps the unchanged complete positive-cone entry and original native
root-boundary unit on the entire original positive section. -/
theorem nativePositiveRootBoundarySection_source {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) :
    nativePositiveRootBoundarySection B σ ≫
        (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).map
          (nativeBoundaryRootSourceMap B n σ) =
      coneRootBoundaryAfterMap (n + 1) ≫
        EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram (n + 1)) := by
  let k := EnrichedFunctor.opposite (simplexInto B σ)
  let W := coneAfterDiagram (⊥ : Vertex.{u} (n + 1))
  let F := nativeRootBoundaryChart B (n + 1) σ
  let U := EnrichedLeftKan.universalHomEquiv k W F
  have hn := EnrichedLeftKan.universalHomEquiv_natural_right k W
    (nativeBoundaryPositiveInverse B n σ) (nativeBoundaryRootSourceMap B n σ)
  have hp := congrArg U (nativeBoundaryPositiveInverse_source B n σ)
  exact hn.symm.trans (hp.trans (EnrichedLeftKan.map_homEquiv k (coneRootBoundaryAfterMap (n + 1))))

/-- Every complete original marked upper-root coordinate maps into the actual native boundary source through its
unchanged existing positive-cone face entry. -/
def nativeUpperRootBoundaryInverse {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) :
    coneUpperFaceMarked (⊥ : Vertex.{u} (n + 1)) (ULift.up j) ⟶ nativeBoundarySourceRootValue B (n + 1) σ :=
  coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up j, hj⟩ ≫
    (nativePositiveRootBoundarySection B σ).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))

/-- The actual all-face source comparison recovers the exact original whole upper-root coordinate inclusion and
unchanged native unit from each genuine upper-coordinate inverse. -/
theorem nativeUpperRootBoundaryInverse_source {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) :
    nativeUpperRootBoundaryInverse B σ j hj ≫
        (nativeBoundaryRootSourceMap B n σ).app
          ((EnrichedFunctor.opposite (simplexInto B σ)).obj
            (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) =
      coneUpperRootFaceToBoundary j hj ≫
        (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ))
          (coneRootBoundaryDiagram (n + 1))).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) := by
  let p := coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up j, hj⟩
  let x := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))
  let u := (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ))
    (coneRootBoundaryDiagram (n + 1))).app x
  have hs := congrArg (fun a => a.app x) (nativePositiveRootBoundarySection_source B σ)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => p ≫ a) hs).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ u) (coneUpperFaceToAfter_rootBoundary j hj))))

end SSet.Marked
