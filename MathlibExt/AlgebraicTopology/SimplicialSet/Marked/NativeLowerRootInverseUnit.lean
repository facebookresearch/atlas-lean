/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerRootUnitTransport

/-!
# The exact original lower root-coordinate inverse identity

Every genuine marked lower root-coordinate map into the actual native
boundary source recovers precisely its original supported root-face
inclusion and unchanged native unit under the all-face source map.
This proves the inverse identity on each whole original lower face;
their lower/lower and lower/upper intersection gluing is still required.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same all-face source comparison recovers exactly the whole original lower root-face inclusion followed by
its unchanged native root-boundary unit. -/
theorem nativeLowerRootBoundaryInverse_source {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) :
    nativeLowerRootBoundaryInverse B σ j hj ≫
        (nativeBoundaryRootSourceMap B n σ).app
          ((EnrichedFunctor.opposite (simplexInto B σ)).obj
            (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) =
      coneLowerRootFaceToBoundary j hj ≫
        (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ))
          (coneRootBoundaryDiagram (n + 1))).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) := by
  let e := coneLowerRootFaceIso.{u} j hj
  let g := coneLowerRootFaceToBoundary.{u} j hj
  let u := (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ))
    (coneRootBoundaryDiagram (n + 1))).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
  have hs := nativeLowerRootBoundaryInverse_sourceTransport B σ j hj
  have hu := nativeLowerRootProperSection_unit B σ j hj
  exact hs.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun a => e.inv ≫ a) hu).trans
      ((congrArg (fun a => e.inv ≫ a) (Category.assoc e.hom g u)).trans
        (e.inv_hom_id_assoc (g ≫ u)))))

end SSet.Marked
