/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerRootBoundaryInverse
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeLowerRootBoundaryUnit

/-!
# The original whole lower root-coordinate source readback

The actual lower coordinate map into the true native boundary source
keeps its exact proper-coface section under the all-face comparison.
Naturality along the proved original root/base object equality gives
the same whole marked target transport. No source-isomorphism or
lower/upper-gluing conclusion is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual complete lower-root coordinate inverse has the original proper-coface section and unchanged root/base
transport under the same whole all-face source map. -/
theorem nativeLowerRootBoundaryInverse_sourceTransport {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) :
    nativeLowerRootBoundaryInverse B σ j hj ≫
        (nativeBoundaryRootSourceMap B n σ).app
          ((EnrichedFunctor.opposite (simplexInto B σ)).obj
            (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) =
      ((coneLowerRootFaceIso j hj).inv ≫
        (nativeProperBoundaryFaceSection B (SimplexCategory.δ j) σ
          (coneCofaceEmbedding_not_surjective j)).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) ≫
        eqToHom (nativeLowerCofaceRootTarget B σ j hj (nativeRootBoundaryChart B (n + 1) σ)) := by
  let F := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  let G := nativeRootBoundaryChart B (n + 1) σ
  let a := nativeBoundaryRootSourceMap B n σ
  let x := (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j).op σ))).obj
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
  let y := (EnrichedFunctor.opposite (simplexInto B σ)).obj
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
  let e := coneLowerRootFaceIso.{u} j hj
  let f := nativeLowerCofaceRootSection B σ j
  let t := eqToHom (nativeLowerCofaceRootTarget B σ j hj F)
  let w := eqToHom (nativeLowerCofaceRootTarget B σ j hj G)
  have ht : t ≫ a.app y = a.app x ≫ w :=
    (eqToHom_naturality (fun c : (realization B)ᵒᵖ => a.app c)
      (nativeLowerCofaceRootObject B σ j hj)).symm
  have hs := nativeLowerCofaceRootSection_source B σ j
  exact (Category.assoc (e.inv ≫ f) t (a.app y)).trans
    ((congrArg (fun v => (e.inv ≫ f) ≫ v) ht).trans
      ((Category.assoc (e.inv ≫ f) (a.app x) w).symm.trans
        ((congrArg (fun v => v ≫ w) (Category.assoc e.inv f (a.app x))).trans
          (congrArg (fun v => (e.inv ≫ v) ≫ w) hs))))

end SSet.Marked
