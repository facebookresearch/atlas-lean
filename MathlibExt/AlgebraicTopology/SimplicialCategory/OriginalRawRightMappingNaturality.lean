/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomRetargetAlgebra
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMapNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontMappingEvaluation

/-!
# Whole original raw Hom evaluation squares and original counit

Every actual original quotient-Hom coefficient follows the full
right-mapping operator. On the SAME original coherent nerve,
postcomposition by the original counit recovers precisely the
existing complete original coefficient evaluation.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping
open SimplicialEnrichment FixedFrontCollapse
variable {K : SSet.{u}} {n m : ℕ}
  (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The SAME complete original raw coefficient Hom is natural for every original right-mapping face and degeneracy. -/
theorem homEvaluation_operator (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight K a b) _⦋m⦌) :
    RightHomResolution.map θ ≫ homEvaluation a b σ =
      homEvaluation a b ((SSet.mappingSpaceRight K a b).map θ.op σ) := by
  let F := realizationMap (FixedFrontOperators.map θ)
  let G := evaluation a b σ
  let σn := (SSet.mappingSpaceRight K a b).map θ.op σ
  have hr := HomRetargetAlgebra.restriction_reindex F G (source n) (target n)
    (FixedFrontVertices.map_source θ) (FixedFrontVertices.map_target θ)
    (evaluation_source a b σ) (evaluation_target a b σ)
  have he := HornHomFaces.retargetMap_eq (evaluation_operator a b θ σ) (source n) (target n)
    ((congrArg G.obj (FixedFrontVertices.map_source θ)).trans (evaluation_source a b σ))
    ((congrArg G.obj (FixedFrontVertices.map_target θ)).trans (evaluation_target a b σ))
    (evaluation_source a b σn) (evaluation_target a b σn)
  exact (Category.assoc (F.map (source n) (target n))
    (eqToHom (congrArg₂ (fun x y : realization (FixedFrontCollapse.object.{u} m) => x ⟶[SSet.{u}] y)
      (FixedFrontVertices.map_source θ) (FixedFrontVertices.map_target θ))) (homEvaluation a b σ)).trans
        (hr.trans he)

/-- The actual original quotient-cube coefficient map into the SAME raw realization Hom. -/
def cubeEvaluation (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    RightCubeRelations.object.{u} n ⟶ hom K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b) :=
  (FixedFrontCubeIso.cubeIso n).hom ≫ homEvaluation a b σ

/-- All original cube operators retain the SAME whole raw Hom coefficient evaluation. -/
theorem cubeEvaluation_operator (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight K a b) _⦋m⦌) :
    RightCubeCosimplicialMaps.map θ ≫ cubeEvaluation a b σ =
      cubeEvaluation a b ((SSet.mappingSpaceRight K a b).map θ.op σ) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ homEvaluation a b σ)
      (FixedFrontCubeOperators.map_naturality θ)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun q => (FixedFrontCubeIso.cubeIso n).hom ≫ q)
            (homEvaluation_operator a b θ σ))))

variable {C : Carrier.{u}} (x y : C)

/-- On the SAME original nerve, the actual raw quotient map is the original whole fixed-front evaluation quotient map.
-/
theorem quotientMap_nerve
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
      (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    quotientMap (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) σ =
      FixedFrontEvaluation.quotientMap x y σ := rfl

/-- The SAME original raw coherent quotient evaluation postcomposed by the original counit is the original full enriched
evaluation. -/
theorem evaluation_counit
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
      (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    evaluation (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) σ ≫ counit C =
      FixedFrontEvaluation.functor x y σ := rfl

/-- The complete original raw Hom coefficient followed by the SAME actual counit retains its whole fixed-front
coefficient evaluation. -/
theorem homEvaluation_counit
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
      (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    homEvaluation (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) σ ≫
      (counit C).map (SSet.yonedaEquiv (HomSimplexEndpoints.vertex x))
        (SSet.yonedaEquiv (HomSimplexEndpoints.vertex y)) =
      FixedFrontEvaluation.homMap x y σ := by
  have h := HornMapNaturality.retargetMap_postcompose
    (evaluation (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) σ) (counit C)
    (source n) (target n)
    (evaluation_source (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) σ)
    (evaluation_target (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) σ)
  exact h

/-- The SAME complete original quotient-cube coefficient followed by the original counit is literally the existing full
cube evaluation. -/
theorem cubeEvaluation_counit
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
      (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    cubeEvaluation (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) σ ≫
      (counit C).map (SSet.yonedaEquiv (HomSimplexEndpoints.vertex x))
        (SSet.yonedaEquiv (HomSimplexEndpoints.vertex y)) =
      FixedFrontMappingEvaluation.evaluate x y σ :=
  (Category.assoc _ _ _).trans
    (congrArg (fun q => (FixedFrontCubeIso.cubeIso n).hom ≫ q) (homEvaluation_counit x y σ))

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
