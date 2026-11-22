/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeMappingEquivalence

/-!
# Whole actual original mapping evaluation naturality

The actual resolving quotient map follows the supplied original
right-join operator. Its genuine realization and counit therefore
retain the entire original evaluation functor and Hom maps. Together
with the proved cube chart this gives all scalar operator squares,
without any mapping-weak or Kan outcome assumption.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.CubeMappingNaturality
open SimplicialEnrichment FixedFrontCollapse FixedFrontEvaluation HornHomFaces
variable {C : Carrier.{u}} {n m : ℕ} (x y : C)

/-- The actual original resolving quotient map follows every supplied right-mapping simplex operator on the
  entire successor simplex. -/
theorem quotient_naturality (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋m⦌) :
    FixedFrontOperators.map θ ≫ quotientMap x y σ =
      quotientMap x y ((SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
        (HomSimplexEndpoints.vertex y)).map θ.op σ) := by
  let σn := (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)).map θ.op σ
  have h : projection n ≫ (FixedFrontOperators.map θ ≫ quotientMap x y σ) = projection n ≫ quotientMap x y σn :=
    (Category.assoc (projection n) (FixedFrontOperators.map θ) (quotientMap x y σ)).symm.trans
      ((congrArg (fun f => f ≫ quotientMap x y σ) (FixedFrontOperators.projection_map θ)).trans
        ((Category.assoc (SSet.stdSimplex.map (PathMaximumOperators.extension θ)) (projection m)
          (quotientMap x y σ)).trans
          ((congrArg (fun f => SSet.stdSimplex.map (PathMaximumOperators.extension θ) ≫ f)
            (quotientMap_readback x y σ)).trans
            ((RightMappingSimplex.transported_operator x y θ σ).symm.trans (quotientMap_readback x y σn).symm))))
  ext q a
  induction a using _root_.Quotient.inductionOn with
  | _ p => exact congr($(h).app q p)

/-- The entire actual original evaluation functor is natural for every right-join operator and the same
  supplied original endpoints. -/
theorem functor_naturality (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋m⦌) :
    realizationMap (FixedFrontOperators.map θ) ≫ FixedFrontEvaluation.functor x y σ =
      FixedFrontEvaluation.functor x y
        ((SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
          (HomSimplexEndpoints.vertex y)).map θ.op σ) :=
  (Category.assoc (realizationMap (FixedFrontOperators.map θ)) (realizationMap (quotientMap x y σ)) (counit
    C)).symm.trans
    ((congrArg (fun F => F ≫ counit C) (realizationMap_comp (FixedFrontOperators.map θ) (quotientMap x y σ)).symm).trans
      (congrArg (fun q => realizationMap q ≫ counit C) (quotient_naturality x y θ σ)))

/-- The actual original source-to-target resolving Hom evaluation follows the same whole right-join operator. -/
theorem homMap_naturality (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋m⦌) :
    RightHomResolution.map θ ≫ FixedFrontEvaluation.homMap x y σ =
      FixedFrontEvaluation.homMap x y
        ((SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
          (HomSimplexEndpoints.vertex y)).map θ.op σ) := by
  let F := realizationMap (FixedFrontOperators.map θ)
  let G := FixedFrontEvaluation.functor x y σ
  let σn := (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)).map θ.op σ
  have hr := HomRetargetAlgebra.restriction_reindex F G (source n) (target n)
    (FixedFrontVertices.map_source θ) (FixedFrontVertices.map_target θ) (functor_source x y σ) (functor_target x y σ)
  have he := retargetMap_eq (functor_naturality x y θ σ) (source n) (target n)
    ((congrArg G.obj (FixedFrontVertices.map_source θ)).trans (functor_source x y σ))
    ((congrArg G.obj (FixedFrontVertices.map_target θ)).trans (functor_target x y σ))
    (functor_source x y σn) (functor_target x y σn)
  exact (Category.assoc (F.map (source n) (target n))
    (eqToHom (congrArg₂ (fun a b : realization (FixedFrontCollapse.object.{u} m) => a ⟶[SSet.{u}] b)
      (FixedFrontVertices.map_source θ) (FixedFrontVertices.map_target θ))) (FixedFrontEvaluation.homMap x y σ)).trans
    (hr.trans he)

/-- The whole actual original cube Hom evaluation commutes with every supplied right-mapping face and degeneracy. -/
theorem evaluate_naturality (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋m⦌) :
    RightCubeCosimplicialMaps.map θ ≫ FixedFrontMappingEvaluation.evaluate x y σ =
      FixedFrontMappingEvaluation.evaluate x y
        ((SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
          (HomSimplexEndpoints.vertex y)).map θ.op σ) :=
  (Category.assoc (RightCubeCosimplicialMaps.map θ) (FixedFrontCubeMap.cubeMap m)
    (FixedFrontEvaluation.homMap x y σ)).symm.trans
    ((congrArg (fun f => f ≫ FixedFrontEvaluation.homMap x y σ) (FixedFrontCubeOperators.map_naturality θ)).trans
      ((Category.assoc (FixedFrontCubeMap.cubeMap n) (RightHomResolution.map θ) (FixedFrontEvaluation.homMap
        x y σ)).trans
        (congrArg (fun f => FixedFrontCubeMap.cubeMap n ≫ f) (homMap_naturality x y θ σ))))

end CategoryTheory.CoherentRealization.CubeMappingNaturality
