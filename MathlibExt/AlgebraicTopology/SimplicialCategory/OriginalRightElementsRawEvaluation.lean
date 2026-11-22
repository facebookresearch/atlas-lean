/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightElementsInputDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNativeGadgetRawHomComparison

/-!
# The SAME full original right-Q coefficient cocone

The original quotient-cube coefficient chart followed by the literal
original pointed input Hom map is precisely the old cubeEvaluation,
with its actual original target endpoint isomorphism. Every original
coefficient and input map is retained in the full cocone square.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction OriginalPointed OriginalGadgetComparison

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- Every SAME original cube coefficient retains its complete raw evaluation and original endpoint transport. -/
theorem rightElementsRawCoefficient_evaluation (e : (SSet.mappingSpaceRight K a b).Elementsᵒᵖ) :
    (rightElementsRawCoefficient a b).app e ≫
      (fixedFrontRawInputAugmentation (pointedInput a b)).app ((rightElementsInputFunctor a b).obj e) =
    cubeEvaluation a b e.unop.val ≫ (boundaryRawHomIso K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).hom := by
  let n := e.unop.obj.unop.len
  let σ := e.unop.val
  have h : fixedFrontRightHomPointedIso.hom.app e.unop.obj.unop ≫ homFunctor.map (toPointedMap a b σ) =
      homEvaluation a b σ ≫ (boundaryRawHomIso K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).hom :=
    EnrichedFunctor.homMap_endpoint_square (realizationMap (quotientMap a b σ))
      (fixedFront_sourceVertex e.unop.obj.unop).symm (fixedFront_targetVertex e.unop.obj.unop).symm
      (sourceVertex_boundaryOneMap (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).symm
      (targetVertex_boundaryOneMap (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).symm
      (evaluation_source a b σ) (evaluation_target a b σ)
      (sourceVertex_map (toPointedMap a b σ)) (targetVertex_map (toPointedMap a b σ))
  change ((FixedFrontCubeIso.cubeIso n).hom ≫ fixedFrontRightHomPointedIso.hom.app e.unop.obj.unop) ≫
      homFunctor.map (toPointedMap a b σ) =
    ((FixedFrontCubeIso.cubeIso n).hom ≫ homEvaluation a b σ) ≫
      (boundaryRawHomIso K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (FixedFrontCubeIso.cubeIso n).hom ≫ f) h).trans (Category.assoc _ _ _).symm)

/-- The SAME complete original right-Q coefficient cocone is the actual original pointed input augmentation followed by
the same endpoint transport. -/
theorem rightElementsRawCoefficient_cocone :
    rightElementsRawCoefficient a b ≫
      Functor.whiskerLeft (rightElementsInputFunctor a b) (fixedFrontRawInputAugmentation (pointedInput a b)) =
    (evaluationCocone a b).ι ≫
      (CategoryTheory.Functor.const (SSet.mappingSpaceRight K a b).Elementsᵒᵖ).map
        (boundaryRawHomIso K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).hom := by
  apply NatTrans.ext
  funext e
  exact rightElementsRawCoefficient_evaluation a b e

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
