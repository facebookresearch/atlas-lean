/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightElementsRawHocolim

/-!
# The SAME original raw right-Q BK evaluation is weak

The full original coefficient cocone triangle and actual BK index
comparison retain every original right-mapping simplex and quotient
map. The proved same fixed-front augmentation and exact endpoint
isomorphism yield weakness of this original cube-evaluation augmentation.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction OriginalPointed OriginalGadgetComparison

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- Every SAME original right-Q coefficient retains the complete original contained-lift augmentation triangle. -/
theorem rightElementsRawCoefficientLift_augmentation (e : (SSet.mappingSpaceRight K a b).Elementsᵒᵖ) :
    (rightElementsRawCoefficientLift a b).app e ≫
      (fixedFrontRawInputAugmentation (pointedInput a b)).app ((rightElementsInputFunctor a b).obj e) =
    SSet.uliftFunctor.{u,u}.map ((rightElementsEvaluationAugmentation a b).app e) ≫
      ((SSet.uliftContainedIso.{u,0} (hom K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b))).hom ≫
        (boundaryRawHomIso K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).hom) := by
  have hEval := rightElementsRawCoefficient_evaluation a b e
  have hLift := SSet.uliftContainedIso_naturality.{u,0} (cubeEvaluation a b e.unop.val)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (SSet.uliftContainedIso.{u,0}
      ((OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b)).obj e)).hom ≫ f) hEval).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ (boundaryRawHomIso K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).hom) hLift.symm).trans
          (Category.assoc _ _ _))))

/-- The SAME full original cube-evaluation BK augmentation is weak for every original quasicategory and both original
endpoint maps. -/
theorem rightElementsEvaluationAugmentation_weak [SSet.Quasicategory K] :
    SSet.realizationWeakEquivalences (SSet.bkAugmentation (rightElementsEvaluationAugmentation a b)) := by
  have hSquare := SSet.bkHocolimIndexMapULift_augmentationSquare.{u,0,0,0}
    (rightElementsInputFunctor a b) (rightElementsRawCoefficientLift a b)
    (rightElementsEvaluationAugmentation a b) (fixedFrontRawInputAugmentation (pointedInput a b))
    ((SSet.uliftContainedIso.{u,0} (hom K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b))).hom ≫
      (boundaryRawHomIso K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).hom)
    (rightElementsRawCoefficientLift_augmentation a b)
  have hTarget := fixedFrontRawInputAugmentation_weak K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)
  have hComposite := SSet.realizationWeakEquivalences.comp_mem _ _ (rightElementsRawIndexMap_weak a b) hTarget
  have hIso := SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso (SSet.uliftContainedIso.{u,0}
      (hom K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b))).hom)
    (SSet.realizationWeakEquivalences.of_isIso (boundaryRawHomIso K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)).hom)
  have hLift := SSet.realizationWeakEquivalences.of_postcomp _ _ hIso (hSquare ▸ hComposite)
  exact (SSet.realizationWeak_ulift_map_iff.{u,u}
    (SSet.bkAugmentation (rightElementsEvaluationAugmentation a b))).mp hLift

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
