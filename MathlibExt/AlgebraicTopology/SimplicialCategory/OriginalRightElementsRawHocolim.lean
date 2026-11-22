/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightElementsInputNerveWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightElementsRawEvaluation

/-!
# The SAME original right-Q coefficient hocolim maps to the raw Hom weakly

Both complete original coefficient directions and the full original
input nerve map give the actual BK index comparison. Its SAME original
augmentation square and the proved full fixed-front augmentation give
weakness of the entire original cube-evaluation BK augmentation.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction OriginalPointed OriginalGadgetComparison

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The same full original quotient-cube coefficient maps have their actual original weak point maps. -/
theorem rightElementsCube_point_weak (e : (SSet.mappingSpaceRight K a b).Elementsᵒᵖ) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      ((OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b)).obj e)) := by
  let t := fixedFrontCubePointedIso.app e.unop.obj.unop
  have hPoint := (fixedFrontDegree_mappingGadget e.unop.obj.unop).1
  have h : t.hom ≫ SSet.stdSimplex.isTerminalObj₀.from (homObject (plainFixedFrontDiagram.obj e.unop.obj.unop)) =
      SSet.stdSimplex.isTerminalObj₀.from
        ((OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b)).obj e) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact h ▸ SSet.realizationWeakEquivalences.comp_mem _ _ (SSet.realizationWeakEquivalences.of_isIso t.hom) hPoint

/-- The SAME full original right-Q coefficient map with its actual contained universe lift. -/
def rightElementsRawCoefficientLift :
    OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b) ⋙ SSet.uliftFunctor.{u,u} ⟶
      rightElementsInputFunctor a b ⋙ fixedFrontRawInputDiagram (pointedInput a b) where
  app e := (SSet.uliftContainedIso.{u,0}
    ((OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b)).obj e)).hom ≫
      (rightElementsRawCoefficient a b).app e
  naturality e d f := by
    have hLift := SSet.uliftContainedIso_naturality.{u,0}
      ((OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b)).map f)
    have hCoeff := (rightElementsRawCoefficient a b).naturality f
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ (rightElementsRawCoefficient a b).app d) hLift).trans
        ((Category.assoc _ _ _).trans (congrArg (fun h =>
          (SSet.uliftContainedIso.{u,0}
            ((OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b)).obj e)).hom ≫ h) hCoeff)))

/-- The SAME original full right-Q input BK index map is weak by its actual original coefficient and input
dictionaries. -/
theorem rightElementsRawIndexMap_weak :
    SSet.realizationWeakEquivalences (SSet.bkHocolimIndexMapULift.{u,0,0,0}
      (rightElementsInputFunctor a b) (rightElementsRawCoefficientLift a b)) :=
  SSet.bkHocolimIndexMapULift_weak_of_pointCoefficients.{u,0,0,0} _ _
    (rightElementsCube_point_weak a b)
    (fun s => (fixedFrontDegree_mappingGadget s.left).1)
    (rightElementsInputFunctor_liftedNerve_weak a b)

/-- The SAME actual original full right-Q cube-evaluation BK augmentation. -/
def rightElementsEvaluationAugmentation :
    OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b) ⟶
      (CategoryTheory.Functor.const (SSet.mappingSpaceRight K a b).Elementsᵒᵖ).obj
        (hom K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)) := (evaluationCocone a b).ι

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
