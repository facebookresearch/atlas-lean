/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeEvaluationCounitWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingRealization

/-!
# Genuine weakness of the SAME original coherent counit comparison composite

On each original Kan Hom, the actual raw right-mapping comparison
followed by the SAME original coherent counit is weak. The whole
composite is the original quotient-cube singular evaluation under
the genuine entire mapping-space isomorphism. Weakness of the raw
comparison itself remains a separate geometric statement.
-/

noncomputable section
universe u
open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping
open SimplicialEnrichment
variable {C : Carrier.{u}} (x y : C)

/-- The SAME entire original counit evaluation factors through the actual full mapping-space/singular-complex
isomorphism. -/
theorem counitEvaluation_factor :
    counitEvaluation x y =
      OriginalRightCubeRealization.map (CubeMappingSpace.iso x y).hom ≫
        OriginalRightCubeRealization.evaluationCounit (x ⟶[SSet.{u}] y) := by
  apply colimit.hom_ext
  intro e
  have hInsert := colimit.ι_desc (counitEvaluationCocone x y) e
  have hMap := OriginalRightCubeRealization.insertion_map (CubeMappingSpace.iso x y).hom e
  have hEval := OriginalRightCubeRealization.insertion_evaluationCounit (x ⟶[SSet.{u}] y)
    ((CubeMappingSpace.iso x y).hom.mapElements.op.obj e)
  exact hInsert.trans
    ((hEval.symm.trans
      (congrArg (fun q => q ≫ OriginalRightCubeRealization.evaluationCounit (x ⟶[SSet.{u}] y))
        hMap.symm)).trans (Category.assoc _ _ _))

/-- The SAME genuine entire original right-mapping singular evaluation is weak whenever its original coefficient Hom is
Kan. -/
theorem counitEvaluation_weak [SSet.KanComplex (x ⟶[SSet.{u}] y)] :
    SSet.realizationWeakEquivalences (counitEvaluation x y) := by
  have hi : SSet.realizationWeakEquivalences
      (OriginalRightCubeRealization.map (CubeMappingSpace.iso x y).hom) :=
    (OriginalRightCubeRealization.map_weak_iff _).mpr (SSet.realizationWeakEquivalences.of_isIso _)
  have he := OriginalRightCubeRealization.evaluationCounit_weak (x ⟶[SSet.{u}] y)
  exact (counitEvaluation_factor x y).symm ▸
    SSet.realizationWeakEquivalences.comp_mem _ _ hi he

/-- The SAME full original raw comparison and complete original coherent counit have a genuinely weak composite on every
original Kan Hom. -/
theorem realizationComparison_counit_weak [SSet.KanComplex (x ⟶[SSet.{u}] y)] :
    SSet.realizationWeakEquivalences
      (realizationComparison (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) ≫
        (counit C).map (SSet.yonedaEquiv (HomSimplexEndpoints.vertex x))
          (SSet.yonedaEquiv (HomSimplexEndpoints.vertex y))) :=
  (realizationComparison_counit x y).symm ▸ counitEvaluation_weak x y

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
