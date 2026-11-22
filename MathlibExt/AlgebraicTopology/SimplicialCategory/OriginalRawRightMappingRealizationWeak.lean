/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightElementsRawEvaluationWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeHocolimAugmentationWeak

/-!
# The SAME original raw right-Q realization comparison is weak

The actual original Q-realization BK augmentation and original
cube-evaluation augmentation retain the entire original coefficient
cocone. Their exact square proves weakness of the SAME originally
defined realizationComparison at every quasicategory and both endpoints.
No locally Kan raw realization or desired weak outcome is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The SAME actual original Q-realization augmentation followed by the original raw comparison is precisely the
original complete cube-evaluation BK augmentation. -/
theorem hocolimAugmentation_realizationComparison :
    OriginalRightCubeRealization.hocolimAugmentation (SSet.mappingSpaceRight K a b) ≫ realizationComparison a b =
      SSet.bkAugmentation (rightElementsEvaluationAugmentation a b) := by
  have h := SSet.bkAugmentation_naturality
    (𝟙 (OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b)))
    (OriginalRightCubeRealization.inputAugmentation (SSet.mappingSpaceRight K a b))
    (rightElementsEvaluationAugmentation a b) (realizationComparison a b) (fun e => by
      change 𝟙 _ ≫ cubeEvaluation a b e.unop.val =
        OriginalRightCubeRealization.insertion (SSet.mappingSpaceRight K a b) e ≫ realizationComparison a b
      exact (Category.id_comp _).trans (insertion_realizationComparison a b e.unop.val).symm)
  have h' : SSet.bkAugmentation (rightElementsEvaluationAugmentation a b) =
      OriginalRightCubeRealization.hocolimAugmentation (SSet.mappingSpaceRight K a b) ≫ realizationComparison a b := by
    have hId := SSet.bkHocolimMap_id (OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b))
    exact (Category.id_comp _).symm.trans (hId ▸ h)
  exact h'.symm

/-- The SAME actual original raw right-Q realization comparison is genuinely weak for every original quasicategory and
both original endpoint maps. -/
theorem realizationComparison_weak [SSet.Quasicategory K] :
    SSet.realizationWeakEquivalences (realizationComparison a b) :=
  SSet.realizationWeakEquivalences.of_precomp _ _
    (OriginalRightCubeRealization.hocolimAugmentation_weak (SSet.mappingSpaceRight K a b))
    ((hocolimAugmentation_realizationComparison a b).symm ▸ rightElementsEvaluationAugmentation_weak a b)

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
