/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeHocolimAugmentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubePoint
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveULiftToTargetWeak

/-!
# The SAME original quotient-cube BK realization augmentation is weak

All complete original cube coefficients have their actual point
weakness. The canonical full original elements/simplex dictionary and
its exact maximum augmentation square compare to the proved original
standard-simplex resolution. The SAME all-input original maximum then
proves weakness of the actual Q-realization augmentation.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- Every SAME original quotient-cube coefficient has its genuine original weak point map. -/
theorem diagram_point_weak (K : SSet.{u}) (e : K.Elementsᵒᵖ) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from ((diagram K).obj e)) := by
  have h := SSet.realizationWeakEquivalences.comp_mem _ _
    (RightCubeWeakComparison.maximum_weak e.unop.obj.unop.len)
    (SSet.stdSimplex_to_point_mem_realizationWeakEquivalences e.unop.obj.unop)
  have he : RightCubeMaximum.map e.unop.obj.unop.len ≫
      SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj e.unop.obj.unop) =
      SSet.stdSimplex.isTerminalObj₀.from ((diagram K).obj e) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ h

/-- The SAME original full elements/simplex index map is weak with its actual original contained coefficient lift. -/
theorem elementsToSimplex_nerve_weak (K : SSet.{u}) :
    SSet.realizationWeakEquivalences (SSet.nerveMapULiftToTarget.{u,0,0,0} (elementsToSimplex K)) :=
  (SSet.nerveMapULiftToTarget_weak_iff (elementsToSimplex K)).mpr
    (nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
      (Functor.Elements.costructuredArrowULiftYonedaEquivalence.{u,0,0} K).functor)

/-- The SAME original quotient-cube-to-standard-simplex BK index map is genuinely weak on every original input. -/
theorem maximumDiagramIndexMap_weak (K : SSet.{u}) :
    SSet.realizationWeakEquivalences
      (SSet.bkHocolimIndexMapULift.{u,0,0,0} (elementsToSimplex K) (maximumDiagramMap K)) :=
  SSet.bkHocolimIndexMapULift_weak_of_pointCoefficients.{u,0,0,0} _ _
    (diagram_point_weak K) (SSet.originalSimplexDiagram_point_weak K) (elementsToSimplex_nerve_weak K)

/-- The SAME original complete quotient-cube BK maximum augmentation is weak for every original input. -/
theorem maximumCocone_hocolim_weak (K : SSet.{u}) :
    SSet.realizationWeakEquivalences (SSet.bkAugmentation (maximumCocone K).ι) := by
  have hSquare := SSet.bkHocolimIndexMapULift_augmentationSquare.{u,0,0,0}
    (elementsToSimplex K) (maximumDiagramMap K) (maximumCocone K).ι (SSet.originalSimplexCocone K)
    (SSet.uliftContainedIso.{u,0} K).hom (maximumDiagramMap_augmentation K)
  have hComposite := SSet.realizationWeakEquivalences.comp_mem _ _
    (maximumDiagramIndexMap_weak K) (SSet.originalSimplexAugmentation_weak K)
  have hLift := SSet.realizationWeakEquivalences.of_postcomp _ _
    (SSet.realizationWeakEquivalences.of_isIso (SSet.uliftContainedIso.{u,0} K).hom) (hSquare ▸ hComposite)
  exact (SSet.realizationWeak_ulift_map_iff.{u,u} (SSet.bkAugmentation (maximumCocone K).ι)).mp hLift

/-- The SAME full original cube-realization BK augmentation followed by its actual original maximum is precisely the
full original maximum cocone augmentation. -/
theorem hocolimAugmentation_maximum (K : SSet.{u}) :
    hocolimAugmentation K ≫ maximum K = SSet.bkAugmentation (maximumCocone K).ι := by
  have h := SSet.bkAugmentation_naturality (𝟙 (diagram K)) (inputAugmentation K) (maximumCocone K).ι
    (maximum K) (fun e => by
      change 𝟙 _ ≫ (maximumCocone K).ι.app e = insertion K e ≫ maximum K
      exact (Category.id_comp _).trans (insertion_maximum K e).symm)
  rw [SSet.bkHocolimMap_id, Category.id_comp] at h
  exact h.symm

/-- The SAME actual original quotient-cube BK augmentation to its genuine original realization is weak for EVERY
original simplicial input. -/
theorem hocolimAugmentation_weak (K : SSet.{u}) :
    SSet.realizationWeakEquivalences (hocolimAugmentation K) :=
  SSet.realizationWeakEquivalences.of_postcomp _ _ (maximum_weak K)
    ((hocolimAugmentation_maximum K).symm ▸ maximumCocone_hocolim_weak K)

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
