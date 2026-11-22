/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalSymmetricPiStarOmegaEvaluationReadback

/-!
# The original entire first comparison in the native coordinate

The complete original coordinate and evaluation-comparison constructors are
fixed as natural transformations before selecting an original input. Their
full original first coaugmentation/comparison word is preserved.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat NativeOmegaRecovery

namespace PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf PointedCGWH.EnrichedMapping.hasSmallLimits
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  Operad.SmallFinBijGroupoid.instMonoidalCategory Operad.SmallFinBijGroupoid.instSymmetricCategory

/-- The original chart is recovered from its two actual given whole comparison maps. -/
def originalCoordinateChart (m : ℕ) :
    (PointedCGWH.SymmetricShift.functor.{u, v} NativeSymmetricDelooping.firstIndex ⋙
      cotensor PointedCGWH.sphereOne.{u, v}) ⋙ level.{u, v} m ≅
        level.{u, v} (m + 1) ⋙ PointedCGWH.loop :=
  (Functor.isoWhiskerRight NativeSymmetricR.comparison.{u, v} (level.{u, v} m)).symm ≪≫
    stepEvaluation.{u, v} m

private theorem originalCoordinateChart_hom_app (m : ℕ) (X : Carrier.{u, v}) :
    (originalCoordinateChart.{u, v} m).hom.app X = 𝟙 _ := by
  change (level.{u, v} m).map (NativeSymmetricR.comparison.{u, v}.inv.app X) ≫
    (stepEvaluation.{u, v} m).hom.app X = _
  erw [original_stepEvaluation_hom_app]
  exact ((level.{u, v} m).mapIso (NativeSymmetricR.comparison.{u, v}.app X)).inv_hom_id

/-- The entire original coordinate retains the full first source word and its actual chart. -/
theorem originalCoordinate_whole_first_free_comparison (m : ℕ) :
    originalCoordinate.{u, v} m = (level.{u, v} m).leftUnitor.inv ≫
      Functor.whiskerRight
        (NativeSymmetricLambda.coaugmentation.{u, v} ≫ NativeSymmetricR.comparison.{u, v}.hom)
        (level.{u, v} m) ≫ (originalCoordinateChart.{u, v} m).hom := by
  unfold originalCoordinate Functor.CoaugmentationEvaluation.coordinate originalCoordinateChart
  simp only [Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_comp, Category.assoc]
  have h := (Functor.isoWhiskerRight NativeSymmetricR.comparison.{u, v}
    (level.{u, v} m)).hom_inv_id_assoc (stepEvaluation.{u, v} m).hom
  change Functor.whiskerRight NativeSymmetricR.comparison.{u, v}.hom (level.{u, v} m) ≫
      Functor.whiskerRight NativeSymmetricR.comparison.{u, v}.inv (level.{u, v} m) ≫
      (stepEvaluation.{u, v} m).hom = (stepEvaluation.{u, v} m).hom at h
  rw [h]

/-- Every original coordinate is the same entire first source word mapped by its actual evaluation. -/
theorem originalCoordinate_first_free_comparison (m : ℕ) (X : Carrier.{u, v}) :
    (originalCoordinate.{u, v} m).app X =
      (level.{u, v} m).map
        ((NativeSymmetricLambda.coaugmentation.{u, v} ≫
          NativeSymmetricR.comparison.{u, v}.hom).app X) := by
  rw [originalCoordinate_whole_first_free_comparison]
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    originalCoordinateChart_hom_app, Category.id_comp]
  exact Category.comp_id _

end PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests
