/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftDayUnitReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalUnitEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalUnitInverseComparison

/-!
# Native Right Unit Coefficient

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open CommutativeModuleConversion NativeModuleEvaluation
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The exact original q/c unit coefficient retains the entire native unit
evaluation, with its original equality cast and inverse source unit. -/
theorem original_named_right_unit_coefficient_getter
    (r : ℕ) (L : PointedCGWH.{u, v})
    (g : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) L ⟶
      𝟙_ CanonicalSourceSmash.Carrier.{u, v}) :
    PairCastBoundary.LeftDayUnitCoefficient
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      CanonicalSourceSmash.monoidalCategory.{u, v}
      PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
      r L g =
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) L
        (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) g := by
  have h := PairCastBoundary.left_day_unit_coefficient_evaluate
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
    CanonicalSourceSmash.monoidalCategory.{u, v}
    PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
    r L g
  rw [original_source_unit_inverse_comparison_getter,
    Free.evaluate_postcomp, original_native_unit_cast_evaluation_getter] at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.comp_id _))

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
