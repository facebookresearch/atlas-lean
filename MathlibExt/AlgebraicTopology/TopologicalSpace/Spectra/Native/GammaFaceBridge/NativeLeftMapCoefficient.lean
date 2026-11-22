/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftDayCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalEvaluationTail
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.ChosenSourceLeftWord

/-!
# Native Left Map Coefficient

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
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleActions
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
open CommutativeModuleConversion
private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The complete original arbitrary native map has its exact selected source coefficient. -/
theorem native_left_map_coefficient (r : ℕ) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (V := PointedCGWH.{u, v}) (A := OrthogonalOperatorIndex.{u, v})
      (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    PairCastBoundary.LeftDayMapCoefficient
      (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v} r K X f =
    Free.evaluate (V := PointedCGWH.{u, v}) (A := OrthogonalOperatorIndex.{u, v})
      (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f := by
  have h0 := PairCastBoundary.left_day_map_coefficient_evaluate
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v} r K X f
  have hId : PairCastBoundary.LeftDayMapCoefficient
      (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v} r K X f ≫
      𝟙 (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r)) =
      PairCastBoundary.LeftDayMapCoefficient
        (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
        SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v} r K X f :=
    Category.comp_id _
  rw [original_pair_source_evaluation_tail_getter] at h0
  simpa only [hId, original_pair_index_getter, Functor.id_obj] using h0

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
