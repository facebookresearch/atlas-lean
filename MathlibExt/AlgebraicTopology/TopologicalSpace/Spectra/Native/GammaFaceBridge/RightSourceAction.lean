/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftDayAction

/-!
# Right Source Action

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
  MonoidalLeftAction.monoidalOppositeLeftAction PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeDay
open CommutativeModuleConversion CanonicalSourceRightModuleActions
private local instance constructionCategory1 : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
private local instance constructionMonoidal2 : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u,
  v}
private local instance constructionEnrichedCategory3 : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
private local instance constructionSymmetric4 : SymmetricCategory OrthogonalIndex :=
  OrthogonalIndex.symmetricCategory.{u, v}
private local instance constructionMonoidal5 : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  :=
  OrthogonalDay.monoidalCategory.{u, v}
private local instance constructionSymmetric6 : SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v}
  OrthogonalIndex) :=
  OrthogonalDay.symmetricCategory.{u, v}
private local instance constructionMonoid7 : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}

theorem source_right_action (X : Actual.OrthogonalCarrier.{u, v}) (r n : OrthogonalIndex) :
    EnrichedDayKernel.Generators.point OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
      (toModule X).X.toEnrichedFunctor sphereISpace.{u, v}.toEnrichedFunctor (r, n) ≫
      component (toModule X).action
        (@MonoidalCategoryStruct.tensorObj OrthogonalIndex OrthogonalIndex.category.{u, v}
          (OrthogonalIndex.monoidalCategory.{u, v}).toMonoidalCategoryStruct r n) = sphereAction X r n := by
  change EnrichedDayKernel.Generators.point OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
      (toModule X).X.toEnrichedFunctor orthogonalSphereFunctor.{u, v} (r, n) ≫
      component (toModule X).action (r + n) = sphereAction X r n
  exact (NativeSphereModule.sphereComponent_day_point (toModule X) r n).symm.trans
    (toModule_sphereComponent X r n)

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeDay
