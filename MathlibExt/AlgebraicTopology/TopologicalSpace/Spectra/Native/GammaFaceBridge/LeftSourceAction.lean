/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RightSourceAction

/-!
# Left Source Action

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

theorem source_left_action (X : Actual.OrthogonalCarrier.{u, v}) (n r : OrthogonalIndex) :
    EnrichedDayKernel.Generators.point OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
      orthogonalSphereFunctor.{u, v} (toModule X).X.toEnrichedFunctor (n, r) ≫
      component (leftAction sphereISpace.{u, v} (toModule X)) (n + r) =
    (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))).hom ≫
      sphereAction X r n ≫ (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv := by
  have h := ModuleLeftAction.left_action OrthogonalIndex.enrichedMonoidalData.{u, v}
    OrthogonalIndex.enrichedSymmetricData.{u, v} sphereISpace.{u, v} (toModule X) n r
  rw [← Category.assoc _ _
    ((toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv),
    source_right_action X r n] at h
  exact h

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeDay
