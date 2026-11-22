/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RightDayComposition
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightActionTail
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightSourceAction

/-!
# Native Right Composition Getters

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
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open CommutativeModuleConversion
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

/-- The complete ordinary q/c action boundary is the original native action at
every source module and both original coefficient levels. -/
theorem original_named_right_source_action_getter
    (X : CanonicalSourceSmash.Carrier.{u, v}) (n r : ℕ) :
    PairCastBoundary.RightDaySourceAction
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      n r X = sphereAction X n r := by
  exact exact_selected_right_source_action_getter X n r

/-- The complete original comparison and counit boundary is the native level
identity, with no coefficient or action removed from the source provider. -/
theorem original_named_right_target_tail_getter
    (X : CanonicalSourceSmash.Carrier.{u, v}) (n r : ℕ) :
    PairCastBoundary.RightDayTargetTail
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      n r X = 𝟙 (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))) := by
  exact original_selected_right_target_getter X n r

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
