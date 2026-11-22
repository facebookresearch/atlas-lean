/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RightPairEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CanonicalNormalizedRightDay

/-!
# Native Canonical Right Readback

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
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

/-- The full original canonical right readback family after its exact complete
native type transport, retaining both original adjunctions and the original Day word. -/
theorem original_canonical_normalized_right_day_readback :
    PairCastBoundary.NormalizedRightDayReadback
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      CanonicalSourceSmash.monoidalCategory.{u, v}
      PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
      (cast PairCastBoundary.canonical_pair_type_native.{u, v}
        (CanonicalSourceFreeSmash.SelectedPair.pairIso CanonicalSourceFreeSmash.pairData.{u, v})) := by
  exact PairCastBoundary.cast_canonical_normalized_right_day_readback
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
    rfl (PairCastBoundary.selected_diagram_pair_eq_original_comparison
      (V := PointedCGWH.{u, v}) SphereSmash.sourceData.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v}
    PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
    PairCastBoundary.canonical_pair_type_native.{u, v}

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
