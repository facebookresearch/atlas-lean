/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeCanonicalLeftReadback

/-!
# Native Canonical Left Evaluation

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
private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- Every original canonical pair, evaluated at all complete native free maps,
gives the entire original left source word with the actual unit-target cast. -/
theorem original_canonical_left_evaluation_word (n r : ℕ) (K L : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K ⟶
      𝟙_ CanonicalSourceSmash.Carrier.{u, v})
    (g : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) L ⟶ X) :
    PairCastBoundary.LeftPairEvaluationWord
      CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
      (fun n r => n + r)
      (cast PairCastBoundary.canonical_pair_type_native.{u, v}
        (CanonicalSourceFreeSmash.SelectedPair.pairIso CanonicalSourceFreeSmash.pairData.{u, v}))
      n r K L X f g =
    PairCastBoundary.NormalizedLeftDayWord
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      CanonicalSourceSmash.monoidalCategory.{u, v}
      PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
      n r K L X f g := by
  exact PairCastBoundary.normalized_left_day_readback_evaluation_word
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
    CanonicalSourceSmash.monoidalCategory.{u, v}
    PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
    (cast PairCastBoundary.canonical_pair_type_native.{u, v}
      (CanonicalSourceFreeSmash.SelectedPair.pairIso CanonicalSourceFreeSmash.pairData.{u, v}))
    original_canonical_normalized_left_day_readback.{u, v} n r K L X f g

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
