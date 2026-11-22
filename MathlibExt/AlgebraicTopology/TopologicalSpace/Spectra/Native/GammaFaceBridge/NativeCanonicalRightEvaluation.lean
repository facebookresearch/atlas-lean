/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeCanonicalRightReadback

/-!
# Native Canonical Right Evaluation

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

/-- The whole original canonical pair family evaluated at every native free map
gives the full original right source word, including its actual unit cast. -/
theorem original_canonical_right_evaluation_word (n r : ℕ) (K L : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K ⟶ X)
    (g : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) L ⟶
      𝟙_ CanonicalSourceSmash.Carrier.{u, v}) :
    PairCastBoundary.RightPairEvaluationWord
      CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
      (fun n r => n + r)
      (cast PairCastBoundary.canonical_pair_type_native.{u, v}
        (CanonicalSourceFreeSmash.SelectedPair.pairIso CanonicalSourceFreeSmash.pairData.{u, v}))
      n r K L X f g =
    PairCastBoundary.NormalizedRightDayWord
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      CanonicalSourceSmash.monoidalCategory.{u, v}
      PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
      n r K L X f g := by
  exact PairCastBoundary.normalized_right_day_readback_evaluation_word
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
    CanonicalSourceSmash.monoidalCategory.{u, v}
    PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
    (cast PairCastBoundary.canonical_pair_type_native.{u, v}
      (CanonicalSourceFreeSmash.SelectedPair.pairIso CanonicalSourceFreeSmash.pairData.{u, v}))
    original_canonical_normalized_right_day_readback.{u, v} n r K L X f g

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
