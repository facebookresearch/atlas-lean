/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightCompositionGetters
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightMapCoefficient
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightUnitCoefficient

/-!
# Native Right Word Evaluation

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
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

set_option maxHeartbeats 500000 in
/-- Every entire original q/c source right word is its two native free
coefficients followed by the original native right sphere action. -/
theorem original_native_right_word_evaluate (r n : ℕ) (K L : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X)
    (g : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) L ⟶
      𝟙_ CanonicalSourceSmash.Carrier.{u, v}) :
    PairCastBoundary.NormalizedRightDayWord
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      CanonicalSourceSmash.monoidalCategory.{u, v}
      PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
      r n K L X f g =
    (Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f ⊗ₘ
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n) L
        (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) g) ≫ sphereAction X r n := by
  have h := PairCastBoundary.normalized_right_day_word_composition
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
    CanonicalSourceSmash.monoidalCategory.{u, v}
    PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u, v}
    r n K L X f g
  rw [original_named_right_source_action_getter, original_named_right_target_tail_getter] at h
  rw [original_named_right_map_coefficient_getter, original_named_right_unit_coefficient_getter] at h
  exact h.trans (Category.comp_id _)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
