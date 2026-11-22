/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftDayCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalEvaluationTail

/-!
# Native Right Map Coefficient

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
open scoped MonoidalClosed
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The actual original q/c map coefficient is the complete native free
coefficient, after its whole original comparison and counit are read back. -/
theorem original_named_right_map_coefficient_getter
    (r : ℕ) (K : PointedCGWH.{u, v}) (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    PairCastBoundary.LeftDayMapCoefficient
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v} r K X f =
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f := by
  have h := PairCastBoundary.left_day_map_coefficient_evaluate
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v} r K X f
  rw [original_pair_source_evaluation_tail_getter] at h
  exact (Category.comp_id _).symm.trans h

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
