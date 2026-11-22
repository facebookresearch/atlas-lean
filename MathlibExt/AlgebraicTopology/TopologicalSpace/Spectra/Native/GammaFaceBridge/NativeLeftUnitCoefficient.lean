/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightUnitCoefficient
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeLeftMapCoefficient

/-!
# Native Left Unit Coefficient

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
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
open scoped MonoidalClosed
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The complete original selected Gamma unit coefficient is the identity on its
original sphere, through the actual unit cast and complete source inverse unit. -/
theorem native_left_unit_coefficient (n : ℕ) :
    PairCastBoundary.LeftDayUnitCoefficient
      (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      CanonicalSourceSmash.monoidalCategory.{u, v} native_primitive_monoidal_eq.{u, v}
      n (PointedCGWH.orthogonalSphere.{u, v} n) (gamma.{u, v} n) =
    𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) := by
  have h := original_named_right_unit_coefficient_getter.{u, v}
    n (PointedCGWH.orthogonalSphere.{u, v} n) (gamma.{u, v} n)
  rw [nativeGamma_evaluate_identity] at h
  exact h

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
