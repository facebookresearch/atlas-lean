/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeCanonicalRightEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightSourceWord

/-!
# Canonical Right Sphere Coefficient

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
open scoped MonoidalClosed
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The complete original canonical right sphere family has the original nu
coefficient at every n, after its exact whole native type transport. -/
theorem original_canonical_right_sphere_coefficient (n : ℕ) :
    PairCastBoundary.RightPairEvaluationWord
      CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
      (fun n r => n + r)
      (cast PairCastBoundary.canonical_pair_type_native.{u, v}
        (CanonicalSourceFreeSmash.SelectedPair.pairIso CanonicalSourceFreeSmash.pairData.{u, v}))
      n n (PointedCGWH.orthogonalSphere.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n)
      (sphereFree.{u, v} n) (𝟙 (sphereFree.{u, v} n)) (gamma.{u, v} n) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n := by
  exact (original_canonical_right_evaluation_word.{u, v} n n
    (PointedCGWH.orthogonalSphere.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n)
    (sphereFree.{u, v} n) (𝟙 (sphereFree.{u, v} n)) (gamma.{u, v} n)).trans
    (original_normalized_right_sphere_coefficient.{u, v} n)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
