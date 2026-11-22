/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RightFaceEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightSphereCoefficient

/-!
# Native Right Sphere Faces

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
  CanonicalSourceSmash.monoidalCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

/-- The full original native right sphere face evaluates to the original nu
coefficient for every n, through its actual original face formula and full pair family. -/
theorem nativeRightSphereCoefficient_eq_nu (n : ℕ) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere.{u, v} n)
      (sphereFree.{u, v} n) (nativeRightFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n := by
  have h := PairCastBoundary.right_faces_evaluation_word_formula
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} gamma.{u, v} nativePairFamily.{u, v}
    nativeRightFaces.{u, v} nativeRightFaces_original.{u, v}
    n n (PointedCGWH.orthogonalSphere.{u, v} n) (sphereFree.{u, v} n) (𝟙 (sphereFree.{u, v} n))
  rw [Category.comp_id] at h
  exact h.trans (original_native_named_right_sphere_coefficient.{u, v} n)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
