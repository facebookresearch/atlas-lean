/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceRightSphereCoefficient

/-!
# Native Right Sphere Action

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
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The original free-sphere action on its complete identity coefficient is
the original coefficient-first nu on the same two sphere blocks. -/
theorem original_native_right_sphere_action_nu (n : ℕ) :
    (Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n) (sphereFree.{u, v} n) (𝟙 (sphereFree.{u, v} n)) ⊗ₘ
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n)) ≫ sphereAction (sphereFree.{u, v} n) n n =
    𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n := by
  simpa only [tensorHom_id, id_tensorHom] using
    NativeFreeAction.nu_identity.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
