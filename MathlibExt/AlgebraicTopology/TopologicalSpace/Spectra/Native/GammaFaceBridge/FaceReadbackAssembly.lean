/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.FaceAlgebra
import MathlibExt.CategoryTheory.Enriched.FreeLifting

/-!
# Face Readback Assembly

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- A proved literal mixed left-face coefficient identifies the entire original native sphere face. -/
theorem nativeLeftSphereFaces_eq_identityExtension (n : ℕ)
    (h : Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere.{u, v} n)
      (sphereFree.{u, v} n) (nativeLeftFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)) =
      (β_ (PointedCGWH.orthogonalSphere.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
        (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ Geometry.identityInclusion.{u, v} n)) :
    nativeLeftSphereFaces.{u, v} n =
      Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
        (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
        ((PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
          (β_ (PointedCGWH.orthogonalSphere.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
            (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ Geometry.identityInclusion.{u, v} n)) := by
  apply (Free.homEquiv (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
    (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)).injective
  change Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
      (nativeLeftSphereFaces.{u, v} n) =
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
      (Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
        (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
        ((PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
          (β_ (PointedCGWH.orthogonalSphere.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
            (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ Geometry.identityInclusion.{u, v} n)))
  rw [Free.evaluate_extend]
  have hFace := congrArg
    (Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n))
    (nativeLeftSphereFaces_precompose.{u, v} n)
  have hEval := Free.evaluate_precomp (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
    (sphereFree.{u, v} n) (PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom
    (nativeLeftFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n))
  exact hFace.trans (hEval.trans (congrArg
    (fun z => (PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫ z) h))

/-- A proved literal mixed right-face coefficient identifies its full original block-crossing sphere extension. -/
theorem nativeRightSphereFaces_eq_blockSwapExtension (n : ℕ)
    (h : Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere.{u, v} n)
      (sphereFree.{u, v} n) (nativeRightFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n) :
    nativeRightSphereFaces.{u, v} n =
      Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
        (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
        ((PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
          (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n)) := by
  apply (Free.homEquiv (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
    (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)).injective
  change Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
      (nativeRightSphereFaces.{u, v} n) =
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
      (Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
        (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
        ((PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
          (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n)))
  rw [Free.evaluate_extend]
  have hFace := congrArg
    (Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n))
    (nativeRightSphereFaces_precompose.{u, v} n)
  have hEval := Free.evaluate_precomp (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
    (sphereFree.{u, v} n) (PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom
    (nativeRightFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n))
  exact hFace.trans (hEval.trans (congrArg
    (fun z => (PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫ z) h))

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- The genuine original based rotation equates the literal native sphere faces once their actual coefficient readbacks
  are proved. -/
theorem nativeSphereFaces_map_eq_of_actual_coefficients (n : ℕ)
    (hLeft : Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere.{u, v} n)
      (sphereFree.{u, v} n) (nativeLeftFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)) =
      (β_ (PointedCGWH.orthogonalSphere.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
        (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ Geometry.identityInclusion.{u, v} n))
    (hRight : Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere.{u, v} n)
      (sphereFree.{u, v} n) (nativeRightFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n) :
    (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (nativeLeftSphereFaces.{u, v} n) =
      (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (nativeRightSphereFaces.{u, v} n) :=
        by
  rw [nativeLeftSphereFaces_eq_identityExtension n hLeft, nativeRightSphereFaces_eq_blockSwapExtension n hRight]
  exact Geometry.explicit_rotation_map_eq.{u, v} n

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
