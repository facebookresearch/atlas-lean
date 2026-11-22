/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RawSphereCoefficient
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.FaceReadbackAssembly

/-!
# Sphere Readback Adapter

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
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalFreeSphereSmashFlatness
  (spectrumMap coefficientMap)
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The original source label cast at equal blocks is the identity on the entire original mixed free map. -/
theorem rawMixedEvaluate_diagonal (X : Actual.OrthogonalCarrier.{u, v}) (n d : ℕ)
    (g : mixedFree.{u, v} n n d ⟶ X) :
    SourceJoin.rawMixedEvaluate X n d n g =
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
        (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere.{u, v} d) X g := by
  simp only [SourceJoin.rawMixedEvaluate, SourceJoin.mixedLabelCast,
    eqToHom_refl, Category.id_comp]

/-- The actual raw-left equation on the same original identity generator gives the complete literal left sphere
  coefficient. -/
theorem nativeLeftSphereCoefficient_of_raw (n : ℕ)
    (hRaw : SourceJoin.rawMixedEvaluate (sphereFree.{u, v} n) n n n
        (nativeLeftFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n) ≫
          𝟙 (sphereFree.{u, v} n)) =
      SourceJoin.rawPowerAction (sphereFree.{u, v} n) n n n (𝟙 (sphereFree.{u, v} n))) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere.{u, v} n)
      (sphereFree.{u, v} n) (nativeLeftFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)) =
    (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
      (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ Geometry.identityInclusion.{u, v} n) := by
  have hMixed := rawMixedEvaluate_diagonal (sphereFree.{u, v} n) n n
    (nativeLeftFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n))
  have hRaw' := hRaw
  rw [Category.comp_id] at hRaw'
  exact hMixed.symm.trans (hRaw'.trans (rawPowerAction_sphere_identity.{u, v} n))

/-- The same actual raw-left generator identifies the entire native left sphere face with the original identity-frame
  rotation map. -/
theorem nativeLeftSphereFaces_eq_identitySpectrumMap_of_raw (n : ℕ)
    (hRaw : SourceJoin.rawMixedEvaluate (sphereFree.{u, v} n) n n n
        (nativeLeftFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n) ≫
          𝟙 (sphereFree.{u, v} n)) =
      SourceJoin.rawPowerAction (sphereFree.{u, v} n) n n n (𝟙 (sphereFree.{u, v} n))) :
    nativeLeftSphereFaces.{u, v} n =
      spectrumMap.{u, v} n (n + n) n (OrthogonalMatrixHom.id (n + n)) := by
  rw [nativeLeftSphereFaces_eq_identityExtension n (nativeLeftSphereCoefficient_of_raw n hRaw)]
  change Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
      ((PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
        (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
          (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
        (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ Geometry.identityInclusion.{u, v} n)) =
    Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
      (coefficientMap.{u, v} n (n + n) n (OrthogonalMatrixHom.id (n + n)))
  rw [Geometry.coefficientMap_identity]

/-- A proved original right coefficient identifies the entire native right sphere face with the unchanged block-swap
  rotation map. -/
theorem nativeRightSphereFaces_eq_blockSwapSpectrumMap (n : ℕ)
    (hRight : Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere.{u, v} n)
      (sphereFree.{u, v} n) (nativeRightFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n) :
    nativeRightSphereFaces.{u, v} n =
      spectrumMap.{u, v} n (n + n) n (OrthogonalIndex.blockSwap n n) := by
  rw [nativeRightSphereFaces_eq_blockSwapExtension n hRight]
  change Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
      ((PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
        (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n)) =
    Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} (n + n)) (sphereFree.{u, v} n)
      (coefficientMap.{u, v} n (n + n) n (OrthogonalIndex.blockSwap n n))
  rw [Geometry.coefficientMap_blockSwap]

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- The genuine original based rotation equates the literal native sphere faces after the actual raw-left and right
  coefficient equations are supplied. -/
theorem nativeSphereFaces_map_eq_of_raw_sphere_readbacks (n : ℕ)
    (hLeft : SourceJoin.rawMixedEvaluate (sphereFree.{u, v} n) n n n
        (nativeLeftFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n) ≫
          𝟙 (sphereFree.{u, v} n)) =
      SourceJoin.rawPowerAction (sphereFree.{u, v} n) n n n (𝟙 (sphereFree.{u, v} n)))
    (hRight : Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere.{u, v} n)
      (sphereFree.{u, v} n) (nativeRightFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n) :
    (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
        (nativeLeftSphereFaces.{u, v} n) =
      (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
        (nativeRightSphereFaces.{u, v} n) := by
  rw [nativeLeftSphereFaces_eq_identitySpectrumMap_of_raw n hLeft,
    nativeRightSphereFaces_eq_blockSwapSpectrumMap n hRight]
  exact PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalFreeSphereSmashFlatness.spectrumMap_rotation_map_eq.{u, v} n

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
