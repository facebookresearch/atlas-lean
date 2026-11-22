/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.TargetCancellation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.FreeIdentityAction

/-!
# Raw Sphere Coefficient

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
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

set_option maxHeartbeats 500000 in
/-- The full original raw action of the actual free sphere identity is the original identity-frame sphere coefficient.
-/
theorem rawPowerAction_sphere_identity (n : ℕ) :
    SourceJoin.rawPowerAction (sphereFree.{u, v} n) n n n (𝟙 (sphereFree.{u, v} n)) =
      (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
        (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
      (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ Geometry.identityInclusion.{u, v} n) := by
  let X := sphereFree.{u, v} n
  let a := OrthogonalOperatorIndex.ofIndex.{u, v} n
  let b := OrthogonalOperatorIndex.ofIndex.{u, v} (n + n)
  let S := PointedCGWH.orthogonalSphere.{u, v} n
  let ev := Free.evaluate a S X (𝟙 X)
  let D := OrthogonalOperatorIndex.nu.{u, v} n n
  let q := (orderedTargetIso.{u, v} n n).hom
  have hNu := nativeNuLeftAction.{u, v} X n n
  have hRaw : SourceJoin.rawPowerAction X n n n (𝟙 X) =
      (S ◁ ev) ≫ CurrentFree.action a b S D X ≫ Sequential.indexMap X q := by
    simpa only [SourceJoin.rawPowerAction, Category.assoc] using
      congrArg (fun z => (S ◁ ev) ≫ z ≫ Sequential.indexMap X q) hNu.symm
  have hTarget := native_nu_ordered_target_identity.{u, v} n
  calc
    _ = (S ◁ ev) ≫ CurrentFree.action a b S D X ≫ Sequential.indexMap X q := hRaw
    _ = (β_ S S).hom ≫
        (S ◁ (D ≫ eHomWhiskerLeft PointedCGWH.{u, v}
          (ForgetEnrichment.of PointedCGWH.{u, v} a) q)) :=
      free_left_identity_target a b b S S D q
    _ = (β_ S S).hom ≫ (S ◁ Geometry.identityInclusion.{u, v} n) :=
      congrArg (fun z => (β_ S S).hom ≫ (S ◁ z)) hTarget
    _ = _ := by
      simp only [id_tensorHom]
      rfl

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
