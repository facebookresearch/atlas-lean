/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.IdentityGenerator

/-!
# Target Cancellation

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
open CategoryTheory.Spectra.SpectrumIndexMaps
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

/-- The complete ordered source generator retains the original native inclusion and full target permutation. -/
theorem orthogonal_ordered_target_inclusion (n : ℕ) :
    (orderedCoefficientIso.{u, v} n).hom ≫ OrthogonalOperatorIndex.nu.{u, v} n n ≫
      eHomWhiskerLeft PointedCGWH.{u, v}
        (ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n))
        (orderedTargetIso.{u, v} n n).hom =
    orderedSymmetricOperatorHom.{u, v} n (n + n) n (Nat.add_comm n n) ≫
      symmetricOrthogonalOperatorHomMap.{u, v} (Sequential.finiteIndex n)
        (Sequential.finiteIndex (n + n)) := by
  have hs := Sequential.sequentialPower_inclusion_map.{u, v} n n
  have hc := orderedPowerCompositeCoefficient.{u, v} n n
  symm
  calc
    _ = ((Sequential.sequentialPowerIso.{u, v} n n).inv ≫
        sequentialSymmetricOperatorHomMap.{u, v} (Sequential.sequentialDegree n)
          (Sequential.sequentialDegree (n + n))) ≫
        symmetricOrthogonalOperatorHomMap.{u, v} (Sequential.finiteIndex n)
          (Sequential.finiteIndex (n + n)) :=
      congrArg (fun z => z ≫ symmetricOrthogonalOperatorHomMap.{u, v}
        (Sequential.finiteIndex n) (Sequential.finiteIndex (n + n))) hs.symm
    _ = _ := by simpa only [Category.assoc] using hc

/-- Canceling the complete original coefficient isomorphism identifies the actual inclusion after its full target block
  permutation. -/
theorem native_nu_ordered_target_identity (n : ℕ) :
    OrthogonalOperatorIndex.nu.{u, v} n n ≫
      eHomWhiskerLeft PointedCGWH.{u, v}
        (ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n))
        (orderedTargetIso.{u, v} n n).hom =
      Geometry.identityInclusion.{u, v} n := by
  apply (cancel_epi (orderedCoefficientIso.{u, v} n).hom).1
  exact (orthogonal_ordered_target_inclusion.{u, v} n).trans
    (ordered_generator_identity_image.{u, v} n)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
