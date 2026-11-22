/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightSphereFaces
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RawLeftEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SphereReadbackAdapter
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.NativeRawReadback

/-!
# Native Gamma Integer Isomorphism

The original orthogonal Gamma maps and zero-to-n stabilization induce isomorphisms
in every signed integer degree. The original generator cardinal is selected internally.
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
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
open scoped CGWH.modelCategory MonoidalClosed
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.generatorOrderBot
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant
  CanonicalSourceSmash.monoidalCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

/-- The literal original native sphere faces agree in the original homotopy
category for every n. The original cardinal bottom is chosen internally. -/
theorem native_sphere_faces_map_eq (n : ℕ) :
    (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
      (nativeLeftSphereFaces.{u, v} n) =
    (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
      (nativeRightSphereFaces.{u, v} n) := by
  exact nativeSphereFaces_map_eq_of_raw_sphere_readbacks.{u, v} n
    (SourceJoin.raw_left_evaluate.{u, v} (sphereFree.{u, v} n) n n n (𝟙 (sphereFree.{u, v} n)))
    (nativeRightSphereCoefficient_eq_nu.{u, v} n)

/-- The original Gamma map induces an isomorphism in every original signed
integer degree, with the original cardinal and all native source actions internal. -/
theorem native_gamma_integer_isIso (n : ℕ) (q : ℤ) :
    IsIso ((integerPiFunctor.{u, v} q).map (gamma.{u, v} n)) := by
  exact integerGamma_isIso_of_raw_faces.{u, v} n q
    (native_sphere_faces_map_eq.{u, v} n)
    (fun X t f => SourceJoin.raw_left_evaluate.{u, v} X
      (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n f)
    (fun t => nativeRawLiftTarget.{u, v} n (integerTailLevel q + t))
    (fun t g => nativeUnitLift_rawMixedEvaluate.{u, v} n (integerTailLevel q + t)
      (integerTailPositiveIndex q + t + 1) g)

/-- The unchanged original stabilization from zero to n induces an isomorphism
in every original signed integer degree. -/
theorem native_stabilization_integer_isIso (n : ℕ) (q : ℤ) :
    IsIso ((integerPiFunctor.{u, v} q).map (Actual.orthogonalStabilization.{u, v} 0 n)) := by
  let := native_gamma_integer_isIso.{u, v} n q
  exact integerStabilization_isIso_of_gamma.{u, v} n q

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
