/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalSourceInverseComparison

/-!
# Original Unit Inverse Comparison

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
open CommutativeModuleConversion
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

/-- The complete selected source unit has the original inverse comparison at
every coefficient level, with the original q fields kept as local let bindings. -/
theorem original_source_unit_inverse_comparison_getter (r : ℕ) :
    letI := SphereSmash.sourceData.{u, v}.dayMonoidal
    letI := SphereSmash.sourceData.{u, v}.daySymmetric
    letI := SphereSmash.sourceData.{u, v}.coefficientMonObj
    letI := SphereSmash.sourceData.{u, v}.coefficientIsComm
    letI := SphereSmash.sourceData.{u, v}.dayCoequalizers
    letI := SphereSmash.sourceData.{u, v}.dayTensorLeftPreserves
    letI := SphereSmash.sourceData.{u, v}.dayTensorRightPreserves
    letI : MonoidalCategory (RightModule SphereSmash.sourceData.{u, v}.coefficient) :=
      RightModuleFree.tensorMonoidal SphereSmash.sourceData.{u, v}.coefficient
    (CanonicalSourceFreeSmash.pairData.{u, v}.evaluationComparison r).inv.app
        (𝟙_ (RightModule SphereSmash.sourceData.{u, v}.coefficient)) =
      𝟙 ((𝟙_ (RightModule SphereSmash.sourceData.{u, v}.coefficient)).X.toEnrichedFunctor.obj r) := by
  let := SphereSmash.sourceData.{u, v}.dayMonoidal
  let := SphereSmash.sourceData.{u, v}.daySymmetric
  let := SphereSmash.sourceData.{u, v}.coefficientMonObj
  let := SphereSmash.sourceData.{u, v}.coefficientIsComm
  let := SphereSmash.sourceData.{u, v}.dayCoequalizers
  let := SphereSmash.sourceData.{u, v}.dayTensorLeftPreserves
  let := SphereSmash.sourceData.{u, v}.dayTensorRightPreserves
  let : MonoidalCategory (RightModule SphereSmash.sourceData.{u, v}.coefficient) :=
    RightModuleFree.tensorMonoidal SphereSmash.sourceData.{u, v}.coefficient
  exact original_source_inverse_comparison_getter r _

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
