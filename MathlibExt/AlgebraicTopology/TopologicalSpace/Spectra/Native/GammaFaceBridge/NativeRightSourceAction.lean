/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeRightActionTail

/-!
# Native Right Source Action

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
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open CommutativeModuleConversion
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

/-- The literal q-bound original Day point and module action have the same
complete native right action at every original level and source module. -/
theorem exact_selected_right_source_action_getter
    (X : CanonicalSourceSmash.Carrier.{u, v}) (n r : ℕ) :
    letI := SphereSmash.sourceData.{u, v}.dayMonoidal
    letI := SphereSmash.sourceData.{u, v}.daySymmetric
    letI := SphereSmash.sourceData.{u, v}.coefficientMonObj
    letI := SphereSmash.sourceData.{u, v}.coefficientIsComm
    letI := SphereSmash.sourceData.{u, v}.dayCoequalizers
    letI := SphereSmash.sourceData.{u, v}.dayTensorLeftPreserves
    letI := SphereSmash.sourceData.{u, v}.dayTensorRightPreserves
    letI : MonoidalCategory (RightModule SphereSmash.sourceData.{u, v}.coefficient) :=
      RightModuleFree.tensorMonoidal SphereSmash.sourceData.{u, v}.coefficient
    EnrichedDayKernel.Generators.point
        SphereSmash.sourceData.{u, v}.monoidalData.tensorEnrichedFunctor
        (CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.inverse.obj X).X.toEnrichedFunctor
        SphereSmash.sourceData.{u, v}.coefficient.toEnrichedFunctor (n, r) ≫
      component (CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.inverse.obj X).action
        (SphereSmash.sourceData.{u, v}.monoidalData.tensorEnrichedFunctor.obj (n, r)) =
      sphereAction X n r := by
  let := SphereSmash.sourceData.{u, v}.dayMonoidal
  let := SphereSmash.sourceData.{u, v}.daySymmetric
  let := SphereSmash.sourceData.{u, v}.coefficientMonObj
  let := SphereSmash.sourceData.{u, v}.coefficientIsComm
  let := SphereSmash.sourceData.{u, v}.dayCoequalizers
  let := SphereSmash.sourceData.{u, v}.dayTensorLeftPreserves
  let := SphereSmash.sourceData.{u, v}.dayTensorRightPreserves
  let : MonoidalCategory (RightModule SphereSmash.sourceData.{u, v}.coefficient) :=
    RightModuleFree.tensorMonoidal SphereSmash.sourceData.{u, v}.coefficient
  exact original_selected_right_source_action_getter X n r

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
