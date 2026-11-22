/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalEvaluationTail

/-!
# Native Right Action Tail

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
open CategoryTheory.Limits
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleActions
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
open CommutativeModuleConversion NativeModuleEvaluation
private local instance constructionMonoidal1 : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  :=
  OrthogonalDay.monoidalCategory.{u, v}
private local instance constructionSymmetric2 : SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v}
  OrthogonalIndex) :=
  OrthogonalDay.symmetricCategory.{u, v}
private local instance constructionMonoid3 : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
private local instance constructionCommMonoid4 : IsCommMonObj sphereISpace.{u, v} :=
  OrthogonalDay.sphereIsCommMonObj.{u, v}
private local instance constructionMonoid5 : MonObj SphereSmash.sourceData.{u, v}.coefficient :=
  SphereSmash.sourceData.{u, v}.coefficientMonObj
private local instance constructionCommMonoid6 : IsCommMonObj SphereSmash.sourceData.{u, v}.coefficient :=
  SphereSmash.sourceData.{u, v}.coefficientIsComm
private local instance constructionMonoidal7 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The full selected Day point and original module action are the original native
right sphere action on every coefficient level. -/
theorem original_selected_right_source_action_getter
    (X : CanonicalSourceSmash.Carrier.{u, v}) (n r : ℕ) :
    EnrichedDayKernel.Generators.point
        SphereSmash.sourceData.{u, v}.monoidalData.tensorEnrichedFunctor
        (CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.inverse.obj X).X.toEnrichedFunctor
        SphereSmash.sourceData.{u, v}.coefficient.toEnrichedFunctor (n, r) ≫
      component (CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.inverse.obj X).action
        (SphereSmash.sourceData.{u, v}.monoidalData.tensorEnrichedFunctor.obj (n, r)) =
      sphereAction X n r := by
  change EnrichedDayKernel.Generators.point
        OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        (toModule X).X.toEnrichedFunctor sphereISpace.{u, v}.toEnrichedFunctor (n, r) ≫
      component (toModule X).action (n + r) = _
  exact NativeDay.source_right_action.{u, v} X n r

/-- The complete selected target comparison followed by its actual source counit
retains the original identity on every native level. -/
theorem original_selected_right_target_getter
    (X : CanonicalSourceSmash.Carrier.{u, v}) (n r : ℕ) :
    (CanonicalSourceFreeSmash.pairData.{u, v}.evaluationComparison
        (SphereSmash.sourceData.{u, v}.monoidalData.tensorEnrichedFunctor.obj (n, r))).inv.app
        (CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.inverse.obj X) ≫
      component (CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.counitIso.hom.app X)
        (CanonicalSourceFreeSmash.pairData.{u, v}.indexMap
          (SphereSmash.sourceData.{u, v}.monoidalData.tensorEnrichedFunctor.obj (n, r))) =
      𝟙 (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))) := by
  simpa only [original_source_tensor_object_getter] using
    original_pair_source_evaluation_tail_getter X
      (SphereSmash.sourceData.{u, v}.monoidalData.tensorEnrichedFunctor.obj (n, r))

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
