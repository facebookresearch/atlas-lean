/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalSourceGetters

/-!
# Original Evaluation Tail

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
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
private local instance constructionMonoidal1 : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  :=
  OrthogonalDay.monoidalCategory.{u, v}
private local instance constructionSymmetric2 : SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v}
  OrthogonalIndex) :=
  OrthogonalDay.symmetricCategory.{u, v}
private local instance constructionMonoid3 : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
private local instance constructionCommMonoid4 : IsCommMonObj sphereISpace.{u, v} :=
  OrthogonalDay.sphereIsCommMonObj.{u, v}
private local instance constructionMonoidal5 : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmash.sourceData.{u, v}.moduleMonoidal
private local instance constructionMonoidal6 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The whole original restriction retains the native level space at the same
original operator index. -/
theorem original_toModule_level_getter
    (X : CanonicalSourceSmash.Carrier.{u, v}) (r : ℕ) :
    (toModule X).X.toEnrichedFunctor.obj r =
      X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r) := rfl

/-- The complete original q/c evaluation tail is the identity on every actual
native level. It keeps the selected comparison, inverse source object and counit. -/
theorem original_pair_source_evaluation_tail_getter
    (X : CanonicalSourceSmash.Carrier.{u, v}) (r : ℕ) :
    (CanonicalSourceFreeSmash.pairData.{u, v}.evaluationComparison r).inv.app
        (CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.inverse.obj X) ≫
      component (CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.counitIso.hom.app X)
        (CanonicalSourceFreeSmash.pairData.{u, v}.indexMap r) =
      𝟙 (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r)) := by
  simp only [original_pair_source_counit_getter,
    original_pair_evaluation_comparison_getter, original_pair_source_object_getter,
    CanonicalSourceRightModuleFreeEvaluation.evaluationComparison_inv_app,
    original_toModule_level_getter]
  exact Category.id_comp _

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
