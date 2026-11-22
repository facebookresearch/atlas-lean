/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NormalizedRightWord
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceRightSphereCoefficient

/-!
# Original Source Getters

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

/-- The selected pair retains the complete original source equivalence. -/
theorem original_pair_source_equivalence_getter :
    CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence =
      CanonicalSourceSmash.sourceEquivalence.{u, v} := rfl

/-- The selected pair retains the original native operator index. -/
theorem original_pair_index_getter (n : ℕ) :
    CanonicalSourceFreeSmash.pairData.{u, v}.indexMap n =
      OrthogonalOperatorIndex.ofIndex.{u, v} n := rfl

/-- The selected pair retains the complete original free/evaluation comparison. -/
theorem original_pair_evaluation_comparison_getter (n : ℕ) :
    CanonicalSourceFreeSmash.pairData.{u, v}.evaluationComparison n =
      CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} n := rfl

/-- The source object obtained through the selected equivalence is the entire original
right sphere module, including its original action. -/
theorem original_pair_source_object_getter (X : CanonicalSourceSmash.Carrier.{u, v}) :
    CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.inverse.obj X =
      toModule X := rfl

/-- The selected coefficient is the original representation-sphere I-space. -/
theorem original_source_coefficient_getter :
    SphereSmash.sourceData.{u, v}.coefficient = sphereISpace.{u, v} := rfl

/-- The entire selected source tensor has the original sum index. -/
theorem original_source_tensor_index_getter (n r : ℕ) :
    CanonicalSourceFreeSmash.pairData.{u, v}.indexMap
        (SphereSmash.sourceData.{u, v}.monoidalData.tensorEnrichedFunctor.obj (n, r)) =
      OrthogonalOperatorIndex.ofIndex.{u, v} (n + r) := rfl

/-- The selected enriched source tensor evaluates to the original sum of dimensions. -/
theorem original_source_tensor_object_getter (n r : ℕ) :
    SphereSmash.sourceData.{u, v}.monoidalData.tensorEnrichedFunctor.obj (n, r) =
      n + r := rfl

/-- The selected source counit is the actual inverse native unit, whose whole level
component is the original identity. -/
theorem original_pair_source_counit_getter (X : CanonicalSourceSmash.Carrier.{u, v}) (r : ℕ) :
    component (CanonicalSourceFreeSmash.pairData.{u, v}.sourceEquivalence.counitIso.hom.app X)
        (CanonicalSourceFreeSmash.pairData.{u, v}.indexMap r) =
      𝟙 (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r)) :=
  CanonicalSourceRightModuleEquivalence.unit_inv_component X
    (OrthogonalOperatorIndex.ofIndex.{u, v} r)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
