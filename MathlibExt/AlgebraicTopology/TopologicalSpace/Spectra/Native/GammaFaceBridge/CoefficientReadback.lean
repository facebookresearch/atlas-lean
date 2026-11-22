/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback

/-!
# Coefficient Readback

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
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  MonoidalLeftAction.monoidalOppositeLeftAction Enriched.prodCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits

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

/-- The whole original source-unit inverse has the original identity on each complete native sphere coefficient. -/
theorem nativeSourceUnit_inverse_component (n : ℕ) :
    component (CanonicalSourceSmash.sourceEquivalence.{u, v}.functor.map
      (CanonicalSourceSmashUnit.TypedSource.sourceUnitIso SphereSmash.sourceData.{u, v}).inv)
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) := by
  change component (CanonicalSourceRightModuleEquivalence.fromModuleFunctor.{u, v}.map
      (CanonicalSourceSmashUnit.TypedSource.sourceUnitIso SphereSmash.sourceData.{u, v}).inv)
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) = _
  rw [CanonicalSourceRightModuleEquivalence.fromModuleFunctor_map_component]
  let q := SphereSmash.sourceData.{u, v}
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  have hUnit := CanonicalSourceSmashUnit.TypedSource.sourceUnit_inv q
  change (CanonicalSourceSmashUnit.TypedSource.sourceUnitIso q).inv.hom =
    𝟙 q.coefficient at hUnit
  exact (congrArg (fun z => component z (n : OrthogonalIndex)) hUnit).trans
    (component_id q.coefficient n)

/-- The actual native Gamma has the same complete original identity-sphere coefficient as regular Gamma. -/
theorem nativeGamma_evaluate_identity (n : ℕ) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n) (𝟙_ CanonicalSourceSmash.Carrier.{u, v})
      (gamma.{u, v} n) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) := by
  rw [NativeUnit.gamma_regular_factor]
  rw [Free.evaluate_postcomp, RegularEvaluation.regularGamma_evaluate]
  change 𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ≫
    component (CanonicalSourceSmash.sourceEquivalence.{u, v}.functor.map
      (CanonicalSourceSmashUnit.TypedSource.sourceUnitIso SphereSmash.sourceData.{u, v}).inv)
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) = _
  rw [Category.id_comp]
  exact nativeSourceUnit_inverse_component.{u, v} n

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
