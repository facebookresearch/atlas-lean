/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CoefficientReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.ModulePairEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.UnitPreimageEvaluation

/-!
# Chosen Source Readback

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
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed CategoryTheory.MonObj

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

/-- The chosen original source preimage has exactly the complete native free coefficient; both actual comparison
  components are identities. -/
theorem chosen_source_preimage_evaluate (r : OrthogonalIndex) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (toModule X)
      (NativeModuleEvaluation.sourcePreimage sphereISpace.{u, v}
        CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
        CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r K X f) =
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f := by
  have h := NativeModuleEvaluation.sourcePreimage_evaluate (V := PointedCGWH.{u, v})
    (J := OrthogonalOperatorIndex.{u, v}) sphereISpace.{u, v}
    CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r K X f
  change CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (toModule X)
      (NativeModuleEvaluation.sourcePreimage sphereISpace.{u, v}
        CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
        CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r K X f) ≫
      (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app (toModule X) ≫
      component (CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.unitIso.hom.app X)
        (OrthogonalOperatorIndex.ofIndex.{u, v} r) = _ at h
  let ev := CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (toModule X)
    (NativeModuleEvaluation.sourcePreimage sphereISpace.{u, v}
      CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
      CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r K X f)
  have hId : ev ≫ (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app (toModule X) ≫
      component (CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.unitIso.hom.app X)
        (OrthogonalOperatorIndex.ofIndex.{u, v} r) = ev := by
    calc
      _ = ev ≫ (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app (toModule X) ≫
          𝟙 (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r)) :=
        congrArg (fun z => ev ≫
          (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app (toModule X) ≫ z)
          (CanonicalSourceRightModuleEquivalence.unit_hom_component X (OrthogonalOperatorIndex.ofIndex.{u, v} r))
      _ = ev ≫ (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app (toModule X) :=
        Category.comp_id _
      _ = ev ≫ 𝟙 ((toModule X).X.toEnrichedFunctor.obj r) :=
        congrArg (fun z => ev ≫ z)
          (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison_inv_app r (toModule X))
      _ = ev := Category.comp_id ev
  exact hId.symm.trans h

/-- The chosen original source-unit preimage retains precisely the actual native unit coefficient. -/
theorem chosen_source_unit_preimage_evaluate (r : OrthogonalIndex) (K : PointedCGWH.{u, v})
    (g : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶
      𝟙_ CanonicalSourceSmash.Carrier.{u, v}) :
    CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (𝟙_ NativeSphereModule.Carrier.{u, v})
      (NativeModuleEvaluation.unitPreimage sphereISpace.{u, v}
        CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
        CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
        SphereSmash.sourceData.{u, v}.moduleMonoidal r K g) =
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K
        (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) g := by
  have h := NativeModuleEvaluation.unit_preimage_evaluate (V := PointedCGWH.{u, v})
    (J := OrthogonalOperatorIndex.{u, v}) sphereISpace.{u, v}
    CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
    SphereSmash.sourceData.{u, v}.moduleMonoidal r K g
  change CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (𝟙_ NativeSphereModule.Carrier.{u, v})
      (NativeModuleEvaluation.unitPreimage sphereISpace.{u, v}
        CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
        CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
        SphereSmash.sourceData.{u, v}.moduleMonoidal r K g) ≫
      (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app
        (𝟙_ NativeSphereModule.Carrier.{u, v}) = _ at h
  let ev := CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (𝟙_ NativeSphereModule.Carrier.{u, v})
    (NativeModuleEvaluation.unitPreimage sphereISpace.{u, v}
      CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
      CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
      SphereSmash.sourceData.{u, v}.moduleMonoidal r K g)
  have hId : ev ≫ (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app
      (𝟙_ NativeSphereModule.Carrier.{u, v}) = ev :=
    (congrArg (fun z => ev ≫ z)
      (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison_inv_app r
        (𝟙_ NativeSphereModule.Carrier.{u, v}))).trans (Category.comp_id ev)
  exact hId.symm.trans h

/-- In the same complete chosen source, the actual Gamma preimage is the original identity-sphere coefficient. -/
theorem chosen_source_unit_preimage_gamma (n : ℕ) :
    CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} n (PointedCGWH.orthogonalSphere.{u, v} n)
      (𝟙_ NativeSphereModule.Carrier.{u, v})
      (NativeModuleEvaluation.unitPreimage sphereISpace.{u, v}
        CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
        CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
        SphereSmash.sourceData.{u, v}.moduleMonoidal n (PointedCGWH.orthogonalSphere.{u, v} n)
        (gamma.{u, v} n)) = 𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) :=
  (chosen_source_unit_preimage_evaluate n (PointedCGWH.orthogonalSphere.{u, v} n) (gamma.{u, v} n)).trans
    (nativeGamma_evaluate_identity.{u, v} n)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
