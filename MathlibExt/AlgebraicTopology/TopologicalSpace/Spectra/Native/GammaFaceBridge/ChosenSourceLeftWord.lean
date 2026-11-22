/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceRightSphereCoefficient
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftSourceAction

/-!
# Chosen Source Left Word

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
attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
open CommutativeModuleConversion
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

/-- The two complete chosen source preimages have the original Gamma identity coefficient
followed by the complete coefficient of the original arbitrary native map. -/
theorem chosen_source_left_tensor_gamma (n : ℕ) (r : OrthogonalIndex) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} n (PointedCGWH.orthogonalSphere.{u, v} n)
        (𝟙_ NativeSphereModule.Carrier.{u, v})
        (NativeModuleEvaluation.unitPreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
          SphereSmash.sourceData.{u, v}.moduleMonoidal n (PointedCGWH.orthogonalSphere.{u, v} n)
          (gamma.{u, v} n)) ⊗ₘ
      CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (toModule X)
        (NativeModuleEvaluation.sourcePreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r K X f) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ
        Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f :=
  congrArg₂ (fun a b => a ⊗ₘ b)
    (chosen_source_unit_preimage_gamma.{u, v} n) (chosen_source_preimage_evaluate r K X f)

/-- Every original native map retains the whole source Gamma-left Day word, its original
coefficient braid and sphere action, and the inverse original source-index braid. -/
theorem chosen_source_left_word (n : ℕ) (r : OrthogonalIndex) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    ((CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} n (PointedCGWH.orthogonalSphere.{u, v} n)
        (𝟙_ NativeSphereModule.Carrier.{u, v})
        (NativeModuleEvaluation.unitPreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
          SphereSmash.sourceData.{u, v}.moduleMonoidal n (PointedCGWH.orthogonalSphere.{u, v} n)
          (gamma.{u, v} n)) ⊗ₘ
      CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (toModule X)
        (NativeModuleEvaluation.sourcePreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r K X f)) ≫
      EnrichedDayKernel.Generators.point OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        sphereISpace.{u, v}.toEnrichedFunctor (toModule X).X.toEnrichedFunctor (n, r) ≫
      component (leftAction sphereISpace.{u, v} (toModule X)) (n + r)) ≫
      (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} (n + r)).inv.app (toModule X) ≫
      component (CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.unitIso.hom.app X)
        (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r)) =
    (PointedCGWH.orthogonalSphere.{u, v} n ◁
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f) ≫
      (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))).hom ≫
      sphereAction X r n ≫ (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv := by
  let ev := Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f
  let point := EnrichedDayKernel.Generators.point
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    sphereISpace.{u, v}.toEnrichedFunctor (toModule X).X.toEnrichedFunctor (n, r)
  let act := component (leftAction sphereISpace.{u, v} (toModule X)) (n + r)
  let w := (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ ev) ≫ point ≫ act
  have hFirst := congrArg (fun z => (z ≫ point ≫ act) ≫
    (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} (n + r)).inv.app (toModule X) ≫
      component (CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.unitIso.hom.app X)
        (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r)))
    (chosen_source_left_tensor_gamma n r K X f)
  have hLast : w ≫
      (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} (n + r)).inv.app (toModule X) ≫
      component (CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.unitIso.hom.app X)
        (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r)) = w :=
    (congrArg (fun z => w ≫ z) (chosen_source_comparison_counit_id X (n + r))).trans
      (Category.comp_id w)
  have hAction := congrArg (fun z =>
    (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ ev) ≫ z)
    (NativeDay.source_left_action.{u, v} X n r)
  have hAction' : w =
      (PointedCGWH.orthogonalSphere.{u, v} n ◁ ev) ≫
        (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))).hom ≫
        sphereAction X r n ≫ (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv := by
    simpa only [w, point, act, sphereISpace, id_tensorHom, Category.assoc] using hAction
  exact hFirst.trans (hLast.trans hAction')

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
