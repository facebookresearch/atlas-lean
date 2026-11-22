/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.ChosenSourceReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RightSourceAction

/-!
# Source Right Sphere Coefficient

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
  EnrichedDayKernel.ColimitMonoidal.smallestColimits PointedCGWH.EnrichedMapping.hasSmallLimits
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

/-- The whole original source evaluation comparison followed by its original native counit is the identity at every
  complete native level. -/
theorem chosen_source_comparison_counit_id (X : CanonicalSourceSmash.Carrier.{u, v}) (r : OrthogonalIndex) :
    (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app (toModule X) ≫
      component (CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.unitIso.hom.app X)
        (OrthogonalOperatorIndex.ofIndex.{u, v} r) =
      𝟙 (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r)) := by
  calc
    _ = (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app (toModule X) ≫
        𝟙 (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r)) :=
      congrArg (fun z => (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app
        (toModule X) ≫ z)
        (CanonicalSourceRightModuleEquivalence.unit_hom_component X (OrthogonalOperatorIndex.ofIndex.{u, v} r))
    _ = (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r).inv.app (toModule X) :=
      Category.comp_id _
    _ = _ := CanonicalSourceRightModuleFreeEvaluation.evaluationComparison_inv_app r (toModule X)

/-- The two whole chosen source preimages retain the native coefficient of an arbitrary first map and the actual
  identity coefficient of Gamma. -/
theorem chosen_source_right_tensor_gamma (r : OrthogonalIndex) (n : ℕ) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (toModule X)
        (NativeModuleEvaluation.sourcePreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r K X f) ⊗ₘ
      CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} n (PointedCGWH.orthogonalSphere.{u, v} n)
        (𝟙_ NativeSphereModule.Carrier.{u, v})
        (NativeModuleEvaluation.unitPreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
          SphereSmash.sourceData.{u, v}.moduleMonoidal n (PointedCGWH.orthogonalSphere.{u, v} n)
          (gamma.{u, v} n)) =
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f ⊗ₘ
        𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) :=
  congrArg₂ (fun a b => a ⊗ₘ b)
    (chosen_source_preimage_evaluate r K X f) (chosen_source_unit_preimage_gamma.{u, v} n)

set_option maxRecDepth 2000 in
set_option maxHeartbeats 500000 in
/-- Every original native free map keeps the whole chosen source right word through the original Day action and both
  target comparisons. -/
theorem chosen_source_right_word (r : OrthogonalIndex) (n : ℕ) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    ((CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} r K (toModule X)
        (NativeModuleEvaluation.sourcePreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} r K X f) ⊗ₘ
      CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} n (PointedCGWH.orthogonalSphere.{u, v} n)
        (𝟙_ NativeSphereModule.Carrier.{u, v})
        (NativeModuleEvaluation.unitPreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
          SphereSmash.sourceData.{u, v}.moduleMonoidal n (PointedCGWH.orthogonalSphere.{u, v} n)
          (gamma.{u, v} n))) ≫
      EnrichedDayKernel.Generators.point OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        (toModule X).X.toEnrichedFunctor sphereISpace.{u, v}.toEnrichedFunctor (r, n) ≫
      component (toModule X).action (r + n)) ≫
      (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} (r + n)).inv.app (toModule X) ≫
      component (CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.unitIso.hom.app X)
        (OrthogonalOperatorIndex.ofIndex.{u, v} (r + n)) =
    (Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f ⊗ₘ
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n)) ≫ sphereAction X r n := by
  simp only [chosen_source_preimage_evaluate, chosen_source_unit_preimage_gamma,
    CanonicalSourceRightModuleFreeEvaluation.evaluationComparison_inv_app,
    CanonicalSourceRightModuleEquivalence.unit_hom_component, Category.assoc]
  exact congrArg (fun z =>
    (Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f ⊗ₘ
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n)) ≫ z)
    (NativeDay.source_right_action.{u, v} X r n)

/-- The complete original source right sphere word, including both preimages, Day action, evaluation comparison and
  native counit, is the original coefficient-first nu. -/
theorem chosen_source_right_sphere_coefficient (n : ℕ) :
    ((CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} n (PointedCGWH.orthogonalSphere.{u, v} n)
        (toModule (sphereFree.{u, v} n))
        (NativeModuleEvaluation.sourcePreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
          n (PointedCGWH.orthogonalSphere.{u, v} n) (sphereFree.{u, v} n) (𝟙 (sphereFree.{u, v} n))) ⊗ₘ
      CanonicalSourceRightModuleFreeEvaluation.evaluate.{u, v} n (PointedCGWH.orthogonalSphere.{u, v} n)
        (𝟙_ NativeSphereModule.Carrier.{u, v})
        (NativeModuleEvaluation.unitPreimage sphereISpace.{u, v}
          CanonicalSourceSmash.sourceEquivalence.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
          CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
          SphereSmash.sourceData.{u, v}.moduleMonoidal n (PointedCGWH.orthogonalSphere.{u, v} n)
          (gamma.{u, v} n))) ≫
      EnrichedDayKernel.Generators.point OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
        (toModule (sphereFree.{u, v} n)).X.toEnrichedFunctor sphereISpace.{u, v}.toEnrichedFunctor (n, n) ≫
      component (toModule (sphereFree.{u, v} n)).action (n + n)) ≫
      (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} (n + n)).inv.app
        (toModule (sphereFree.{u, v} n)) ≫
      component (CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.unitIso.hom.app (sphereFree.{u, v} n))
        (OrthogonalOperatorIndex.ofIndex.{u, v} (n + n)) =
    𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n := by
  have h := chosen_source_right_word.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)
    (sphereFree.{u, v} n) (𝟙 (sphereFree.{u, v} n))
  have hNu := NativeFreeAction.nu_identity.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n)
  have hNu' : (Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n) (sphereFree.{u, v} n) (𝟙 (sphereFree.{u, v} n)) ⊗ₘ
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n)) ≫ sphereAction (sphereFree.{u, v} n) n n =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n := by
    simpa only [tensorHom_id, id_tensorHom] using hNu
  exact h.trans hNu'

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
