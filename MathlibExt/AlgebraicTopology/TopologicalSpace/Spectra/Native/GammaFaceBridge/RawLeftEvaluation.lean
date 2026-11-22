/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeLeftFaceEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.EvaluationLabelCast
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalTargetBraid

/-!
# Raw Left Evaluation

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
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleActions
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
open scoped MonoidalClosed
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
private local instance constructionMonoidal1 : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  :=
  OrthogonalDay.monoidalCategory.{u, v}
private local instance constructionMonoid2 : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
private local instance constructionMonoidal3 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The literal original n+r/r+n source cast gives the full original ordered-target action
on every coefficient object, free map and native target. -/
theorem native_left_label_evaluate (n r : ℕ) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (r + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ K) X
      (eqToHom (congrArg (fun i => Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} i)
        (PointedCGWH.orthogonalSphere.{u, v} n ⊗ K)) (Nat.add_comm r n)) ≫
        nativeLeftFaces.{u, v} n r K ≫ f) =
    (PointedCGWH.orthogonalSphere.{u, v} n ◁
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f) ≫
      (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))).hom ≫
      sphereAction X r n ≫ Sequential.indexMap X (orderedTargetIso.{u, v} r n).hom := by
  have h := evaluate_label_cast OrthogonalOperatorIndex.ofIndex.{u, v}
    (Nat.add_comm r n) (PointedCGWH.orthogonalSphere.{u, v} n ⊗ K) X
    (nativeLeftFaces.{u, v} n r K ≫ f)
  rw [native_left_faces_evaluate n r K X f] at h
  have ht :
      (CanonicalSourceRightModuleActions.toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv ≫
        eqToHom (congrArg (fun i => X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} i))
          (Nat.add_comm r n).symm) =
      Sequential.indexMap X (orderedTargetIso.{u, v} r n).hom := by
    simpa only using NativeDay.source_inverse_braid_target X r n
  simpa only [Category.assoc, ht] using h

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin
private local instance constructionMonoidal4 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The literal original raw-left Gamma equation at every target, level, sphere degree and
Gamma index, with the original mixed source cast and ordered-target action unchanged. -/
theorem raw_left_evaluate (X : Actual.OrthogonalCarrier.{u, v}) (r d n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r)
      (PointedCGWH.orthogonalSphere.{u, v} d) ⟶ X) :
    rawMixedEvaluate X r d n (nativeLeftFaces.{u, v} n r (PointedCGWH.orthogonalSphere.{u, v} d) ≫ f) =
      rawPowerAction X r d n f := by
  simpa only [rawMixedEvaluate, mixedLabelCast, rawPowerAction, Category.assoc] using
    NativeGammaFaceBridge.native_left_label_evaluate n r (PointedCGWH.orthogonalSphere.{u, v} d) X f

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin
