/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeCanonicalLeftEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeLeftWordEvaluation

/-!
# Native Named Left Word

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
private local instance constructionMonoid2 : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
private local instance constructionMonoidal3 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The complete original native pair evaluated word is the complete original
source left word for every original Gamma index, level, coefficient and free map. -/
theorem original_native_named_left_word_evaluate (n r : ℕ) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    PairCastBoundary.LeftPairEvaluationWord
      CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
      (fun n r => n + r) nativePairFamily.{u, v}
      n r (PointedCGWH.orthogonalSphere.{u, v} n) K X (gamma.{u, v} n) f =
    (PointedCGWH.orthogonalSphere.{u, v} n ◁
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f) ≫
      (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))).hom ≫
      sphereAction X r n ≫
        (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv := by
  have hCast := (original_canonical_left_evaluation_word.{u, v}
    n r (PointedCGWH.orthogonalSphere.{u, v} n) K X (gamma.{u, v} n) f).trans
      (original_native_left_word_evaluate.{u, v} n r K X f)
  exact Eq.subst (motive := fun p : NativeFamilyType.{u, v} =>
      PairCastBoundary.LeftPairEvaluationWord
        CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
        (fun n r => n + r) p
        n r (PointedCGWH.orthogonalSphere.{u, v} n) K X (gamma.{u, v} n) f =
      (PointedCGWH.orthogonalSphere.{u, v} n ◁
        Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f) ≫
        (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))).hom ≫
        sphereAction X r n ≫
          (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv)
    PairCastBoundary.native_pair_eq_canonical_cast.{u, v}.symm hCast

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
