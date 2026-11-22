/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftFaceEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeNamedLeftWord

/-!
# Native Left Face Evaluation

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

/-- Every complete original native left face followed by every complete native
free map has the full original source action, coefficient braid and index braid. -/
theorem native_left_faces_evaluate (n r : ℕ) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ K) X (nativeLeftFaces.{u, v} n r K ≫ f) =
    (PointedCGWH.orthogonalSphere.{u, v} n ◁
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f) ≫
      (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))).hom ≫
      sphereAction X r n ≫
        (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv := by
  exact (PairCastBoundary.left_faces_evaluation_word_formula
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} gamma.{u, v} nativePairFamily.{u, v}
    nativeLeftFaces.{u, v} nativeLeftFaces_original.{u, v} n r K X f).trans
      (original_native_named_left_word_evaluate.{u, v} n r K X f)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
