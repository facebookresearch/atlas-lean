/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeLeftCompositionGetters
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeLeftUnitCoefficient

/-!
# Native Left Word Evaluation

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
open PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
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

set_option maxHeartbeats 500000 in
/-- Every entire original left Day word has the native Gamma identity coefficient
and complete arbitrary native free coefficient, followed by the full source left
action, coefficient braid and inverse original source-index braid. -/
theorem original_native_left_word_evaluate (n r : ℕ) (K : PointedCGWH.{u, v})
    (X : CanonicalSourceSmash.Carrier.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ X) :
    PairCastBoundary.NormalizedLeftDayWord
      SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      CanonicalSourceSmash.monoidalCategory.{u, v} native_primitive_monoidal_eq.{u, v}
      n r (PointedCGWH.orthogonalSphere.{u, v} n) K X (gamma.{u, v} n) f =
    (PointedCGWH.orthogonalSphere.{u, v} n ◁
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K X f) ≫
      (β_ (PointedCGWH.orthogonalSphere.{u, v} n)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))).hom ≫
      sphereAction X r n ≫
        (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv := by
  have h := PairCastBoundary.normalized_left_day_word_factors
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
    CanonicalSourceSmash.monoidalCategory.{u, v} native_primitive_monoidal_eq.{u, v}
    n r (PointedCGWH.orthogonalSphere.{u, v} n) K X (gamma.{u, v} n) f
  rw [original_named_left_source_action_getter, original_named_left_target_tail_getter] at h
  rw [native_left_unit_coefficient, native_left_map_coefficient] at h
  have h0 := h.trans ((Category.assoc _ _ _).symm.trans (Category.comp_id _))
  exact h0.trans (by simp only [id_tensorHom])

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
