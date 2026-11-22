/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialIndexSourceBridge
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftSourceAction

/-!
# Original Target Braid

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open scoped MonoidalClosed
attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  MonoidalLeftAction.monoidalOppositeLeftAction Enriched.prodCategory

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeDay
open OriginalSequentialIndexSourceBridge CanonicalSourceRightModuleActions
private local instance constructionCategory1 : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
private local instance constructionMonoidal2 : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u,
  v}
private local instance constructionEnrichedCategory3 : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
private local instance constructionSymmetric4 : SymmetricCategory OrthogonalIndex :=
  OrthogonalIndex.symmetricCategory.{u, v}
private local instance constructionMonoidal5 : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  :=
  OrthogonalDay.monoidalCategory.{u, v}
private local instance constructionMonoid6 : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}

/-- The original finite ordered target word maps to the same complete inverse continuous braid
and the original degree-label cast. -/
theorem bare_ordered_target_word (r n : ℕ) :
    bareIndexFunctor.{u, v}.mapIso (Sequential.orderedTargetPermutation r n) =
      (β_ (n : OrthogonalIndex) r).symm ≪≫ eqToIso (Nat.add_comm n r) := by
  rw [Sequential.orderedTargetPermutation, Functor.mapIso_trans, Functor.mapIso_symm,
    bareIndexFunctor_braidingIso, eqToIso_map]
  rfl

/-- The full inverse source braid followed by the original label equality is the unchanged
actual ordered target action on every native diagram. -/
theorem source_inverse_braid_target (X : Actual.OrthogonalCarrier.{u, v}) (r n : ℕ) :
    (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ (n : OrthogonalIndex) r).inv ≫
      eqToHom (congrArg (fun k => (toModule X).X.toEnrichedFunctor.obj k) (Nat.add_comm n r)) =
    Sequential.indexMap X (orderedTargetIso.{u, v} r n).hom := by
  have hm := mappedIndexIso_hom_value X (Sequential.orderedTargetPermutation r n)
  change Sequential.indexMap X (orderedTargetIso.{u, v} r n).hom =
      (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map
        (bareIndexFunctor.{u, v}.mapIso (Sequential.orderedTargetPermutation r n)).hom at hm
  rw [bare_ordered_target_word, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp] at hm
  change Sequential.indexMap X (orderedTargetIso.{u, v} r n).hom =
    (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ (n : OrthogonalIndex) r).inv ≫
      (toModule X).X.toEnrichedFunctor.toOrdinaryFunctor.map (eqToHom (Nat.add_comm n r)) at hm
  rw [eqToHom_map] at hm
  exact hm.symm

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeDay
