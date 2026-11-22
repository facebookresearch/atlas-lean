/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Canonical Pair Equality

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uJ
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped MonoidalClosed
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [HasColimitsOfSize.{0, 0} V] [HasProducts.{0} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The selected tensor and its original primitive constructor give the same whole pair type. -/
theorem canonical_pair_type : CanonicalSourceFreeSmash.SelectedPair.PairIsoType c =
    Selected.PairFamilyType q c := by
  unfold Selected.PairFamilyType
  rw [q.moduleMonoidal_eq_primitive]
  rfl

/-- A common whole family type makes the original selected/canonical pair relation an exact
equality before any concrete source-instance specialization. -/
theorem cast_pair_eq (T : Type (max (max uJ uV) vV)) (h : Selected.PairFamilyType q c = T)
    (k : CanonicalSourceFreeSmash.SelectedPair.PairIsoType c = T) :
    cast h (Selected.pairFamily q c) = cast k (CanonicalSourceFreeSmash.SelectedPair.pairIso c) := by
  exact eq_of_heq ((cast_heq h (Selected.pairFamily q c)).trans
    ((Selected.pairFamily_heq_original q c).trans
      (cast_heq k (CanonicalSourceFreeSmash.SelectedPair.pairIso c)).symm))

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
