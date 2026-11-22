/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CanonicalPairEquality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.PredicateTransport

/-!
# Native Canonical Pair Cast

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
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
open scoped MonoidalClosed
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary

theorem canonical_pair_type_native :
    CanonicalSourceFreeSmash.SelectedPair.PairIsoType CanonicalSourceFreeSmash.pairData.{u, v} =
      NativeFamilyType.{u, v} :=
  (canonical_pair_type SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}).trans
    pairFamily_type_native.{u, v}

/-- The original native family is exactly the canonical source family after its same complete
type transport; equality cases are resolved before native instantiation. -/
theorem native_pair_eq_canonical_cast :
    nativePairFamily.{u, v} = cast canonical_pair_type_native.{u, v}
      (CanonicalSourceFreeSmash.SelectedPair.pairIso CanonicalSourceFreeSmash.pairData.{u, v}) := by
  delta nativePairFamily
  exact predicate_eq_mp pairFamily_type_native.{u, v}
    (Selected.pairFamily SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v})
    (fun p : NativeFamilyType.{u, v} => p = cast canonical_pair_type_native.{u, v}
      (CanonicalSourceFreeSmash.SelectedPair.pairIso CanonicalSourceFreeSmash.pairData.{u, v}))
    (cast_pair_eq SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
      NativeFamilyType.{u, v} pairFamily_type_native.{u, v} canonical_pair_type_native.{u, v})

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
