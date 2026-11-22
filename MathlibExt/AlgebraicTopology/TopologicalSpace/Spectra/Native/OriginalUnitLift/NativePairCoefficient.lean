/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Generic
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.PrimitivePair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.PairHEq
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.CastPairBridge
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.NativeTypes
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.CoefficientTransport
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Native Pair Coefficient

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped MonoidalClosed
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits

private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}


theorem native_index_map_eq : CanonicalSourceFreeSmash.pairData.{u, v}.indexMap =
    OrthogonalOperatorIndex.ofIndex.{u, v} := rfl

theorem native_tensor_index_eq : CanonicalSourceFreeSmash.pairData.{u, v}.tensorIndex =
    (fun n r : ℕ => n + r) := rfl

theorem native_pair_cast_type :
    Selected.PairFamilyType SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v} =
      Independent.PairFormula CanonicalSourceSmash.monoidalCategory.{u, v}
        (fun n X => Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) X) (fun n r => n + r) :=
  pairFamily_type_native.{u, v}

set_option maxHeartbeats 500000 in
theorem nativePair_coefficient_from_cast : CoefficientFamily
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v}
    OrthogonalOperatorIndex.ofIndex.{u, v} (fun n r => n + r)
    (cast pairFamily_type_native.{u, v}
      (Selected.pairFamily SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v})) := by
  have h := castPairFamily_coefficient (V := PointedCGWH.{u, v})
    (J := OrthogonalOperatorIndex.{u, v}) SphereSmash.sourceData.{u, v}
    CanonicalSourceFreeSmash.pairData.{u, v}
    CanonicalSourceSmash.monoidalCategory.{u, v}
    OrthogonalOperatorIndex.ofIndex.{u, v} (fun n r => n + r)
    native_primitive_monoidal_eq.{u, v} native_index_map_eq.{u, v}
    native_tensor_index_eq.{u, v} native_pair_cast_type.{u, v}
  exact h

set_option maxHeartbeats 500000 in
theorem nativePair_coefficient_family : CoefficientFamily
    (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v}
    OrthogonalOperatorIndex.ofIndex.{u, v} (fun n r => n + r) nativePairFamily.{u, v} := by
  delta nativePairFamily
  exact coefficientFamily_eq_mp (V := PointedCGWH.{u, v})
    (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v}
    OrthogonalOperatorIndex.ofIndex.{u, v} (fun n r => n + r)
    (Selected.PairFamilyType SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v})
    pairFamily_type_native.{u, v}
    (Selected.pairFamily SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v})
    nativePair_coefficient_from_cast.{u, v}

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
