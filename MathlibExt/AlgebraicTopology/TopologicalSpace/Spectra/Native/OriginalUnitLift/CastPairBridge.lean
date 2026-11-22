/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Generic
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.PrimitivePair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.PairHEq
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Cast Pair Bridge

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped MonoidalClosed
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
section Selected
universe uV vV uJ
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} V]
  [CategoryTheory.Limits.HasProducts.{0} V] [CategoryTheory.Limits.HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- A proved type cast of the literal selected pair preserves its full coefficient equation. -/
theorem castPairFamily_coefficient
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (hM : primitiveMonoidal q c = M) (ha : c.indexMap = a) (ht : c.tensorIndex = t)
    (hType : Selected.PairFamilyType q c =
      Independent.PairFormula M (fun n X => Free.object (a n) X) t) :
    CoefficientFamily M a t (cast hType (Selected.pairFamily q c)) := by
  have hp : HEq (primitivePair q c) (cast hType (Selected.pairFamily q c)) :=
    (primitivePair_heq_original q c).trans
      ((Selected.pairFamily_heq_original q c).symm.trans
        (cast_heq hType (Selected.pairFamily q c)).symm)
  exact coefficientFamily_transport (primitiveMonoidal q c) M
    c.indexMap a c.tensorIndex t hM ha ht
    (primitivePair q c) (cast hType (Selected.pairFamily q c)) hp
    (primitivePair_coefficient q c)

end Selected
end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
