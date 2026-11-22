/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Generic
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Primitive Pair

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

open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-- The primitive source-module tensor transported along the selected source equivalence. -/
@[instance_reducible]
def primitiveMonoidal : MonoidalCategory (EnrichedFunctorCat V J) :=
  @Monoidal.transport q.Module q.moduleCategory q.primitiveMonoidal
    (EnrichedFunctorCat V J) inferInstance c.sourceEquivalence

/-- The selected free-pair comparison for the transported primitive tensor. -/
def primitivePair : Independent.PairFormula (primitiveMonoidal q c)
    (fun n X => Free.object (c.indexMap n) X) c.tensorIndex := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  exact CanonicalSourceFreeSmash.SelectedPair.pairIso c

set_option maxHeartbeats 500000 in
theorem primitivePair_coefficient : CoefficientFamily
    (primitiveMonoidal q c) c.indexMap c.tensorIndex (primitivePair q c) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  exact CanonicalSourceFreeSmash.SelectedPair.coefficientEquation c

theorem primitiveMonoidal_eq_source : primitiveMonoidal q c =
    (TypedFullPowerData.sourceContext c).monoidalCategory := by
  exact (congrArg
    (fun M : @MonoidalCategory q.Module q.moduleCategory =>
      @Monoidal.transport q.Module q.moduleCategory M
        (EnrichedFunctorCat V J) inferInstance c.sourceEquivalence)
    q.moduleMonoidal_eq_primitive).symm

end Selected
end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
