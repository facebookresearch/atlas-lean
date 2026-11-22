/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CastLeftDayFamilyReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalDiagramPair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceDiagramPair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceDayContext
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.NativeTypes
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeCanonicalPairCast

/-!
# Canonical Cast Left Day Readback

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
open NativeModuleEvaluation
section Selected
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [HasColimitsOfSize.{0, 0} V] [HasProducts.{0} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The left-unit Day evaluation identity after transport to the selected native tensor using its
monoidal equality. -/
def SelectedCastLeftDayReadback (T : EnrichedFunctor V (ℕ × ℕ) ℕ)
    (tensorComparison : SourceDayComparisonType q T)
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (p : Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
      (fun n r => T.obj (n, r))) : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  CastLeftDayFamilyReadback q.coefficient c.sourceEquivalence c.indexMap c.evaluationComparison
    T tensorComparison M hM p

/-- Preserve the entire selected source context while resolving the original index,
diagram, target-tensor and pair-family equalities before native specialization. -/
theorem cast_canonical_left_day_readback (T : EnrichedFunctor V (ℕ × ℕ) ℕ)
    (tensorComparison : SourceDayComparisonType q T)
    (ht : c.tensorIndex = fun n r => T.obj (n, r))
    (he : letI := q.dayMonoidal
      cast (congrArg (SourceDiagramFamilyType q) ht) c.diagramPair =
        (fun n r K L => tensorComparison.app (Free.object n K, Free.object r L) ≪≫
          EnrichedDayKernel.FreePairComparison.iso T n r K L))
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (hType : CanonicalSourceFreeSmash.SelectedPair.PairIsoType c =
      Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
        (fun n r => T.obj (n, r))) :
    SelectedCastLeftDayReadback q c T tensorComparison M hM
      (cast hType (CanonicalSourceFreeSmash.SelectedPair.pairIso c)) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  cases c with
  | mk E a h t e hc =>
    change t = _ at ht
    subst t
    have he' : e = fun n r K L => tensorComparison.app (Free.object n K, Free.object r L) ≪≫
        EnrichedDayKernel.FreePairComparison.iso T n r K L := by
      simpa only [cast_eq] using he
    exact cast_family_left_day_readback q.coefficient E a h T tensorComparison e he' M hM hType

end Selected

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
