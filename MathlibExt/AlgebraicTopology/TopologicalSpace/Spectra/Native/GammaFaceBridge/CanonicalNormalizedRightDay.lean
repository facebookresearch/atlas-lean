/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NormalizedRightDayReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceDayContext
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceDiagramPair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalDiagramPair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.NativeTypes
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeCanonicalPairCast

/-!
# Canonical Normalized Right Day

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

/-- Normalize the full original q/c right readback before any native specialization, so a
caller can apply the exact original indices and coefficient objects in the same term. -/
theorem cast_canonical_normalized_right_day_readback
    (ht : c.tensorIndex = fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r))
    (he : letI := q.dayMonoidal
      cast (congrArg (SourceDiagramFamilyType q) ht) c.diagramPair =
        (fun n r K L => (DayTensorBridge.originalTensorComparison q.monoidalData).app
          (Free.object n K, Free.object r L) ≪≫
          EnrichedDayKernel.FreePairComparison.iso q.monoidalData.tensorEnrichedFunctor n r K L))
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (hType : CanonicalSourceFreeSmash.SelectedPair.PairIsoType c =
      Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
        (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r))) :
    NormalizedRightDayReadback q c M hM
      (cast hType (CanonicalSourceFreeSmash.SelectedPair.pairIso c)) :=
  selected_right_day_readback_drop_comparison q c M hM
    (cast hType (CanonicalSourceFreeSmash.SelectedPair.pairIso c))
    (cast_canonical_right_day_readback q c q.monoidalData.tensorEnrichedFunctor
      (DayTensorBridge.originalTensorComparison q.monoidalData) ht he M hM hType)

end Selected
end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
