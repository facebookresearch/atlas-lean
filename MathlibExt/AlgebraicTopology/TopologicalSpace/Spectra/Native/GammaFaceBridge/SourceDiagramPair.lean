/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalDiagramPair

/-!
# Source Diagram Pair

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uV vV
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open PointedCGWH.Spectra.Orthogonal
open scoped MonoidalClosed
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [HasColimitsOfSize.{0, 0} V] [HasProducts.{0} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)

/-- The whole original selected Day pair retains the original identity comparison at the
same selected source-data projection, without expanding a concrete source constructor. -/
theorem selected_diagram_pair_eq_original_comparison :
    letI := q.dayMonoidal
    SphereSmashFree.Selected.diagramPair q =
      (fun n r K L => (DayTensorBridge.originalTensorComparison q.monoidalData).app
        (Free.object n K, Free.object r L) ≪≫
        EnrichedDayKernel.FreePairComparison.iso q.monoidalData.tensorEnrichedFunctor n r K L) := by
  let := q.dayMonoidal
  funext n r K L
  exact DayTensorBridge.original_diagram_pair_eq_comparison q.monoidalData n r K L

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
