/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryAfter
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryMonomorphism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootRelativeCofibration

/-!
# The actual whole positive native chart inside the complete boundary

The original positive-maximum cone map into the actual root boundary
is left-extended along the same original base simplex. Its attaching
composite remains the unchanged original positive native chart map.
Every original marked coefficient and complete coherent path is kept.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The unchanged whole original positive native chart enters the same actual complete native root-boundary chart. -/
def nativePositiveRootBoundaryMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    nativePositiveRootChart B n σ ⟶ nativeRootBoundaryChart B n σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map
    (coneRootBoundaryAfterMap n)

/-- The actual whole positive-to-boundary map keeps precisely its unchanged original positive chart attaching map. -/
theorem nativePositiveRootBoundaryMap_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    nativePositiveRootBoundaryMap B n σ ≫ nativeRootBoundaryChartMap B n σ =
      nativePositiveRootChartMap B n σ := by
  let L := EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  exact (L.map_comp (coneRootBoundaryAfterMap n) (coneRootBoundaryDiagramInclusion n)).symm.trans
    (congrArg L.map (coneRootBoundaryAfterMap_inclusion n))

/-- The same full original positive native chart map into the supported boundary is genuinely monic. -/
instance (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) : Mono (nativePositiveRootBoundaryMap B n σ) := by
  have hm : Mono (nativePositiveRootChartMap B n σ) :=
    coherentDiagram_projectiveLeft_mono B (nativePositiveRootChartMap B n σ)
      (nativePositiveRootChart_projectiveLeft B n σ)
  let _ : Mono (nativePositiveRootChartMap B n σ) := hm
  exact mono_of_mono_fac (nativePositiveRootBoundaryMap_attachment B n σ)

end SSet.Marked
