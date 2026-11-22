/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeSharpRootMarkPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeConcreteImageIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanCofibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramProjectiveMonomorphisms

/-!
# The actual original native sharp-edge marking chart attachment

The whole original interval marking cell lies over the unchanged base
edge. Its original maximum-preserving to sharp cone map has its actual
native enriched left extension. The genuine marked free-root pushout
proves the projective left class of that same whole native chart map.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original whole interval marking cell over the actual unchanged base edge, retaining its exact minimal and
maximal markings. -/
def nativeMarkingCell (B : SSet.{u}) (σ : B _⦋1⦌) : nativeSimplexBasis B 1 σ ⟶ nativeSharpBasis B σ :=
  Over.homMk edgeMarkCell (Hom.ext (Category.id_comp _))

/-- Every original scalar simplex of the native marking cell is its unchanged underlying identity. -/
theorem nativeMarkingCell_hom (B : SSet.{u}) (σ : B _⦋1⦌) : (nativeMarkingCell B σ).left.hom = 𝟙 (Δ[1] : SSet.{u})
  := rfl

/-- The entire original interval marking chart map is the actual native left extension of the same whole original
cone marking map. -/
def nativeSharpMarkingChartMap (B : SSet.{u}) (σ : B _⦋1⦌) : nativeSimplexChart B 1 σ ⟶ nativeSharpChart B σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneSharp 1)

/-- The same actual original sharp-edge native chart map has the genuine projective left class over every original
base edge. -/
theorem nativeSharpMarkingChartMap_projectiveLeft (B : SSet.{u}) (σ : B _⦋1⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp (nativeSharpMarkingChartMap B σ) :=
  enrichedLeftKan_freeLeft (EnrichedFunctor.opposite (simplexInto B σ)) coefficientGeneratingMonos
    (coneSharp 1) coneSharpInterval_projectiveLeft

/-- The unchanged original sharp-edge native chart map is a cofibration in the actual original coherent marked model. -/
theorem nativeSharpMarkingChartMap_cofibration (B : SSet.{u}) (σ : B _⦋1⦌) :
    let _ := coherentDiagramModelCategory B
    Cofibration (nativeSharpMarkingChartMap B σ) := by
  let _ := coherentDiagramModelCategory B
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativeSharpMarkingChartMap_projectiveLeft B σ

end SSet.Marked
