/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCellPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanCofibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningSimplex
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramModel

/-!
# Genuine native left extension of the original root attachment

The complete original positive-maximum source attaches to the original
cone by its proved free-root pushout. The genuine original enriched
left-extension adjunction transports that same whole projective map
over every original base simplex. This is an actual relative native
chart cofibration, before identifying the positive source with native
straightening of the original zeroth face or completing all boundary
latching and straightening weak-class comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The native whole positive-maximum root chart is its genuine original enriched left extension. -/
def nativePositiveRootChart (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) : EnrichedDiagram (realization B)ᵒᵖ :=
  EnrichedLeftKan.object (EnrichedFunctor.opposite (simplexInto B σ))
    (coneAfterDiagram (⊥ : Vertex.{u} n))

/-- The actual relative positive-maximum native chart map retains the entire original root attachment and
  base simplex. -/
def nativePositiveRootChartMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    nativePositiveRootChart B n σ ⟶ nativeSimplexChart B n σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map
    (coneAfterDiagramInclusion (⊥ : Vertex.{u} n))

/-- The whole original positive-maximum relative chart map has the genuine native projective left class for
  all original simplex dimensions and value universes. -/
theorem nativePositiveRootChart_projectiveLeft (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (nativePositiveRootChartMap B n σ) :=
  enrichedLeftKan_freeLeft (EnrichedFunctor.opposite (simplexInto B σ)) coefficientGeneratingMonos
    (coneAfterDiagramInclusion (⊥ : Vertex.{u} n)) (coneAfterRootInclusion_projectiveLeft n)

/-- The same complete original native root attachment is an actual cofibration in the genuinely constructed
  coherent marked model over every original base and value universe. -/
theorem nativePositiveRootChart_cofibration (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    let _ := coherentDiagramModelCategory B
    Cofibration (nativePositiveRootChartMap B n σ) := by
  let _ := coherentDiagramModelCategory B
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativePositiveRootChart_projectiveLeft B n σ

end SSet.Marked
