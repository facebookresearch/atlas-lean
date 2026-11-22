/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryChart
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramProjectiveMonomorphisms

/-!
# The unchanged native root-boundary attachment is monic

The actual free-root pushout gives the native supported inclusion its
genuine projective left class. The original coherent model and actual
coefficient evaluation turn that same inclusion into a cofibration and
a monomorphism. These properties preserve the original map over every
base, rather than assuming an all-face boundary source comparison.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual whole native supported root-boundary map is monic over every original base simplex. -/
instance (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) : Mono (nativeRootBoundaryChartMap B n σ) :=
  coherentDiagram_projectiveLeft_mono B (nativeRootBoundaryChartMap B n σ)
    (nativeRootBoundaryChartMap_projectiveLeft B n σ)

/-- The same unchanged native supported root-boundary map is a cofibration in the genuinely constructed original
coherent marked model. -/
theorem nativeRootBoundaryChartMap_cofibration (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    let _ := coherentDiagramModelCategory B
    Cofibration (nativeRootBoundaryChartMap B n σ) := by
  let _ := coherentDiagramModelCategory B
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativeRootBoundaryChartMap_projectiveLeft B n σ

end SSet.Marked
