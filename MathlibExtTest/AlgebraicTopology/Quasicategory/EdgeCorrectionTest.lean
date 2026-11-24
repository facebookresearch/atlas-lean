/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeCorrection

/-! # Public client for strict edge correction

The given endpoints are fixed, the represented source morphism is
preserved, and the actual mapped edge equals the prescribed base edge.
No equivalence assumption on either edge is supplied.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.EdgeCorrectionTest

/-- The neutral API corrects any edge with the exact endpoints and
mapped edge, while preserving its represented morphism. -/
theorem exists_corrected_edge_with_edge_eq {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.InnerFibration p) [SSet.Quasicategory B]
    {x₀ x₁ : E _⦋0⦌} (u : SSet.Edge x₀ x₁)
    (w : SSet.Edge (p.app _ x₀) (p.app _ x₁))
    (h : SSet.HomotopyCategory.homMk w = SSet.HomotopyCategory.homMk (u.map p)) :
    ∃ u' : SSet.Edge x₀ x₁, SSet.HomotopyCategory.homMk u' = SSet.HomotopyCategory.homMk u ∧
      u'.map p = w := by
  obtain ⟨u', hu', hmap⟩ := SSet.exists_edge_correction_of_innerFibration p hp u w h
  exact ⟨u', hu', SSet.Edge.ext hmap⟩

end MathlibExtTest.AlgebraicTopology.Quasicategory.EdgeCorrectionTest
