/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.Crossings

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.Crossings`

Tests the definitions `StatMech.TwoDim.rectangle`, its sides, `HorizontalCrossing` and
`horizontalCrossingEvent`: membership in `rectangle 1 0`, the all-open configuration crosses
`rectangle 1 0` (a one-edge path), every configuration crosses the degenerate `rectangle 0 b`, and
the crossing events are increasing (applied to the all-closed ≤ all-open pair).
-/

@[expose] public section

open StatMech StatMech.TwoDim StatMech.Lattice

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.Crossings

-- Membership in the rectangle and its sides.
example : (![1, 0] : Site 2) ∈ rectangle 1 0 := by simp [mem_rectangle]

example : (![0, 0] : Site 2) ∈ leftSide 1 0 := by simp [leftSide, mem_rectangle]

example : (![2, 0] : Site 2) ∉ rectangle 1 0 := by simp [mem_rectangle]

-- The all-open configuration crosses `[0, 1] × [0, 0]` along the edge `(0,0)–(1,0)`.
theorem allOpen_mem_horizontalCrossingEvent :
    (fun _ => true : ConfigSpace (Sym2 (Site 2))) ∈ horizontalCrossingEvent 1 0 := by
  refine ⟨⟨![0, 0], by simp [leftSide, mem_rectangle]⟩,
    ⟨![1, 0], by simp [rightSide, mem_rectangle]⟩, ?_⟩
  refine SimpleGraph.Adj.reachable ?_
  rw [openSubgraphInduce_adj, openSubgraph_adj]
  refine ⟨?_, rfl⟩
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

-- Every configuration crosses the degenerate rectangle of width `0`.
example (ω : ConfigSpace (Sym2 (Site 2))) : ω ∈ horizontalCrossingEvent 0 0 :=
  ⟨⟨![0, 0], by simp [leftSide, mem_rectangle]⟩, ⟨![0, 0], by simp [rightSide, mem_rectangle]⟩,
    connectedWithin_refl _ _ _⟩

-- Monotonicity: all-closed ≤ all-open, applied to a crossing of the degenerate rectangle.
example : (fun _ => true : ConfigSpace (Sym2 (Site 2))) ∈ horizontalCrossingEvent 0 0 :=
  horizontalCrossingEvent_increasing (ω := fun _ => false) (fun _ => Bool.false_le _)
    ⟨⟨![0, 0], by simp [leftSide, mem_rectangle]⟩, ⟨![0, 0], by simp [rightSide, mem_rectangle]⟩,
      connectedWithin_refl _ _ _⟩

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.Crossings
