/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.Defs

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.Defs`

Tests the definitions of `StatMech.RSW.Box`: `rect` and its sides, `horizontalCrossingEvent`
(the all-open configuration crosses `rect 0 1 0 0`; the event is increasing), `annulus`
membership, `boxCrossingEvent`, and the named box-crossing properties `P5` and `P5c`, proved for
constant set functions (`1` and `1/2`) and related by `P5c.p5`.
-/

@[expose] public section

open MeasureTheory StatMech StatMech.RSW StatMech.RSW.Box StatMech.Lattice

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.Defs

-- `rect` membership.
example : (![1, 0] : Site 2) ∈ rect 0 1 0 0 := by simp [mem_rect]

example : (![0, 2] : Site 2) ∉ rect 0 1 0 1 := by simp [mem_rect]

-- The all-open configuration crosses `[0, 1] × [0, 0]`.
theorem allOpen_mem_horizontalCrossingEvent :
    (fun _ => true : ConfigSpace (Sym2 (Site 2))) ∈ horizontalCrossingEvent 0 1 0 0 := by
  refine ⟨⟨![0, 0], by simp [mem_rect]⟩, ⟨![1, 0], by simp [mem_rect]⟩, ?_⟩
  refine SimpleGraph.Adj.reachable ?_
  rw [openSubgraphInduce_adj, openSubgraph_adj]
  refine ⟨?_, rfl⟩
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

-- Monotonicity of the crossing event.
example (ω : ConfigSpace (Sym2 (Site 2))) (h : ω ∈ horizontalCrossingEvent 0 1 0 0) :
    (fun _ => true : ConfigSpace (Sym2 (Site 2))) ∈ horizontalCrossingEvent 0 1 0 0 :=
  Box.horizontalCrossingEvent_increasing (fun _ => Bool.le_true _) h

-- Rectangle crossing events are genuine measurable events on the infinite bond cube.
example : MeasurableSet (horizontalCrossingEvent 0 1 0 0) :=
  measurableSet_horizontalCrossingEvent 0 1 0 0

example : MeasurableSet (verticalCrossingEvent 0 1 0 0) :=
  measurableSet_verticalCrossingEvent 0 1 0 0

-- `(2, 0)` lies in the annulus `Λ_2 \ Λ_1` around the origin.
example : (![2, 0] : Site 2) ∈ annulus 0 1 := by
  rw [mem_annulus]
  refine ⟨![2, 0], ⟨?_, ?_⟩, by simp⟩
  · rw [mem_box]; intro i; fin_cases i <;> simp
  · rw [mem_box]; push Not; exact ⟨0, by simp⟩

-- `boxCrossingEvent` unfolds to a rectangle crossing.
example : boxCrossingEvent 2 3 = horizontalCrossingEvent 0 6 0 3 := by
  simp only [boxCrossingEvent]
  norm_num

-- `P5` and `P5c` for constant set functions.
example : P5 (fun _ _ => 1) := fun _ _ => ⟨1, one_pos, fun _ => le_rfl⟩

theorem p5c_half : P5c (Ξ := Unit) (fun _ _ _ => 1 / 2) :=
  fun _ _ => ⟨1 / 2, by norm_num, fun _ _ => ⟨le_rfl, by norm_num⟩⟩

example : P5 (fun _ _ => (1 / 2 : ℝ)) := p5c_half.p5 ()

end MathlibExtTest.StatMech.Probability.Percolation.RSW.Defs
