/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.DualCircuitToWalk
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.DualCircuitToWalk`

* `dcw_barrierEdge_exists` for the all-closed configuration on `rect 0 1 0 1`: a bottom-row barrier
  edge exists, and its quarter turn is an edge of the rotated barrier graph
  (`dcw_dualBarrierGraph_nonempty_edge`) and of the `dualConfig`-open graph
  (`dcw_dualBarrierGraph_le_open`).
* `dcw_leftRight_crossCount_odd`: the row walk from `(0, 0)` to `(1, 0)` crosses the boundary of
  the left-reach set an odd number of times.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box StatMech.Universality SimpleGraph

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.DualCircuitToWalk

/-- In the all-closed configuration, sites connected inside a set are equal. -/
theorem connWithin_closed {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 (fun _ => false) S x y) : x = y := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ =>
    rw [openSubgraphInduce_adj] at hadj
    simp [openSubgraph_adj] at hadj

/-- The all-closed configuration has no open horizontal crossing of `rect 0 1 0 1`. -/
theorem noH_closed : ¬ HorizontalCrossing (fun _ => false) 0 1 0 1 := by
  rintro ⟨x, y, hxy⟩
  have h := congrArg Subtype.val (connWithin_closed hxy)
  have hx : (x : Site 2) 0 = 0 := x.2.2
  have hy : (y : Site 2) 0 = 1 := y.2.2
  simp only at h
  rw [h] at hx
  omega

example : ∃ v w : Site 2, dcw_isBarrierEdge (fun _ => false) 1 v w ∧ v 1 = 0 ∧ w 1 = 0 :=
  dcw_barrierEdge_exists _ 1 (by norm_num) noH_closed

example : ∃ p q : Site 2, (openSubgraph 2 (dualConfig (fun _ => false))).Adj p q := by
  obtain ⟨p, q, h⟩ := dcw_dualBarrierGraph_nonempty_edge _ 1 (by norm_num) noH_closed
  exact ⟨p, q, dcw_dualBarrierGraph_le_open _ 1 h⟩

example (w : (hypercubicLattice 2).Walk ![0, 0] ![1, 0]) :
    ¬ Even (crossCount (bcd_leftReach (fun _ => false) 1) w) :=
  dcw_leftRight_crossCount_odd _ 1 noH_closed (by simp [leftSide]) (by simp [rightSide]) w

end MathlibExtTest.StatMech.Probability.Percolation.Universality.DualCircuitToWalk
