/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.DualCutToPath
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.DualCutToPath`

* `dcp_topBarrierEdge_exists` and `dcp_rotatedCut_nonempty_edge` for the all-closed configuration
  on `rect 0 1 0 1`.
* `dcp_rot90_bottomRow`, `dcp_rot90_topRow` at concrete points.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box StatMech.Universality SimpleGraph

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.DualCutToPath

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

example : ∃ v w : Site 2, dcw_isBarrierEdge (fun _ => false) 1 v w ∧ v 1 = 1 ∧ w 1 = 1 :=
  dcp_topBarrierEdge_exists _ 1 (by norm_num) noH_closed

example : ∃ p q : Site 2, (dcw_dualBarrierGraph (fun _ => false) 1).Adj p q ∧
    p ∈ rect (-1) 0 0 1 ∧ q ∈ rect (-1) 0 0 1 :=
  dcp_rotatedCut_nonempty_edge _ 1 (by norm_num) noH_closed

example : rot90Fun ![3, 0] = ![0, 3] := dcp_rot90_bottomRow 3

example : rot90Fun ![3, 2] = ![-2, 3] := dcp_rot90_topRow 3 2

end MathlibExtTest.StatMech.Probability.Percolation.Universality.DualCutToPath
