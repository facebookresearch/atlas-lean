/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.BoxCrossingDichotomy
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.BoxCrossingDichotomy`

* `bcd_separation` for the all-closed configuration on `rect 0 1 0 1` (which has no horizontal
  crossing): the left-reach set is finite, contains `(0, 0)`, and misses `(1, 0)`.
* `bcd_horizontal_iff_right_in_leftReach`: on the one-point square `rect 0 0 0 0` every
  configuration has a horizontal crossing.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box StatMech.Universality SimpleGraph

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.BoxCrossingDichotomy

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

example : (bcd_leftReach (fun _ => false) 1).Finite ∧ (![0, 0] : Site 2) ∈ bcd_leftReach (fun _ => false) 1 ∧
    (![1, 0] : Site 2) ∉ bcd_leftReach (fun _ => false) 1 := by
  obtain ⟨hfin, hleft, hdisj, -⟩ := bcd_separation (fun _ => false) 1 noH_closed
  refine ⟨hfin, hleft _ (by simp [leftSide]), fun h => ?_⟩
  exact Set.disjoint_left.1 hdisj h (by simp [rightSide])

example (ω : ConfigSpace (Sym2 (Site 2))) : HorizontalCrossing ω 0 0 0 0 :=
  (bcd_horizontal_iff_right_in_leftReach ω 0).2
    ⟨0, by simp [rightSide], by simp, 0, by simp [leftSide], by simp,
      connectedWithin_refl ω _ _⟩

end MathlibExtTest.StatMech.Probability.Percolation.Universality.BoxCrossingDichotomy
