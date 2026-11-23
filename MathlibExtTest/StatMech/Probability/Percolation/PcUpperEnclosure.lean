/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.PcUpperEnclosure

/-!
# Tests for `MathlibExt.Probability.Percolation.PcUpperUncond`

Tests the dual-circuit machinery of `StatMech.Percolation.pc_lt_one_of_enclosure`:
`measure_closedCircuitEvent` on a one-step dual walk (probability `1 - p`, so `1/2` at `p = 1/2`)
and on the empty walk (probability `1`), `anchorFinset_card`, and `pcSummandTwo` at `ℓ = 0` and
`p = 1`. The named hypothesis `PcAnchoredEnclosure` (every finite origin cluster is enclosed by an
anchored face-boundary cycle) is not proved in the library and has no cheap witness; the headline
`pc_lt_one_of_enclosure` and `one_sub_theta_le` are restated with it.
-/

@[expose] public section

open StatMech StatMech.Percolation StatMech.Lattice
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.PcUpperUncond

/-- A one-step walk from the origin to its right neighbour. -/
noncomputable def stepWalk : (hypercubicLattice 2).Walk (origin 2)
    (coordShift (origin 2) 0 (stepSign true)) :=
  SimpleGraph.Walk.cons (adj_coordShift _ _ _) SimpleGraph.Walk.nil

-- The one-step walk crosses one primal edge, which is closed with probability `1 - p`.
example (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedCircuitEvent stepWalk) =
      ((1 - p : ℝ≥0) : ENNReal) := by
  rw [measure_closedCircuitEvent]
  simp [primalEdgeFinset, stepWalk]

example (hp : (1 / 2 : ℝ≥0) ≤ 1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) hp) (closedCircuitEvent stepWalk) =
      ((1 / 2 : ℝ≥0) : ENNReal) := by
  rw [measure_closedCircuitEvent]
  simp [primalEdgeFinset, stepWalk]

-- The empty walk crosses no edge.
example (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
      (closedCircuitEvent
        (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk (origin 2) _)) = 1 := by
  rw [measure_closedCircuitEvent]
  simp [primalEdgeFinset]

-- Anchor count and summands of the doubled Peierls series.
example : (anchorFinset 3).card ≤ 6 := anchorFinset_card 3

example (p : ℝ) : pcSummandTwo p 0 = 0 := by simp [pcSummandTwo]

example : pcSummandTwo 1 2 = 0 := by simp [pcSummandTwo]

-- The headline and the contour bound, with the unproved hypothesis inlined.
example (henc : PcAnchoredEnclosure) : pc 2 < 1 := pc_lt_one_of_enclosure henc

example (henc : PcAnchoredEnclosure) (p : ℝ≥0) (hp : p ≤ 1) (hsum : ‖pcRatio (p : ℝ)‖ < 1) :
    1 - theta 2 p hp ≤ 2 * pcUpperBound (p : ℝ) :=
  one_sub_theta_le henc p hp hsum

end MathlibExtTest.StatMech.Probability.Percolation.PcUpperUncond
