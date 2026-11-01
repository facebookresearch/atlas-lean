/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Omega

/-!
# A parent step towards a root in a connected graph

A generic metric-graph fact: in a connected graph every vertex `v ≠ s` has a
neighbor one step closer to `s` (a parent of `v` in a breadth-first tree rooted
at `s`). This was previously proved in the unrooted-tree-counting development;
it is generic graph theory, so it lives here.
-/

@[expose] public section

namespace SimpleGraph

/-- In a connected graph every vertex `v ≠ s` has a neighbor `p` one step closer to `s`
(a parent of `v` in a breadth-first tree rooted at `s`). -/
theorem exists_parent {V : Type*} {G : SimpleGraph V} (hG : G.Connected) {s v : V}
    (hv : v ≠ s) : ∃ p, G.Adj v p ∧ G.dist s p + 1 = G.dist s v := by
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist v s
  cases q with
  | nil => exact absurd rfl hv
  | @cons _ c _ h q' =>
    refine ⟨c, h, ?_⟩
    have h1 := SimpleGraph.dist_le q'
    have h2 := (SimpleGraph.dist_eq_one_iff_adj.mpr h)
    have h3 := hG.dist_triangle (u := v) (v := c) (w := s)
    simp only [SimpleGraph.Walk.length_cons] at hq
    rw [SimpleGraph.dist_comm (u := s), SimpleGraph.dist_comm (u := s)]
    omega

end SimpleGraph
