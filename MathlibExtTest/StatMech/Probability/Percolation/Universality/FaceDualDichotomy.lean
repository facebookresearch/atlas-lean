/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.FaceDualDichotomy
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.FaceDualDichotomy`

* `fdd_square_dichotomy` (the separation bundle, not the dichotomy) for the all-closed
  configuration on `rect 0 1 0 1`: the left-reach set has a face-boundary cycle.
* `fdd_cluster_dualCircuit_open` for the all-closed configuration: the cluster `{0}` is
  surrounded by a face-boundary cycle with every separating edge closed.
* `fdd_straight_dualEdges_disjoint` at face `(0, 0)`.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box StatMech.Universality SimpleGraph

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualDichotomy

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

example : ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach (fun _ => false) 1)).Walk u u),
    c.IsCycle :=
  (fdd_square_dichotomy _ 1 (by norm_num) noH_closed).2.2.2

/-- In the all-closed configuration the cluster of `o` is `{o}`. -/
theorem cluster_closed (o : Site 2) : cluster 2 (fun _ => false) o = {o} := by
  ext y
  simp only [mem_cluster, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w⟩
    cases w with
    | nil => rfl
    | cons h _ => simp [openSubgraph_adj] at h
  · rintro rfl
    exact connected_refl _ _

example : ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 (fun _ => false) 0)).Walk u u),
    c.IsCycle ∧ (∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      dualConfig (fun _ => false) (crossEdge (sharedPrimalEdge f g)) = true) := by
  refine fdd_cluster_dualCircuit_open 0 (by rw [cluster_closed]; exact Set.finite_singleton _)
    (z := ![1, 0]) ?_ (by rw [cluster_closed]; intro h; have := congrFun h 0; simp at this)
  exact (Adj.toWalk (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide))

example {p : Site 2} (h1 : p ∈ crossEdge (sharedPrimalEdge ![0, 0] ![0 - 1, 0]))
    (h2 : p ∈ crossEdge (sharedPrimalEdge ![0, 0] ![0 + 1, 0])) : False :=
  fdd_straight_dualEdges_disjoint 0 0 h1 h2

end MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualDichotomy
