/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutClusterNoCrossing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutClusterNoCrossing`

In the plane:
* `bc7_cut_edge_stays_in_cluster`: after forcing the edge `(1,0)–(2,0)` in the all-closed
  configuration and removing the origin, `(2,0)` is in the cut cluster of `(1,0)`;
* `bc7_cut_no_crossing`: no open edge joins the distinct cut clusters of `(1,0)` and `(0,1)` in the
  all-closed configuration;
* `bc7_cut_clusters_eq_of_openEdge_between` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutClusterNoCrossing

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- In the all-closed configuration only a site is connected to itself. -/
theorem closed_connected_eq {a b : Site 2} (h : Connected 2 closed2 a b) : a = b := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj.2 (by simp [closed2])

/-- Distinct sites have distinct clusters in the all-closed configuration. -/
theorem closed_cluster_ne {a b : Site 2} (hab : a ≠ b) :
    cluster 2 closed2 a ≠ cluster 2 closed2 b := by
  intro h
  have hb : b ∈ cluster 2 closed2 b := SimpleGraph.Reachable.refl b
  rw [← h] at hb
  exact hab (closed_connected_eq hb)

/-- `(1,0)` and `(2,0)` are lattice neighbours. -/
theorem adj10 : (hypercubicLattice 2).Adj ![1, 0] ![2, 0] := by
  simp [hypercubicLattice, NearestNeighbour, Fin.sum_univ_two]

/-- The edge `(1,0)–(2,0)` avoids the origin. -/
theorem notMem10 : (0 : Site 2) ∉ s(![1, 0], ![2, 0]) := by
  simp only [Sym2.mem_iff, not_or]
  constructor <;> intro h <;> simpa using congrFun h 0

-- A forced open edge keeps its far end in the cut cluster.
example : (![2, 0] : Site 2) ∈
    cluster 2 (removeSite 0 (forceOpenFinset {s(![1, 0], ![2, 0])} closed2)) ![1, 0] :=
  bc7_cut_edge_stays_in_cluster (SimpleGraph.Reachable.refl _)
    ⟨adj10, by
      unfold removeSite forceOpenFinset
      simp only [notMem10, ↓reduceIte, Finset.mem_singleton]⟩

-- No open edge between distinct cut clusters of the all-closed configuration.
example : ¬ IsOpenEdge 2 (removeSite 0 closed2) ![1, 0] ![0, 1] := by
  have hrm : removeSite 0 closed2 = closed2 := by
    funext e; simp [removeSite, closed2]
  refine bc7_cut_no_crossing ?_ (SimpleGraph.Reachable.refl _) (SimpleGraph.Reachable.refl _)
  rw [hrm]
  exact closed_cluster_ne fun h => by simpa using congrFun h 0

-- An open edge between two cut clusters merges them.
example (ω : ConfigSpace (Sym2 (Site 2))) (x y u v : Site 2)
    (hxu : Connected 2 (removeSite 0 ω) x u) (hvy : Connected 2 (removeSite 0 ω) y v)
    (huv : IsOpenEdge 2 (removeSite 0 ω) u v) :
    cluster 2 (removeSite 0 ω) x = cluster 2 (removeSite 0 ω) y :=
  bc7_cut_clusters_eq_of_openEdge_between hxu hvy huv

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutClusterNoCrossing
