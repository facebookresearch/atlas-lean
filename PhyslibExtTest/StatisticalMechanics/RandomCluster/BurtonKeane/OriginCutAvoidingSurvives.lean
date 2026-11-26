/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutAvoidingSurvives

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutAvoidingSurvives`

* `bc4_adj_survives_origin_cut` in `ℤ` with every edge open: the edge `{1, 2}` stays open after
  removing the origin (instance).
* `bc4_avoiding_walk_survives_origin_cut` and `bc4_cluster_mono_of_avoiding` on the one-step walk
  `1 – 2` (instance).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutAvoidingSurvives

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The edge `{1, 2}` is open in the all-open configuration of `ℤ`. -/
theorem adj12 : (openSubgraph 1 fun _ => true).Adj (fun _ => 1) (fun _ => 2) := by simp

/-- A constant site `k ≠ 0` of `ℤ` is not the origin. -/
theorem const_ne {k : ℤ} (hk : k ≠ 0) : (fun _ => k : Site 1) ≠ 0 := fun h => hk (congrFun h 0)

-- The edge survives the origin cut.
example : (openSubgraph 1 (removeSite 0 fun _ => true)).Adj (fun _ => 1) (fun _ => 2) :=
  bc4_adj_survives_origin_cut _ (const_ne one_ne_zero) (const_ne two_ne_zero) adj12

/-- The origin is not on the walk `1 – 2`. -/
theorem zero_notMem : (0 : Site 1) ∉ (SimpleGraph.Walk.cons adj12 .nil).support := by
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false, not_or]
  exact ⟨(const_ne one_ne_zero).symm, (const_ne two_ne_zero).symm⟩

-- The walk survives, so `2` is in the cut cluster of `1`.
example : Connected 1 (removeSite 0 fun _ => true) (fun _ => 1) (fun _ => 2) ∧
    (fun _ => 2) ∈ cluster 1 (removeSite 0 fun _ => true) (fun _ => 1) :=
  ⟨bc4_avoiding_walk_survives_origin_cut _ _ zero_notMem,
    bc4_cluster_mono_of_avoiding _ _ zero_notMem⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutAvoidingSurvives
