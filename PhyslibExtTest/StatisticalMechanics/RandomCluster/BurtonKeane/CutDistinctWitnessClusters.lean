/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutDistinctWitnessClusters

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutDistinctWitnessClusters`

In the plane:
* `bc7_distinctWitnessClusters`: `bc7_DistinctWitnessClusters 2 n` holds, here at `n = 5`;
* `bc7_cutCluster_ne`: the distinct clusters of `(1,0)` and `(0,1)` in the all-closed
  configuration stay distinct after removing the origin.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutDistinctWitnessClusters

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

-- Distinct witness clusters exist for the radius-5 box.
example : bc7_DistinctWitnessClusters 2 5 :=
  bc7_distinctWitnessClusters 5

-- Distinct clusters give distinct cut clusters.
example : cluster 2 (removeSite 0 closed2) ![1, 0] ≠ cluster 2 (removeSite 0 closed2) ![0, 1] :=
  bc7_cutCluster_ne closed2 (SimpleGraph.Reachable.refl _) (SimpleGraph.Reachable.refl _)
    (closed_cluster_ne fun h => by simpa using congrFun h 0)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutDistinctWitnessClusters
