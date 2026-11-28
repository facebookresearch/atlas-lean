/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorConfinement

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorConfinement`

In the plane:
* `bcc_disjoint_sides_iff_clusters_distinct`: the all-closed configuration has disjoint closed
  sides around three distinct sites (their clusters are distinct singletons);
* `bcc_axisCorridor_corridorStep` along the axis-`0` corridor of length `3`;
* `bcc_disjointRouting_of_residue` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorConfinement

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Percolation.DisjointPaths

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

-- Three distinct sites of the all-closed configuration have disjoint closed sides.
example : ∃ S₁ S₂ S₃ : Set (Site 2),
    ((0 : Site 2) ∈ S₁ ∧ ![1, 0] ∈ S₂ ∧ ![0, 1] ∈ S₃) ∧
    ((∀ u v, u ∈ S₁ → (openSubgraph 2 closed2).Adj u v → v ∈ S₁) ∧
      (∀ u v, u ∈ S₂ → (openSubgraph 2 closed2).Adj u v → v ∈ S₂) ∧
      (∀ u v, u ∈ S₃ → (openSubgraph 2 closed2).Adj u v → v ∈ S₃)) ∧
    (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃) := by
  refine (bcc_disjoint_sides_iff_clusters_distinct closed2 _ _ _).mpr ⟨?_, ?_, ?_⟩ <;>
    refine closed_cluster_ne fun h => ?_
  · simpa using congrFun h 0
  · simpa using congrFun h 1
  · simpa using congrFun h 0

-- The axis-`0` corridor of length `3` is a chain of corridor steps.
example : Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges (0 : Fin 2) 3))
    (hrHD_rayPt 0 1) (hrHD_rayPt 0 ((3 : ℕ) : ℤ)) :=
  bcc_axisCorridor_corridorStep 0 3 (by norm_num)

-- The residue gives a disjoint corridor routing.
example (ω : ConfigSpace (Sym2 (Site 2))) (h : bcc_distinct_clusters_residue ω) :
    DisjointCorridorRouting ω :=
  bcc_disjointRouting_of_residue ω h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorConfinement
