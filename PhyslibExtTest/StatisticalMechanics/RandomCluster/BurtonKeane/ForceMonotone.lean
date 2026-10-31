/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForceMonotone

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForceMonotone`

In the plane, with the all-closed configuration and the forced edge `(1,0)–(2,0)`:
* `bc2_force_mono_base` and `bc2_force_mono_cut`;
* `bc2_cluster_force_mono`: the cluster of `(1,0)` grows, here to contain `(2,0)` after forcing;
* `bc2_clusterInfinite_force_mono_origin` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForceMonotone

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- `(1,0)` and `(2,0)` are lattice neighbours. -/
theorem adj10 : (hypercubicLattice 2).Adj ![1, 0] ![2, 0] := by
  simp [hypercubicLattice, NearestNeighbour, Fin.sum_univ_two]

/-- The edge `(1,0)–(2,0)` avoids the origin. -/
theorem notMem10 : (0 : Site 2) ∉ s(![1, 0], ![2, 0]) := by
  simp only [Sym2.mem_iff, not_or]
  constructor <;> intro h <;> simpa using congrFun h 0

/-- The forced edge set `{(1,0)–(2,0)}`. -/
def W : Finset (Sym2 (Site 2)) := {s(![1, 0], ![2, 0])}

-- Forcing only opens edges, also after removing a site.
example : closed2 ≤ forceOpenFinset W closed2 ∧
    removeSite ![5, 5] closed2 ≤ removeSite ![5, 5] (forceOpenFinset W closed2) :=
  ⟨bc2_force_mono_base _ _, bc2_force_mono_cut _ _ _⟩

-- After forcing, `(2,0)` joins the (enlarged) cluster of `(1,0)`.
example : cluster 2 closed2 ![1, 0] ⊆ cluster 2 (forceOpenFinset W closed2) ![1, 0] ∧
    (![2, 0] : Site 2) ∈ cluster 2 (forceOpenFinset W closed2) ![1, 0] :=
  ⟨bc2_cluster_force_mono _ _ _, SimpleGraph.Adj.reachable (G := openSubgraph 2 _)
    ⟨adj10, by simp [forceOpenFinset, W]⟩⟩

-- Infinite cut clusters stay infinite after forcing.
example (ω : ConfigSpace (Sym2 (Site 2))) (y : Site 2)
    (h : (cluster 2 (removeSite 0 ω) y).Infinite) :
    (cluster 2 (removeSite 0 (forceOpenFinset W ω)) y).Infinite :=
  bc2_clusterInfinite_force_mono_origin ω W h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForceMonotone
