/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutClusterSurvives

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutClusterSurvives`

In the plane, with the all-closed configuration and the forced edge `(1,0)–(2,0)`:
* `bc9_removeSite_le_forceOpen` and `bc9_cutCluster_subset`;
* `bc9_origin_isolated_of_avoiding`: the origin stays isolated;
* `bc9_reaches_shares_cluster`: `(1,0)` and `(2,0)` share a cut cluster after forcing;
* `bc9_cut_survives` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutClusterSurvives

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

/-- `W` avoids the origin. -/
theorem W_avoid : ∀ e ∈ W, (0 : Site 2) ∉ e := fun e he => by
  rw [W, Finset.mem_singleton] at he
  exact he ▸ notMem10

-- Forcing only opens edges, so cut clusters grow.
example : removeSite (0 : Site 2) closed2 ≤ removeSite 0 (forceOpenFinset W closed2) ∧
    cluster 2 (removeSite 0 closed2) ![1, 0]
      ⊆ cluster 2 (removeSite 0 (forceOpenFinset W closed2)) ![1, 0] :=
  ⟨bc9_removeSite_le_forceOpen W closed2, bc9_cutCluster_subset W closed2 _⟩

-- The origin stays isolated when the forced edges avoid it.
example : ¬ (openSubgraph 2 (removeSite 0 (forceOpenFinset W closed2))).Adj 0 ![1, 0] :=
  bc9_origin_isolated_of_avoiding W closed2 W_avoid _

-- After forcing, `(1,0)` and `(2,0)` share a cut cluster.
example : cluster 2 (removeSite 0 (forceOpenFinset W closed2)) ![1, 0]
    = cluster 2 (removeSite 0 (forceOpenFinset W closed2)) ![2, 0] :=
  bc9_reaches_shares_cluster W closed2 (SimpleGraph.Adj.reachable (G := openSubgraph 2 _)
    ⟨adj10, by
      unfold removeSite forceOpenFinset
      simp only [notMem10, ↓reduceIte, W, Finset.mem_singleton]⟩)

-- Infinite cut clusters survive forcing edges avoiding the origin.
example (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2)
    (hinf : (cluster 2 (removeSite 0 ω) x).Infinite) :
    (cluster 2 (removeSite 0 (forceOpenFinset W ω)) x).Infinite :=
  (bc9_cut_survives W ω W_avoid hinf).1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutClusterSurvives
