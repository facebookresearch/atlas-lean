/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoverageShells

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoverageShells`

On the square lattice `square` (fundamental domain `{0}`):
* `canonicalConnectionShellPairs_card_le` gives at most `81 (n + 1)⁴` canonical pairs;
* at `n = 0` this is at most `81` pairs;
* `mem_canonicalConnectionShellPairs_dist` gives graph distance at least `n` for every canonical
  pair.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoverageShells

open MeasureTheory _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

/-- The all-open configuration. -/
def allOpen : ConfigSpace (Sym2 (Site 2)) := fun _ => true

/-- The all-closed configuration. -/
def allClosed : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- In the all-open configuration every cluster is the whole lattice. -/
theorem cluster_allOpen (x : Site 2) : square.cluster allOpen x = Set.univ := by
  have hopen : square.openSubgraph allOpen = hypercubicLattice 2 := by
    ext a b
    simp only [PeriodicGraph.openSubgraph_adj, allOpen, and_true]
    rfl
  ext y
  simp only [PeriodicGraph.cluster, hopen, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hypercubicLattice_two_reachable x y

/-- The cluster of every vertex in the all-open configuration is infinite. -/
theorem cluster_allOpen_infinite (x : Site 2) : (square.cluster allOpen x).Infinite := by
  rw [cluster_allOpen]; exact Set.infinite_univ

-- The canonical shell of `square` has at most `81 (n + 1)⁴` pairs.
example (n : ℕ) : (square.canonicalConnectionShellPairs n).card ≤ 81 * (n + 1) ^ 4 := by
  have h := square.canonicalConnectionShellPairs_card_le n
  have h1 : square.fundamentalDomain.card = 1 := Finset.card_singleton 0
  rwa [h1, one_pow, mul_one] at h

-- At radius `0` there are at most `81` pairs.
example : (square.canonicalConnectionShellPairs 0).card ≤ 81 := by
  have h := square.canonicalConnectionShellPairs_card_le 0
  have h1 : square.fundamentalDomain.card = 1 := Finset.card_singleton 0
  simpa [h1] using h

-- Canonical pairs are at graph distance at least `n`.
example (n : ℕ) (xy : square.BufferedVertex n × square.BufferedVertex n)
    (h : xy ∈ square.canonicalConnectionShellPairs n) :
    n ≤ (hypercubicLattice 2).dist xy.1.1 xy.2.1 :=
  square.mem_canonicalConnectionShellPairs_dist n xy h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoverageShells
