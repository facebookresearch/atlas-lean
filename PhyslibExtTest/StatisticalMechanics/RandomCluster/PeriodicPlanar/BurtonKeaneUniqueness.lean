/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneUniqueness

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneUniqueness`

On the square lattice `square`:
* the all-open configuration is not in `threeDistinctInfiniteEvent` (its clusters coincide), nor is
  the all-closed one (its clusters are finite), so the event is a proper restriction;
* `numInfiniteClusters_top_subset_threeDistinct` applies to `square`;
* given a periodic plane embedding of `square` (conditional form),
  `freeBufferedInfiniteVolume_numInfiniteClusters_zero_or_one` applies at `p = 1/2`, `q = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneUniqueness

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

-- The all-open configuration has one cluster, so three distinct infinite clusters fail.
example (x : Fin 3 → Site 2) : allOpen ∉ square.threeDistinctInfiniteEvent x := by
  rintro ⟨-, hne⟩
  exact hne 0 1 (by decide) (by rw [cluster_allOpen, cluster_allOpen])

/-- In the all-closed configuration every cluster is a singleton. -/
theorem cluster_allClosed (x : Site 2) : square.cluster allClosed x = {x} := by
  ext y
  refine ⟨fun h => ?_, fun h => h ▸ square.self_mem_cluster allClosed x⟩
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj.2 (by simp [allClosed])

-- The all-closed configuration has only finite clusters.
example (x : Fin 3 → Site 2) : allClosed ∉ square.threeDistinctInfiniteEvent x := by
  rintro ⟨hinf, -⟩
  have h := hinf 0
  rw [cluster_allClosed] at h
  exact h (Set.finite_singleton _)

-- Infinitely many infinite clusters force three distinct infinite clusters.
example : {ω | square.numInfiniteClusters ω = ⊤} ⊆
    ⋃ x : Fin 3 → Site 2, square.threeDistinctInfiniteEvent x :=
  square.numInfiniteClusters_top_subset_threeDistinct

/-- The square lattice is connected. -/
theorem square_connected : square.graph.Connected :=
  ⟨fun x y => hypercubicLattice_two_reachable x y⟩

-- Given a plane embedding of `square`, the free limit at `p = 1/2`, `q = 1` has `0` or `1`
-- infinite clusters almost surely.
example (E : PeriodicPlaneEmbedding square) :
    ∃ k : ℕ∞,
      (square.freeBufferedInfiniteVolume (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
          (zero_lt_one.trans_le le_rfl) : Measure _)
          {ω | square.numInfiniteClusters ω = k} = 1 ∧ (k = 0 ∨ k = 1) :=
  E.freeBufferedInfiniteVolume_numInfiniteClusters_zero_or_one square_connected
    (by norm_num) (by norm_num) le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneUniqueness
