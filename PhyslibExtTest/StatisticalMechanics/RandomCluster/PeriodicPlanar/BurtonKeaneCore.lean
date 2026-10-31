/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneCore

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneCore`

On the square lattice `square` (periodic graph on `ℤ²`):
* the all-closed configuration has `numInfiniteClusters = 0` (every cluster is a singleton);
* the all-open configuration has a unique infinite cluster, so
  `numInfiniteClusters_eq_one_iff_hasUnique` gives `numInfiniteClusters = 1`;
* the Dirac mass at the all-open configuration is ergodic (`IsErgodic` is non-vacuous), and
  `numInfiniteClusters_ae_const` applies to it;
* `measurable_numInfiniteClusters` applies to `square`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneCore

open MeasureTheory _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

/-- The all-open configuration. -/
def allOpen : ConfigSpace (Sym2 (Site 2)) := fun _ => true

/-- The all-closed configuration. -/
def allClosed : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- In the all-closed configuration every cluster is a singleton. -/
theorem cluster_allClosed (x : Site 2) : square.cluster allClosed x = {x} := by
  ext y
  refine ⟨fun h => ?_, fun h => h ▸ square.self_mem_cluster allClosed x⟩
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj.2 (by simp [allClosed])

/-- In the all-open configuration every cluster is the whole lattice. -/
theorem cluster_allOpen (x : Site 2) : square.cluster allOpen x = Set.univ := by
  have hopen : square.openSubgraph allOpen = hypercubicLattice 2 := by
    ext a b
    simp only [PeriodicGraph.openSubgraph_adj, allOpen, and_true]
    rfl
  ext y
  simp only [PeriodicGraph.cluster, hopen, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hypercubicLattice_two_reachable x y

-- The all-closed configuration has no infinite cluster.
example : square.numInfiniteClusters allClosed = 0 := by
  rw [PeriodicGraph.numInfiniteClusters, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro C ⟨hC, x, rfl⟩
  rw [cluster_allClosed] at hC
  exact hC (Set.finite_singleton x)

/-- The all-open configuration has a unique infinite cluster. -/
theorem hasUnique_allOpen : square.HasUniqueInfiniteCluster allOpen := by
  refine ⟨⟨0, ?_⟩, fun x y _ _ => ?_⟩
  · rw [cluster_allOpen]; exact Set.infinite_univ
  · have hy : y ∈ square.cluster allOpen x := by rw [cluster_allOpen]; trivial
    exact hy

-- Hence the all-open configuration has exactly one infinite cluster.
example : square.numInfiniteClusters allOpen = 1 :=
  (square.numInfiniteClusters_eq_one_iff_hasUnique allOpen).2 hasUnique_allOpen

/-- The Dirac mass at the all-open configuration is ergodic. -/
theorem isErgodic_dirac_allOpen : square.IsErgodic (Measure.dirac allOpen) := by
  refine ⟨fun z => ?_, fun s hs _ => ?_⟩
  · refine ⟨square.measurable_configTranslate z, ?_⟩
    rw [Measure.map_dirac' (square.measurable_configTranslate z)]
    rfl
  · by_cases h : allOpen ∈ s
    · exact Or.inr (Measure.dirac_apply_of_mem h)
    · left
      rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem h]

-- The infinite-cluster count is almost surely constant under the ergodic Dirac mass.
example : ∃ k : ℕ∞, Measure.dirac allOpen {ω | square.numInfiniteClusters ω = k} = 1 :=
  square.numInfiniteClusters_ae_const _ isErgodic_dirac_allOpen

-- The count is measurable on the square lattice.
example : Measurable square.numInfiniteClusters := square.measurable_numInfiniteClusters

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneCore
