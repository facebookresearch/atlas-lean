/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTrifurcation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTrifurcation`

On the square lattice `square`:
* `removeVertex 0` closes the edge `s(0, (1, 0))` of the all-open configuration, and
  `removeVertex_le` compares it with the original;
* no vertex is a trifurcation of the all-closed configuration (`IsTrifurcation` needs open
  neighbours), while `measurableSet_isTrifurcation` applies to `square`;
* given a periodic plane embedding of `square` (conditional form), `trifurcation_measure_eq_zero`
  applies to the translation-invariant Dirac mass at the all-open configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTrifurcation

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

-- Removing `0` closes the edges at `0`.
example : removeVertex 0 allOpen s(0, ![1, 0]) = false := by
  simp [removeVertex]

-- Removing a vertex only closes edges.
example : removeVertex 0 allOpen ≤ allOpen := removeVertex_le 0 allOpen

-- The all-closed configuration has no trifurcation.
example (x : Site 2) : ¬ square.IsTrifurcation allClosed x := by
  rintro ⟨a1, -, -, h1, -⟩
  exact absurd h1.2 (by simp [allClosed])

-- The trifurcation event at `0` is measurable.
example : MeasurableSet {ω : ConfigSpace (Sym2 (Site 2)) | square.IsTrifurcation ω 0} :=
  square.measurableSet_isTrifurcation 0

/-- The Dirac mass at the all-open configuration is translation invariant. -/
theorem isTranslationInvariant_dirac_allOpen :
    square.IsTranslationInvariant (Measure.dirac allOpen) := fun z => by
  refine ⟨square.measurable_configTranslate z, ?_⟩
  rw [Measure.map_dirac' (square.measurable_configTranslate z)]
  rfl

-- Given a plane embedding of `square`, `0` is a.s. not a trifurcation of the Dirac mass.
example (E : PeriodicPlaneEmbedding square) :
    Measure.dirac allOpen {ω | square.IsTrifurcation ω 0} = 0 :=
  E.trifurcation_measure_eq_zero _ isTranslationInvariant_dirac_allOpen 0
    (Finset.mem_singleton_self 0)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTrifurcation
