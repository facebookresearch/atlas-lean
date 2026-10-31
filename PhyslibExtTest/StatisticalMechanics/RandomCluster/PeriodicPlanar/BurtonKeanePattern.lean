/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeanePattern

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeanePattern`

On the square lattice `square` with `K = {0}`:
* `incidentEdgeFinset` contains the lattice edge `s(0, (1, 0))` touching `K`, and not the edge
  `s((2, 0), (3, 0))`, which misses `K`;
* `openExactlyPattern I O` opens an edge of `I` lying in `O`;
* `three_clusters_pattern_trifurcation` applies to the connected square lattice (conditional
  form: three distinct infinite clusters give a trifurcation pattern).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeanePattern

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

/-- The square-lattice edge from `0` to `(1, 0)`. -/
theorem square_adj_zero_e0 : square.graph.Adj 0 ![1, 0] := by
  change (hypercubicLattice 2).Adj 0 ![1, 0]
  simp [Fin.sum_univ_two]

/-- The square-lattice edge from `(2, 0)` to `(3, 0)`. -/
theorem square_adj_two_three : square.graph.Adj ![2, 0] ![3, 0] := by
  change (hypercubicLattice 2).Adj ![2, 0] ![3, 0]
  simp [Fin.sum_univ_two]

-- An edge touching `K = {0}` is an incident edge of `K`.
example : s(0, ![1, 0]) ∈ square.incidentEdgeFinset {0} :=
  (square.mem_incidentEdgeFinset_mk {0} 0 ![1, 0]).2
    ⟨square_adj_zero_e0, Or.inl (Finset.mem_singleton_self 0)⟩

-- An edge missing `K = {0}` is not an incident edge of `K`.
example : s(![2, 0], ![3, 0]) ∉ square.incidentEdgeFinset {0} := by
  rw [square.mem_incidentEdgeFinset_mk]
  rintro ⟨-, h | h⟩ <;>
    exact absurd (congrFun (Finset.mem_singleton.mp h) 0) (by decide)

-- The pattern opening exactly `O` opens an edge of `I ∩ O`.
example : openExactlyPattern ({s(0, ![1, 0])} : Finset (Sym2 (Site 2))) {s(0, ![1, 0])}
    ⟨s(0, ![1, 0]), Finset.mem_singleton_self _⟩ = true := by
  simp [openExactlyPattern]

/-- The square lattice is connected. -/
theorem square_connected : square.graph.Connected :=
  ⟨fun x y => hypercubicLattice_two_reachable x y⟩

-- Three distinct infinite clusters on the square lattice yield a trifurcation pattern.
example (ω : ConfigSpace (Sym2 (Site 2))) (x : Fin 3 → Site 2)
    (hinf : ∀ i, (square.cluster ω (x i)).Infinite)
    (hcl : ∀ i j, i ≠ j → square.cluster ω (x i) ≠ square.cluster ω (x j)) :
    ∃ (I : Finset (Sym2 (Site 2))) (eta : ConfigSpace ↥I) (hub : Site 2),
      square.IsTrifurcation (_root_.StatMech.FK.setPattern I eta ω) hub :=
  square.three_clusters_pattern_trifurcation square_connected ω x hinf hcl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeanePattern
