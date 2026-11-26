/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestNeighbourSpanningTree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestNeighbourSpanningTree`

* `bc71_deg3_of_three_neighbours` on the complete graph on `Fin 4` (instance).
* `bc71_degree_collapse_possible`: a contracted neighbour need not be a lattice neighbour.
* The first and third conjuncts of `bc71_status` applied in `ℤ` (instance and conditional form).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestNeighbourSpanningTree

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- In the complete graph on four vertices, vertex `0` has three distinct neighbours.
example : 3 ≤ (⊤ : SimpleGraph (Fin 4)).degree 0 :=
  bc71_deg3_of_three_neighbours (u := 0) (a₁ := 1) (a₂ := 2) (a₃ := 3) ⊤
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- The degree collapse witness.
example : ∃ (D : ℕ) (ω : ConfigSpace (Sym2 (Site D))) (L : ℕ) (y a b : Site D),
    b ∈ bc61_boxAround D L y ∧ (openSubgraph D ω).Adj b a ∧ bc67_GnIncident ω L y a ∧
    ¬ (hypercubicLattice D).Adj y a :=
  bc71_degree_collapse_possible

-- The summary's degree statement, applied to the complete graph on `Fin 4`.
example : 3 ≤ (⊤ : SimpleGraph (Fin 4)).degree 0 :=
  (bc71_status (d := 1)).1 ⊤ 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

-- The summary's counting statement, as a conditional.
example (ω : ConfigSpace (Sym2 (Site 1))) (L R : ℕ) (h : bc71_GnForestNeighbours ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 1 R :=
  (bc71_status (d := 1)).2.2 ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestNeighbourSpanningTree
