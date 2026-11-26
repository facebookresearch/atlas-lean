/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiberForestSpanningTree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiberForestSpanningTree`

In the plane:
* `bc75_upperLines_openBoundaryEdge` at `R = 2`;
* `bc75_spanForest_acyclic` for the all-closed configuration on the one-site set `{0}`;
* `bc75_collapseFiber` is the identity on an empty fibre (`bc75_emptyFiber_collapse_id`);
* `bc75_fiber_count_of_gnTrifData` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FiberForestSpanningTree

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- The upper lines have an open boundary edge at radius `2`.
example : bc57_pt 0 ((2 : ℕ) : ℤ) ∈ vertexBoundary 2 2 ∧
    bc57_pt 1 ((2 : ℕ) : ℤ) ∈ vertexBoundary 2 2 ∧
    (openSubgraph 2 bc60_upperLines).Adj (bc57_pt 0 ((2 : ℕ) : ℤ)) (bc57_pt 1 ((2 : ℕ) : ℤ)) :=
  bc75_upperLines_openBoundaryEdge (by norm_num)

-- The fibre spanning forest is acyclic.
example : (bc75_spanForest closed2 1 1 (fun _ => 0) ({0} : Set (Site 2))).IsAcyclic :=
  bc75_spanForest_acyclic _ _ _ _ _

-- On an empty fibre the collapse map is the identity.
example (c : Fin 2 → Fin (2 * 1 + 1)) (h : bc73_fiber closed2 1 1 c = ∅) :
    bc75_collapseFiber closed2 1 1 c ![1, 0] = ![1, 0] :=
  bc75_emptyFiber_collapse_id _ _ _ c h _

-- Fibre data bound the fibre size.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1))
    (h : bc75_FiberGnTrifData ω L R c) : (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard 2 R :=
  bc75_fiber_count_of_gnTrifData ω L R c h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FiberForestSpanningTree
