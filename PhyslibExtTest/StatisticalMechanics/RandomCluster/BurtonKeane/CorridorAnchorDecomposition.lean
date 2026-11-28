/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorAnchorDecomposition

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorAnchorDecomposition`

In the plane:
* `bc3_origin_mem_anchorSites_corridor` and `bc3_rayPt_mem_anchorSites_corridor` for the axis-`0`
  corridor;
* `bc3_anchorSites_corridorUnion_nonempty` and `bc3_anchor_cover_index_finite`;
* `bc3_cluster_covered_by_anchors` for the all-closed configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorAnchorDecomposition

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- The origin and the ray point at distance `2` are anchors of the length-4 axis-0 corridor.
example : (0 : Site 2) ∈ anchorSites (hrHD_corridorEdges (0 : Fin 2) (3 + 1)) ∧
    hrHD_rayPt (0 : Fin 2) (((1 : ℕ) : ℤ) + 1) ∈ anchorSites (hrHD_corridorEdges (0 : Fin 2) 3) :=
  ⟨bc3_origin_mem_anchorSites_corridor 0 3, bc3_rayPt_mem_anchorSites_corridor 0 3 1 (by norm_num)⟩

-- The anchors of a three-corridor union are nonempty, and the cover index set is finite.
example : (anchorSites (bc3_corridorUnion (0 : Fin 2) 1 0 2 2 2)).Nonempty ∧
    (insert (0 : Site 2) (anchorSites (bc3_corridorUnion (0 : Fin 2) 1 0 2 2 2))).Finite :=
  ⟨bc3_anchorSites_corridorUnion_nonempty _ _ _ _ _ _, bc3_anchor_cover_index_finite _ _⟩

-- Forced clusters of the all-closed configuration are covered by anchor clusters.
example (G : Finset (Sym2 (Site 2))) (x : Site 2) :
    cluster 2 (forceOpenFinset G closed2) x ⊆ ⋃ a ∈ insert x (anchorSites G), cluster 2 closed2 a :=
  bc3_cluster_covered_by_anchors G closed2 x

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorAnchorDecomposition
