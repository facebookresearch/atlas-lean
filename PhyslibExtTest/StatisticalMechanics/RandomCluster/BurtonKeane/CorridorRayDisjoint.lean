/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorRayDisjoint

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorRayDisjoint`

In the plane:
* `bc2_ray_disjoint_nonvacuous` at `d = 2`;
* `bc2_corridorEdges_disjoint` for the two axes;
* `bc2_origin_mem_corridorVerts_iff`: the origin is a corridor vertex for length `3`, not `0`;
* `bc2_rayCell_eq_iff_origin`: ray cells on different axes meet only at the origin.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorRayDisjoint

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- The disjointness statement is non-vacuous in the plane.
example : ∃ i j : Fin 2, i ≠ j ∧ (hrHD_rayPt i 1 : Site 2) ≠ 0 ∧ (hrHD_rayPt j 1 : Site 2) ≠ 0 ∧
    (hrHD_rayPt i 1 : Site 2) ≠ hrHD_rayPt j 1 ∧
    Disjoint (hrHD_corridorEdges i 1) (hrHD_corridorEdges j 1) ∧
    bc2_corridorVerts i 1 ∩ bc2_corridorVerts j 1 ⊆ {(0 : Site 2)} :=
  bc2_ray_disjoint_nonvacuous le_rfl

-- Corridors along the two axes have disjoint edges.
example : Disjoint (hrHD_corridorEdges (0 : Fin 2) 3) (hrHD_corridorEdges (1 : Fin 2) 4) :=
  bc2_corridorEdges_disjoint (by decide) 3 4

-- The origin is a vertex of the length-3 corridor but not of the empty one.
example : (0 : Site 2) ∈ bc2_corridorVerts (0 : Fin 2) 3 ∧
    (0 : Site 2) ∉ bc2_corridorVerts (0 : Fin 2) 0 :=
  ⟨(bc2_origin_mem_corridorVerts_iff 0 3).mpr (by norm_num),
    fun h => absurd ((bc2_origin_mem_corridorVerts_iff 0 0).mp h) (lt_irrefl 0)⟩

-- Ray cells on the two axes meet only at the origin.
example : (hrHD_rayPt (0 : Fin 2) 2 : Site 2) ≠ hrHD_rayPt 1 2 := fun h =>
  absurd ((bc2_rayCell_eq_iff_origin (by decide) 2 2).mp h).1 (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorRayDisjoint
