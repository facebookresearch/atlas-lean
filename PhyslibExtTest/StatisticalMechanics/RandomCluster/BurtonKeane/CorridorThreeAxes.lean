/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorThreeAxes

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorThreeAxes`

* `bkm_dcc_three_axes` in `Site 3`;
* `bkm_corridorRay_inter_eq_origin` for the two planar axes;
* `origin_mem_corridorRay`, `rayPt_mem_corridorRay` and `bkm_corridorRay_disjoint_off_origin` at
  explicit points.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorThreeAxes

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- Three pairwise disjoint axis corridors exist in three dimensions.
example : ∃ j₁ j₂ j₃ : Fin 3, (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
    (corridorRay j₁ ∩ corridorRay j₂ = {(0 : Site 3)} ∧
      corridorRay j₁ ∩ corridorRay j₃ = {(0 : Site 3)} ∧
      corridorRay j₂ ∩ corridorRay j₃ = {(0 : Site 3)}) ∧
    (∀ L : ℕ, Disjoint (hrHD_corridorEdges j₁ L) (hrHD_corridorEdges j₂ L) ∧
      Disjoint (hrHD_corridorEdges j₁ L) (hrHD_corridorEdges j₃ L) ∧
      Disjoint (hrHD_corridorEdges j₂ L) (hrHD_corridorEdges j₃ L)) :=
  bkm_dcc_three_axes le_rfl

-- The two planar axes meet only at the origin.
example : corridorRay (0 : Fin 2) ∩ corridorRay 1 = {(0 : Site 2)} :=
  bkm_corridorRay_inter_eq_origin (by decide)

-- The origin and the ray point at `5` lie on the axis-0 line, which misses the axis-1 point `1`.
example : (0 : Site 2) ∈ corridorRay (0 : Fin 2) ∧ hrHD_rayPt (0 : Fin 2) 5 ∈ corridorRay 0 ∧
    ¬ (hrHD_rayPt (1 : Fin 2) 1 ∈ corridorRay 0 ∧ hrHD_rayPt (1 : Fin 2) 1 ∈ corridorRay 1) :=
  ⟨origin_mem_corridorRay 0, rayPt_mem_corridorRay 0 5,
    bkm_corridorRay_disjoint_off_origin (by decide)
      (fun h => by simpa [hrHD_rayPt] using congrFun h 1)⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorThreeAxes
