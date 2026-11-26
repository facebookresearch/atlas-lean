/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CylinderArmPattern

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CylinderArmPattern`

For Bernoulli(1/2) bond percolation on the plane:
* `bcl_cylinder_measurable` and `bcl_cylinder_dependsOn` for the cylinder on one edge;
* `bcl_bk_atLeastTwo` and `bcl_hroute_of_residue` in conditional form (under `bcl_ArmResidue`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CylinderArmPattern

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The one-edge index set `{(1,0)–(2,0)}`. -/
def I1 : Finset (Sym2 (Site 2)) := {s(![1, 0], ![2, 0])}

-- The cylinder "the edge is open" is measurable and depends only on that edge.
example : MeasurableSet ((cylinder I1 ({fun _ => true} : Set (ConfigSpace ↥I1))) :
    Set (ConfigSpace (Sym2 (Site 2)))) ∧
    DependsOn (cylinder I1 ({fun _ => true} : Set (ConfigSpace ↥I1)))
      (↑I1 : Set (Sym2 (Site 2))) :=
  ⟨bcl_cylinder_measurable I1 _, bcl_cylinder_dependsOn I1 _⟩

-- The arm residue excludes two infinite clusters for Bernoulli(1/2).
example (hres : bcl_ArmResidue (1 / 2) (by norm_num)) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num) (atLeastTwoInfinite 2)
      = 0 :=
  bcl_bk_atLeastTwo _ _ (by norm_num) (by norm_num) hres

-- The arm residue gives positive-probability neighbour precursors.
example (hres : bcl_ArmResidue (1 / 2) (by norm_num)) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)
      (threeMeetBox 2 n)) :
    ∃ a₁ a₂ a₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)
      (NeighborTrifPrecursor 2 a₁ a₂ a₃) :=
  bcl_hroute_of_residue _ _ (by norm_num) (by norm_num) hres n hpos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CylinderArmPattern
