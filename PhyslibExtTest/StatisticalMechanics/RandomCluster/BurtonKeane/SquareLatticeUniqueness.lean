/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SquareLatticeUniqueness

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SquareLatticeUniqueness`

* the headline `bins_bk_unconditional` at `p = 1/2`: almost surely at most one infinite cluster in
  `ℤ²`;
* `bins_route` at `p = 1/2`;
* instance: `bins_corridors_of_same_side` gives corridors in `B_1` to the right-side sites `(1,
  -1)`, `(1, 0)`, `(1, 1)`;
* `bins_connected_of_walk_edges_open` on the trivial walk.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SquareLatticeUniqueness

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory
open scoped NNReal

-- Burton–Keane on `ℤ²` at `p = 1/2`: no two infinite clusters, at most one almost surely.
example : bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)
      (atLeastTwoInfinite 2) = 0 ∧
    bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)
      {omega | numInfiniteClusters 2 omega ≤ 1} = 1 :=
  ⟨(bins_bk_unconditional _ _ (by norm_num) (by norm_num)).2.1,
    (bins_bk_unconditional _ _ (by norm_num) (by norm_num)).2.2⟩

-- The route package holds at `p = 1/2`.
example : bins_Route (1 / 2) (by norm_num) := bins_route _ _

-- Corridors to three sites on the right side of `B_1`.
example : bcor_Corridors 1 ![1, -1] ![1, 0] ![1, 1] :=
  bins_corridors_of_same_side 1 le_rfl _ _ _ (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two]) (by decide) (by decide)
    (by decide) (Or.inl ⟨rfl, rfl, rfl⟩)

-- A walk with all edges open connects its ends (the trivial walk).
example (x : Site 2) : Connected 2 (fun _ => false) x x :=
  bins_connected_of_walk_edges_open SimpleGraph.Walk.nil _ (by simp)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SquareLatticeUniqueness
