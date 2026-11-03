/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicArmSubforest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicArmSubforest`

* `bau_star_witness`: the explicit star `bau_star` on `Fin 4` is a tree with a degree-3 centre;
* `bau_sub_witness`: `bau_sub` is a proper acyclic subgraph of the star;
* `bau_armUnion_acyclic_of_spanningTree` applied with `H = T = bau_star` and `G = bau_sub`;
* `bau_bk_of_subforestData` in its conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicArmSubforest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls
open scoped NNReal

-- The star is a tree whose centre has degree three.
example : bau_star.IsTree ∧ bau_star.degree 0 = 3 :=
  ⟨bau_star_witness.1, bau_star_witness.2.2.1⟩

-- The subgraph `bau_sub` is a proper subgraph of the star.
example : bau_sub ≤ bau_star ∧ bau_sub ≠ bau_star :=
  ⟨bau_sub_witness.1, bau_sub_witness.2.1⟩

-- A subgraph of a spanning tree of a connected graph is acyclic (concrete instance).
example : bau_sub.IsAcyclic :=
  bau_armUnion_acyclic_of_spanningTree bau_star_witness.1.connected bau_star le_rfl
    bau_star_witness.1 bau_sub_witness.1

-- The subforest datum everywhere gives the Burton–Keane conclusion.
example (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bau_bk_of_subforestData p hp1 hp0 hdata

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicArmSubforest
