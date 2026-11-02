/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineArmTreeLeaf

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineArmTreeLeaf`

In the plane:
* `bfl_tree_le_lattice` for the empty subgraph;
* `bfl_fineTrif_iff_bc67_zero` for the all-closed configuration at the origin;
* the `Fin 4` obstruction clause of `bfl_status` (a spanning tree with a leaf off `B`);
* `bfl_fineCount_of_armSubforest` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FineArmTreeLeaf

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- Subgraphs of the open subgraph are lattice subgraphs.
example : (⊥ : SimpleGraph (Site 2)) ≤ hypercubicLattice 2 :=
  bfl_tree_le_lattice (ω := closed2) bot_le

-- Fine trifurcations are `Gn` trifurcations at scale zero.
example : bft_FineTrif closed2 0 ↔ bc67_IsGnTrifurcation closed2 0 0 :=
  bfl_fineTrif_iff_bc67_zero closed2 0

-- A spanning tree may have a leaf outside the boundary set.
example : ∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj)
    (B : Finset (Fin 4)), T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧
    ¬ (∀ v, T.degree v = 1 → v ∈ B) :=
  bfl_status.2.2.2.1

-- Arm-subforest data bound the fine count.
example (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ) (h : bau_ArmSubforestData ω 0 R) :
    bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R :=
  bfl_fineCount_of_armSubforest ω R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FineArmTreeLeaf
