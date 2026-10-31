/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmSubforestCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmSubforestCount`

* `bca_datum_implies_count` in conditional form;
* `bca_status`: its last component, the explicit star `bau_star` is a tree with a degree-3
  centre;
* `bca_status`: a subgraph of a tree is acyclic, applied to `⊥ ≤ bau_star`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmSubforestCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The subforest datum bounds the coarse count.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω L R h

-- The star witness recorded in the status lemma.
example : bau_star.IsTree ∧ bau_star.degree 0 = 3 :=
  ⟨bca_status.2.2.2.2.1, bca_status.2.2.2.2.2.2⟩

-- A subgraph of the star is acyclic.
example : (⊥ : SimpleGraph (Fin 4)).IsAcyclic :=
  bca_status.2.2.2.1 bca_status.2.2.2.2.1 bot_le

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmSubforestCount
