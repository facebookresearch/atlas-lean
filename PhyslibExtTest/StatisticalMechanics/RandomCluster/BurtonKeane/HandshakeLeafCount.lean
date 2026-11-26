/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HandshakeLeafCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HandshakeLeafCount`

* `bof2_interiorLeaf_obstruction`: a spanning-tree leaf can be an interior vertex of the graph
  (instance, the explicit graphs `bof2_advG ⊇ bof2_advT`).
* `bof2_forest_handshake` applied to the tree of that witness (instance).
* `bof2_trifCount_le_boundary` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.HandshakeLeafCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- A tree leaf need not be a boundary vertex.
example : ∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj)
    (B : Finset (Fin 4)), T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧
    ¬ (∀ v, T.degree v = 1 → v ∈ B) :=
  bof2_interiorLeaf_obstruction

-- The handshake bound for the tree of the witness.
example : ∃ (T : SimpleGraph (Fin 4)) (_ : DecidableRel T.Adj), T.IsTree ∧
    (Finset.univ.filter (fun v => 3 ≤ T.degree v)).card ≤
      (Finset.univ.filter (fun v => T.degree v = 1)).card := by
  obtain ⟨_, T, _, _, _, _, hT, _⟩ := bof2_interiorLeaf_obstruction
  exact ⟨T, _, hT, bof2_forest_handshake hT⟩

-- Separating vertices of `H` are at most the leaves of a spanning tree.
example {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι] {H T : SimpleGraph V}
    [DecidableRel T.Adj] (hTH : T ≤ H) (hT : T.IsTree) (f : ι → V) (hf : Function.Injective f)
    (hcut : ∀ i, ∃ a₁ a₂ a₃ : V, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧
      ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₂ ∧
      ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₃ ∧
      ¬ (bkg_deleteVertex H (f i)).Reachable a₂ a₃)
    (B : Finset V) (hleaf : ∀ v, T.degree v = 1 → v ∈ B) : Fintype.card ι ≤ B.card :=
  bof2_trifCount_le_boundary hTH hT f hf hcut B hleaf

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.HandshakeLeafCount
