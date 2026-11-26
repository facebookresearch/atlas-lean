/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrif

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrif`

In the plane:
* `bft_boxAround_zero`: the scale-zero box around a site is that site;
* `bft_fineTrif_iff` shows the all-closed configuration has no fine trifurcation (it would need an
  open edge at the hub);
* `bft_gnIncident_zero` and `bft_contractedLattice_zero` for the all-closed configuration;
* `bft_separation` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrif

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- The scale-zero box around `(1,2)` is a singleton.
example : bc61_boxAround 2 0 ![1, 2] = {![1, 2]} :=
  bft_boxAround_zero _

-- The all-closed configuration has no fine trifurcation.
example (x : Site 2) : ¬ bft_FineTrif closed2 x := fun h => by
  obtain ⟨_, _, _, ⟨h₁, -, -⟩, -⟩ := (bft_fineTrif_iff closed2 x).mp h
  exact absurd h₁.2 (by simp [closed2])

-- Scale-zero incidence is open adjacency; the scale-zero contraction deletes the hub.
example : (bc67_GnIncident closed2 0 0 ![1, 0] ↔ (openSubgraph 2 closed2).Adj 0 ![1, 0]) ∧
    bc67_contractedLattice closed2 0 0 = bkg_deleteVertex (openSubgraph 2 closed2) 0 :=
  ⟨bft_gnIncident_zero _ _ _, bft_contractedLattice_zero _ _⟩

-- A fine trifurcation has three separated neighbours.
example (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (h : bft_FineTrif ω x) :
    ∃ a₁ a₂ a₃ : Site 2, a₁ ≠ x ∧ a₂ ≠ x ∧ a₃ ≠ x ∧
      ¬ (bkg_deleteVertex (openSubgraph 2 ω) x).Reachable a₁ a₂ ∧
      ¬ (bkg_deleteVertex (openSubgraph 2 ω) x).Reachable a₁ a₃ ∧
      ¬ (bkg_deleteVertex (openSubgraph 2 ω) x).Reachable a₂ a₃ :=
  bft_separation ω h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrif
