/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount`

* `cfc_T_acyclic` and `cfc_T_open` for the all-open configuration of `ℤ²`;
* `cfc_Tcount_le_boundary_of_no_trif` for the all-closed configuration;
* `cfc_Tcount_le_boundary_of_canonical` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

/-- The all-closed configuration has no trifurcation. -/
theorem noTrif_closed {d : ℕ} (x : Site d) : ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, a₂, -, ⟨h₁₂, -, -⟩, ⟨c₁, c₂, -⟩, -⟩
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext u v; simp
  unfold Connected at c₁ c₂
  rw [hbot, SimpleGraph.reachable_bot] at c₁ c₂
  exact h₁₂ (c₁.symm.trans c₂)

-- The canonical forest is acyclic (all-open configuration).
example : (cfc_T (d := 2) (fun _ => true) 2).IsAcyclic := cfc_T_acyclic _ 2

-- Its edges are open.
example (u v : Site 2) (h : (cfc_T (d := 2) (fun _ => true) 2).Adj u v) :
    (openSubgraph 2 (fun _ => true)).Adj u v :=
  cfc_T_open _ 2 u v h

-- The count bound for the all-closed configuration.
example : Tcount 2 (fun _ => false) 3 ≤ boxSV_boundaryCard 2 3 :=
  cfc_Tcount_le_boundary_of_no_trif _ 3 fun x _ => noTrif_closed x

-- The canonical count bound, by type.
example := @cfc_Tcount_le_boundary_of_canonical

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount
