/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootParentWard

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootParentWard`

* non-vacuity: `bc43_RootWardRootParent` holds for the all-closed configuration with any rank and
  parent (`bc43_rootWardRootParent_of_noTrif`);
* `bc43_selfDownArm_of_cutGeometryFixed'_rootParent` in conditional form, composed with the
  self-down-arm count `bc36_Tcount_le_boundary_of_selfDownArm`;
* `bc43_rootWardRootParent_of_rootWardAvoidingWalk` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootParentWard

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

variable {d : ℕ}

/-- In the all-closed configuration every open cluster is a single site. -/
theorem cluster_closed (x : Site d) : cluster d (fun _ => false) x = {x} := by
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext a b
    simp
  ext y
  simp only [mem_cluster, Connected, hbot, SimpleGraph.reachable_bot, Set.mem_singleton_iff]
  exact eq_comm

/-- In the all-closed configuration no site is a trifurcation. -/
theorem not_isTrifurcation_closed (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, -, -, -, -, ⟨h, -, -⟩, -⟩
  rw [cluster_closed] at h
  exact h (Set.finite_singleton a₁)

-- The all-closed configuration satisfies the root-ward condition for every rank and parent.
example (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d) :
    bc43_RootWardRootParent (d := d) (fun _ => false) n rank par :=
  bc43_rootWardRootParent_of_noTrif _ n rank par fun x _ => not_isTrifurcation_closed x

-- Fixed cut geometry and the root-ward condition give the trifurcation count.
example (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hwalk : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc43_RootWardRootParent ω n rank par) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn
    (bc43_selfDownArm_of_cutGeometryFixed'_rootParent ω n hgeo hwalk)

-- Root-ward avoiding walks give the root-ward condition.
example (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ)
    (par : Site d → Site d) (h : bc41_RootWardAvoidingWalk ω n rank par) :
    bc43_RootWardRootParent ω n rank par :=
  bc43_rootWardRootParent_of_rootWardAvoidingWalk ω n rank par h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootParentWard
