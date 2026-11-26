/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedColoredForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedColoredForest`

* non-vacuity: `rts_RootedColoredForest` holds for the all-closed configuration (no site is a
  trifurcation), via `rts_rootedColoredForest_of_noTrif`;
* `rts_Tcount_le_boundary_of_rootedColoredForest` applies to that witness;
* refutation: `rts_RootedColoredForest` cannot hold for every configuration and `n ≥ 1` when `d ≥ 1`
  (its counting bound contradicts `tfc_not_forall_Tcount_le_boundary`).
* `rts_rootedTreeArmSelection_of_rootedColoredForest` turns the witness into
  `bas_RootedTreeArmSelection`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootedColoredForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

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

/-- The all-closed configuration satisfies `rts_RootedColoredForest`. -/
theorem closed_cert (n : ℕ) : rts_RootedColoredForest (d := d) (fun _ => false) n :=
  rts_rootedColoredForest_of_noTrif _ n fun x _ => not_isTrifurcation_closed x

-- The counting bound applies to the witness.
example (n : ℕ) (hn : 1 ≤ n) : Tcount d (fun _ => false) n ≤ boxSV_boundaryCard d n :=
  rts_Tcount_le_boundary_of_rootedColoredForest _ n hn (closed_cert n)

-- No such certificate holds for every configuration in dimension `d ≥ 1`.
example (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → rts_RootedColoredForest ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    rts_Tcount_le_boundary_of_rootedColoredForest ω n hn (h ω n hn)

-- `rts_rootedTreeArmSelection_of_rootedColoredForest` transfers the witness.
example (n : ℕ) : bas_RootedTreeArmSelection (d := d) (fun _ => false) n :=
  rts_rootedTreeArmSelection_of_rootedColoredForest _ n (closed_cert n)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootedColoredForest
