/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedArmDivergence

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedArmDivergence`

* non-vacuity: `bc29_BundledRootedDownArmForest` holds for the all-closed configuration (no site is
  a trifurcation), via `bc29_rootedDownArmForest_of_noTrif`;
* `bc29_Tcount_le_boundary_of_rootedDownArmForest` applies to that witness;
* refutation: `bc29_BundledRootedDownArmForest` cannot hold for every configuration and `n ≥ 1` when
  `d ≥ 1` (its counting bound contradicts `tfc_not_forall_Tcount_le_boundary`).
* `bc29_rootedArmDivergence_of_bundled` turns the witness into `rfp_RootedArmDivergence`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootedArmDivergence

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

/-- The all-closed configuration satisfies `bc29_BundledRootedDownArmForest`. -/
theorem closed_cert (n : ℕ) : bc29_BundledRootedDownArmForest (d := d) (fun _ => false) n :=
  bc29_rootedDownArmForest_of_noTrif _ n fun x _ => not_isTrifurcation_closed x

-- The counting bound applies to the witness.
example (n : ℕ) (hn : 1 ≤ n) : Tcount d (fun _ => false) n ≤ boxSV_boundaryCard d n :=
  bc29_Tcount_le_boundary_of_rootedDownArmForest _ n hn (closed_cert n)

-- No such certificate holds for every configuration in dimension `d ≥ 1`.
example (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc29_BundledRootedDownArmForest ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc29_Tcount_le_boundary_of_rootedDownArmForest ω n hn (h ω n hn)

-- `bc29_rootedArmDivergence_of_bundled` transfers the witness.
example (n : ℕ) : rfp_RootedArmDivergence (d := d) (fun _ => false) n :=
  bc29_rootedArmDivergence_of_bundled _ n (closed_cert n)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootedArmDivergence
