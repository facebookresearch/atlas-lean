/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OutwardArm

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OutwardArm`

* non-vacuity: `fld_OutwardArm` holds for the all-closed configuration (no trifurcations), via
  `fld_outwardArm_of_noTrif`;
* `fld_outwardArm_iff_forestPeel` turns that witness into `bkfl_ForestPeel`;
* `fld_Tcount_le_boundary_of_outwardArm` applies to the witness;
* refutation: `fld_OutwardArm` cannot hold for every configuration and `n ≥ 1` when `d ≥ 1`
  (counting bound + `tfc_not_forall_Tcount_le_boundary`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OutwardArm

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

/-- The all-closed configuration has outward arms. -/
theorem outwardArm_closed (n : ℕ) : fld_OutwardArm (d := d) (fun _ => false) n :=
  fld_outwardArm_of_noTrif _ n fun x _ => not_isTrifurcation_closed x

-- Outward arms are forest peeling: the witness transfers.
example (n : ℕ) : bkfl_ForestPeel (d := d) (fun _ => false) n :=
  (fld_outwardArm_iff_forestPeel _ n).mp (outwardArm_closed n)

-- The counting bound applies to the witness.
example (n : ℕ) (hn : 1 ≤ n) : Tcount d (fun _ => false) n ≤ boxSV_boundaryCard d n :=
  fld_Tcount_le_boundary_of_outwardArm _ n hn (outwardArm_closed n)

-- No outward-arm certificate holds for every configuration in dimension `d ≥ 1`.
example (hd : 1 ≤ d) : ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fld_OutwardArm ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    fld_Tcount_le_boundary_of_outwardArm ω n hn (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OutwardArm
