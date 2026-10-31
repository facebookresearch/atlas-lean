/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif`

* non-vacuity: `daepf_PrivateArm` holds for the all-closed configuration (no site is a
  trifurcation), via `daepf_privateArm_of_noTrif`;
* `daepf_Tcount_le_boundary_of_privateArm` applies to that witness;
* refutation: `daepf_PrivateArm` cannot hold for every configuration and `n ≥ 1` when `d ≥ 1` (its
  counting bound contradicts `tfc_not_forall_Tcount_le_boundary`).
* `daepf_singleCutBranchSeparation_of_privateArm` turns the witness into
  `daep2_SingleCutBranchSeparation`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif

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

/-- The all-closed configuration satisfies `daepf_PrivateArm`. -/
theorem closed_cert (n : ℕ) : daepf_PrivateArm (d := d) (fun _ => false) n :=
  daepf_privateArm_of_noTrif _ n fun x _ => not_isTrifurcation_closed x

-- The counting bound applies to the witness.
example (n : ℕ) (hn : 1 ≤ n) : Tcount d (fun _ => false) n ≤ boxSV_boundaryCard d n :=
  daepf_Tcount_le_boundary_of_privateArm _ n hn (closed_cert n)

-- No such certificate holds for every configuration in dimension `d ≥ 1`.
example (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → daepf_PrivateArm ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    daepf_Tcount_le_boundary_of_privateArm ω n hn (h ω n hn)

-- `daepf_singleCutBranchSeparation_of_privateArm` transfers the witness.
example (n : ℕ) : daep2_SingleCutBranchSeparation (d := d) (fun _ => false) n :=
  daepf_singleCutBranchSeparation_of_privateArm _ n (closed_cert n)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif
