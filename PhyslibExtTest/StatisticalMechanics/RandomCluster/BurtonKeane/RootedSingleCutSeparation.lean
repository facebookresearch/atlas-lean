/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSingleCutSeparation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSingleCutSeparation`

* non-vacuity: `fcc_ThreeArmCover`, `fcc_RootedPrivateArm` and `fcc_RootedSingleCutSeparation` hold
  for the all-closed configuration (no trifurcation);
* `fcc_rootedSpanningForest_iff` assembles the cover and the single-cut separation into
  `stt_RootedSpanningForest`, and `fcc_Tcount_le_boundary_of_armsPrivate` applies;
* refutation: rooted private arms with three-arm covers cannot hold for every configuration and `n ≥
  1` when `d ≥ 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSingleCutSeparation

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

/-- The all-closed configuration has a three-arm cover. -/
theorem closed_cover (n : ℕ) : fcc_ThreeArmCover (d := d) (fun _ => false) n :=
  fcc_threeArmCover_of_noTrif _ n fun x _ => not_isTrifurcation_closed x

/-- The all-closed configuration has rooted private arms. -/
theorem closed_priv (n : ℕ) : fcc_RootedPrivateArm (d := d) (fun _ => false) n :=
  fcc_rootedPrivateArm_of_noTrif _ n fun x _ => not_isTrifurcation_closed x

-- The characterisation assembles a rooted spanning forest.
example (n : ℕ) : stt_RootedSpanningForest (d := d) (fun _ => false) n :=
  (fcc_rootedSpanningForest_iff _ n).mpr ⟨closed_cover n,
    fcc_rootedSingleCutSeparation_of_noTrif _ n fun x _ => not_isTrifurcation_closed x⟩

-- The counting bound applies.
example (n : ℕ) (hn : 1 ≤ n) : Tcount d (fun _ => false) n ≤ boxSV_boundaryCard d n :=
  fcc_Tcount_le_boundary_of_armsPrivate _ n hn (closed_cover n) (closed_priv n)

-- No such pair of certificates holds for every configuration in dimension `d ≥ 1`.
example (hd : 1 ≤ d) : ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
    fcc_ThreeArmCover ω n ∧ fcc_RootedPrivateArm ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    fcc_Tcount_le_boundary_of_armsPrivate ω n hn (h ω n hn).1 (h ω n hn).2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSingleCutSeparation
