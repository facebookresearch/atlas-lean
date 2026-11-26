/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeArmCover

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeArmCover`

* concrete instance: in the plus configuration `tac_plus` of `ℤ²` the origin is a trifurcation
  (`tac_origin_isTrifurcation`) and its four arms are separated (`tac_disconnected_of_ne_ray`);
* refutation: `tac_threeArmCover_false`, and hence `fcc_ThreeArmCover` fails for some configuration;
* non-vacuity: `fcc_ThreeArmCover` holds for the all-closed configuration
  (`fcc_threeArmCover_of_noTrif`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeArmCover

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

-- The origin of the plus configuration is a trifurcation.
example : IsTrifurcation 2 tac_plus (0 : Site 2) := tac_origin_isTrifurcation

-- The east and north arms are separated once the origin is removed.
example : ¬ Connected 2 (removeSite (0 : Site 2) tac_plus) ![1, 0] ![0, 1] :=
  tac_disconnected_of_ne_ray (by rw [tac_ray_east, tac_ray_north]; decide)

-- The plus configuration has no three-arm cover.
example : ¬ fcc_ThreeArmCover (d := 2) tac_plus 1 := tac_threeArmCover_false

-- So three-arm covers fail for some configuration of `ℤ²`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → fcc_ThreeArmCover ω n :=
  fun h => tac_threeArmCover_false (h _ 1 le_rfl)

-- The all-closed configuration has a three-arm cover.
example (n : ℕ) : fcc_ThreeArmCover (d := d) (fun _ => false) n :=
  fcc_threeArmCover_of_noTrif _ n fun x _ => not_isTrifurcation_closed x

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeArmCover
