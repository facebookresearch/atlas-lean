/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TwoSidedPrivateFar

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TwoSidedPrivateFar`

* non-vacuity: `fps_TwoSidedPrivateFar` holds for the all-closed configuration
  (`fps_twoSidedPrivateFar_of_noTrif`);
* `frc_not_twoSidedPrivateFar_of_claw` used contrapositively: the all-closed configuration is not a
  claw;
* `frc_uniform_twoSidedPrivateFar_false` and `frc_claw_excludes_twoSidedPrivateFar` in conditional
  form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TwoSidedPrivateFar

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

/-- The all-closed configuration has two-sided private far arms. -/
theorem closed_cert (n : ℕ) : fps_TwoSidedPrivateFar (d := d) (fun _ => false) n :=
  fps_twoSidedPrivateFar_of_noTrif _ n fun x _ => not_isTrifurcation_closed x

-- Hence it is not a claw configuration.
example (n : ℕ) : ¬ stac_ClawConfig (d := d) (fun _ => false) n :=
  fun h => frc_not_twoSidedPrivateFar_of_claw _ n h (closed_cert n)

-- A claw contradicts two-sided private far arms.
example (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hclaw : stac_ClawConfig ω n)
    (h : fps_TwoSidedPrivateFar ω n) : False :=
  frc_claw_excludes_twoSidedPrivateFar ω n hclaw h

-- A single claw refutes the uniform certificate.
example (hex : ∃ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n ∧ stac_ClawConfig ω n) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fps_TwoSidedPrivateFar ω n :=
  frc_uniform_twoSidedPrivateFar_false hex

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TwoSidedPrivateFar
