/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarArmOrder

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarArmOrder`

* non-vacuity: `bc26_PrivateFarOrder` and `bkfl_CoherentArmSelector` hold for the all-closed
  configuration;
* `bc27_not_privateFarOrder_of_claw` and `bc27_not_coherentSelector_of_claw` used contrapositively:
  the all-closed configuration is not a claw;
* `bc27_not_privateFarOrder_of_claw` in conditional form: a claw has no private-far order.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarArmOrder

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

/-- The all-closed configuration has a private-far order. -/
theorem closed_order (n : ℕ) : bc26_PrivateFarOrder (d := d) (fun _ => false) n :=
  bc26_privateFarOrder_of_noTrif _ n fun x _ => not_isTrifurcation_closed x

-- It also has a coherent arm selector.
example (n : ℕ) : bkfl_CoherentArmSelector (d := d) (fun _ => false) n :=
  (bc26_privateFarOrder_iff_coherentSelector _ n).mp (closed_order n)

-- Contrapositively, the all-closed configuration is not a claw (two routes).
example (n : ℕ) : ¬ stac_ClawConfig (d := d) (fun _ => false) n :=
  fun h => bc27_not_privateFarOrder_of_claw _ n h (closed_order n)

-- The same through coherent arm selectors.
example (n : ℕ) : ¬ stac_ClawConfig (d := d) (fun _ => false) n :=
  fun h => bc27_not_coherentSelector_of_claw _ n h
    ((bc26_privateFarOrder_iff_coherentSelector _ n).mp (closed_order n))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarArmOrder
