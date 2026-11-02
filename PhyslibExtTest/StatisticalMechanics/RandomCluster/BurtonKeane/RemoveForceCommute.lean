/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RemoveForceCommute

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RemoveForceCommute`

* instance: forcing the edge `{0, y}` open in the all-closed configuration and then removing the
  origin gives back the all-closed configuration (`bc8_removeSite_forceOpen_comm`), so every cluster
  is a single site (`bc8_cluster_forceOpen_eq`);
* `bc8_connected_forceOpen_iff` on the same instance;
* `bc8_removeSite_forceOpen_comm_general` at an arbitrary site.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RemoveForceCommute

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

/-- The forced edge set `{{0, y}}` contains the origin in each edge. -/
theorem hF (y : Site d) : ∀ e ∈ ({s(0, y)} : Finset (Sym2 (Site d))), (0 : Site d) ∈ e := by
  intro e he
  rw [Finset.mem_singleton.mp he]
  exact Sym2.mem_mk_left _ _

/-- Removing a site from the all-closed configuration leaves it all-closed. -/
theorem removeSite_closed (x : Site d) : removeSite x (fun _ => false) = fun _ => false := by
  funext e
  simp only [removeSite, ite_self]

-- Forcing `{0, y}` and removing the origin is just removing the origin.
example (y : Site d) :
    removeSite (0 : Site d) (forceOpenFinset {s(0, y)} (fun _ => false)) = fun _ => false := by
  rw [bc8_removeSite_forceOpen_comm _ _ (hF y), removeSite_closed]

-- Clusters after removal ignore the forced edge: they are single sites.
example (y a : Site d) :
    cluster d (removeSite (0 : Site d) (forceOpenFinset {s(0, y)} (fun _ => false))) a = {a} := by
  rw [bc8_cluster_forceOpen_eq _ _ (hF y), removeSite_closed, cluster_closed]

-- Connectivity after removal ignores the forced edge.
example (y : Site d) (hy : y ≠ 0) :
    ¬ Connected d (removeSite (0 : Site d) (forceOpenFinset {s(0, y)} (fun _ => false))) 0 y := by
  rw [bc8_connected_forceOpen_iff _ _ (hF y), removeSite_closed, ← mem_cluster, cluster_closed]
  exact fun h => hy h

-- The general commutation at a site `x`.
example (x y : Site d) :
    removeSite x (forceOpenFinset {s(x, y)} (fun _ => false)) = fun _ => false := by
  rw [bc8_removeSite_forceOpen_comm_general x _ _ (by simp), removeSite_closed]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RemoveForceCommute
