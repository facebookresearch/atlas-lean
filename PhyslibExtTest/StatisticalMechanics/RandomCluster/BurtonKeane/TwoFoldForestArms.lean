/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TwoFoldForestArms

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TwoFoldForestArms`

* refutation: `tfh_TwoFoldForestArms` fails for the all-closed configuration (its root cluster is
  finite), hence it cannot hold for every configuration and `n ≥ 1`;
* `tfh_twoFold_hall_root` on an explicit instance in `ℕ` (one trifurcation, root end `{0}`, arm ends
  `{1}` and `{2}`);
* `tfh_Tcount_le_boundary_of_twoFoldForestArms` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TwoFoldForestArms

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

/-- Removing sites from the all-closed configuration leaves it all-closed. -/
theorem removeSites_closed (T : Finset (Site d)) :
    removeSites T (fun _ => false) = fun _ => false := by
  funext e
  simp only [removeSites, ite_self]

/-- The all-closed configuration has no two-fold forest arms. -/
theorem not_cert_closed (n : ℕ) : ¬ tfh_TwoFoldForestArms (d := d) (fun _ => false) n := by
  rintro ⟨r, -, ⟨-, hr⟩, -⟩
  rw [removeSites_closed, cluster_closed] at hr
  exact hr (Set.finite_singleton r)

-- Two-fold forest arms cannot hold for every configuration.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfh_TwoFoldForestArms ω n :=
  fun h => not_cert_closed 1 (h _ 1 le_rfl)

-- The two-fold Hall selection on an explicit instance.
example : ∃ (r₀ : ℕ) (ℓ : ℕ → Fin 2 → ℕ), r₀ ∈ ({0} : Finset ℕ) ∧
    (∀ x ∈ ({5} : Finset ℕ), ∀ i : Fin 2, ℓ x i ∈ ({(i : ℕ) + 1} : Finset ℕ)) ∧
    (∀ x ∈ ({5} : Finset ℕ), ∀ i : Fin 2, ℓ x i ≠ r₀) ∧
    (∀ x ∈ ({5} : Finset ℕ), ∀ i : Fin 2, ∀ y ∈ ({5} : Finset ℕ), ∀ j : Fin 2,
      ℓ x i = ℓ y j → x = y ∧ i = j) :=
  tfh_twoFold_hall_root {5} {0} (fun _ i => {(i : ℕ) + 1}) (by simp) (by simp)
    (by simp) (by decide)

-- The counting bound in conditional form.
example (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) (h : tfh_TwoFoldForestArms ω n)
    (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfh_Tcount_le_boundary_of_twoFoldForestArms ω n hn h hbase

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TwoFoldForestArms
