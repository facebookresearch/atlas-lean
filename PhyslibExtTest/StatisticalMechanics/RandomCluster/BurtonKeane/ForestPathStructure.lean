/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPathStructure

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPathStructure`

* In the all-closed configuration of `ℤ²` there are no trifurcations, so `fps_TwoSidedPrivateFar`
  holds and `fps_Tcount_le_boundary_of_twoSidedPrivateFar` gives the counting bound
  (non-vacuity).
* `fps_pairwiseCutSeparation_of_twoSidedPrivateFar` gives the pairwise cut separation there.
* The certificate cannot hold for every configuration of `ℤ` (refutation through
  `tfc_not_forall_Tcount_le_boundary`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPathStructure

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

/-- In the all-closed configuration every cluster is a single site, so no site is a
trifurcation. -/
theorem not_isTrifurcation_closed {d : ℕ} (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a, -, -, -, -, ⟨h, -, -⟩, -⟩
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  have hc : cluster d (fun _ => false) a = {a} := by
    ext y
    simp [cluster, Connected, hb, eq_comm]
  exact h (hc ▸ Set.finite_singleton a)

/-- The two-sided private-arm certificate holds in the all-closed configuration. -/
theorem closed_twoSidedPrivateFar (d n : ℕ) :
    fps_TwoSidedPrivateFar (d := d) (fun _ => false) n :=
  ⟨id, fun x _ hx => absurd hx (not_isTrifurcation_closed x),
    fun x _ hx => absurd hx (not_isTrifurcation_closed x)⟩

-- The counting bound in the all-closed configuration of `ℤ²`.
example : Tcount 2 (fun _ => false) 2 ≤ boxSV_boundaryCard 2 2 :=
  fps_Tcount_le_boundary_of_twoSidedPrivateFar _ 2 (by norm_num) (closed_twoSidedPrivateFar 2 2)

-- Pairwise cut separation in the all-closed configuration.
example : fac_PairwiseCutSeparation (d := 2) (fun _ => false) 2 :=
  fps_pairwiseCutSeparation_of_twoSidedPrivateFar _ 2 (closed_twoSidedPrivateFar 2 2)

-- No configuration-wide two-sided private-arm certificate exists in `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → fps_TwoSidedPrivateFar ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary le_rfl fun ω n hn =>
    fps_Tcount_le_boundary_of_twoSidedPrivateFar ω n hn (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPathStructure
