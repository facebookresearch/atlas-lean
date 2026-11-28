/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound`

* In the all-closed configuration of `ℤ` no site is a trifurcation, so
  `daec_forestLeafInjection_of_subsingleton` gives the certificate `daec_ForestLeafInjection` and
  `daec_Tcount_le_boundary_of_forestLeafInjection` gives the counting bound (non-vacuity).
* The certificate is equivalent to `tfc_DistinctArmEnds`
  (`daec_forestLeafInjection_iff_distinctArmEnds`).
* The certificate cannot hold for every configuration: composing the counting bound with
  `tfc_not_forall_Tcount_le_boundary` refutes the configuration-wide form (refutation).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound

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

/-- The leaf-injection certificate holds in the all-closed configuration. -/
theorem closed_forestLeafInjection (d n : ℕ) (hn : 1 ≤ n) :
    daec_ForestLeafInjection (d := d) (fun _ => false) n :=
  daec_forestLeafInjection_of_subsingleton _ n hn fun x _ _ hx => absurd hx
    (not_isTrifurcation_closed x)

-- The counting bound applied to the all-closed configuration in `ℤ²`.
example : Tcount 2 (fun _ => false) 3 ≤ boxSV_boundaryCard 2 3 :=
  daec_Tcount_le_boundary_of_forestLeafInjection _ 3 (closed_forestLeafInjection 2 3 (by norm_num))

-- The certificate is literally `tfc_DistinctArmEnds`.
example : tfc_DistinctArmEnds (d := 1) (fun _ => false) 1 :=
  (daec_forestLeafInjection_iff_distinctArmEnds _ 1).mp (closed_forestLeafInjection 1 1 le_rfl)

-- No configuration-wide leaf injection exists in `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → daec_ForestLeafInjection ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary le_rfl fun ω n hn =>
    daec_Tcount_le_boundary_of_forestLeafInjection ω n (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound
