/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutDistinctWitnesses

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutDistinctWitnesses`

* `bc3_twoArms_cutInfinite` on the three rows through `(0, 0)`, `(0, 1)`, `(0, 2)` of `ℤ²` with
  every horizontal edge open (instance).
* `bc3_OriginCutLeavesInfinite` holds in the all-closed configuration, which has no infinite
  cluster (non-vacuity).
* `bc3_threeArms_cutInfinite_of_residue` and `bc3_distinctWitnessClusters` as conditional
  statements.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutDistinctWitnesses

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The row of height `k` in `ℤ²` meets the horizontal-line configuration in an infinite
cluster. -/
theorem row_cluster_infinite (k : ℤ) :
    (cluster 2 (tfc_lineConfig 0) (Pi.single 1 k)).Infinite := by
  simpa using tfc_line_cluster_infinite (0 : Fin 2) (Pi.single 1 k) 0

/-- Rows of different heights lie in different clusters of the horizontal-line configuration. -/
theorem row_cluster_ne {k k' : ℤ} (h : k ≠ k') :
    cluster 2 (tfc_lineConfig 0) (Pi.single 1 k) ≠
      cluster 2 (tfc_lineConfig 0) (Pi.single 1 k') := by
  intro hc
  have hm : Connected 2 (tfc_lineConfig 0) (Pi.single 1 k + Pi.single 0 0) (Pi.single 1 k') := by
    simpa [← hc] using self_mem_cluster (tfc_lineConfig (0 : Fin 2)) (Pi.single 1 k')
  obtain ⟨j, hj⟩ := tfc_line_on_line (0 : Fin 2) (Pi.single 1 k) hm
  have := congrFun hj 1
  simp at this
  exact h this.symm

-- Two of the three rows stay infinite after removing the origin.
example : ((cluster 2 (removeSite 0 (tfc_lineConfig 0)) (Pi.single 1 0)).Infinite ∧
      (cluster 2 (removeSite 0 (tfc_lineConfig 0)) (Pi.single 1 1)).Infinite) ∨
    ((cluster 2 (removeSite 0 (tfc_lineConfig 0)) (Pi.single 1 0)).Infinite ∧
      (cluster 2 (removeSite 0 (tfc_lineConfig 0)) (Pi.single 1 2)).Infinite) ∨
    ((cluster 2 (removeSite 0 (tfc_lineConfig 0)) (Pi.single 1 1)).Infinite ∧
      (cluster 2 (removeSite 0 (tfc_lineConfig 0)) (Pi.single 1 2)).Infinite) :=
  bc3_twoArms_cutInfinite _ (row_cluster_infinite 0) (row_cluster_infinite 1)
    (row_cluster_infinite 2) (row_cluster_ne (by decide)) (row_cluster_ne (by decide))
    (row_cluster_ne (by decide))

/-- Every cluster of the all-closed configuration is finite. -/
theorem cluster_closed_finite {d : ℕ} (a : Site d) : (cluster d (fun _ => false) a).Finite := by
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  have hc : cluster d (fun _ => false) a = {a} := by
    ext y
    simp [cluster, Connected, hb, eq_comm]
  exact hc ▸ Set.finite_singleton a

-- The residue condition holds in the all-closed configuration.
example : bc3_OriginCutLeavesInfinite (d := 2) fun _ => false :=
  fun x hx _ => absurd (cluster_closed_finite x) hx

-- The residue gives three surviving witnesses.
example (ω : ConfigSpace (Sym2 (Site 2))) (hres : bc3_OriginCutLeavesInfinite ω) (x₁ x₂ x₃ : Site 2)
    (h1 : (cluster 2 ω x₁).Infinite) (h2 : (cluster 2 ω x₂).Infinite)
    (h3 : (cluster 2 ω x₃).Infinite) :
    ∃ x₁' x₂' x₃' : Site 2, x₁' ∈ cluster 2 ω x₁ ∧ x₂' ∈ cluster 2 ω x₂ ∧
      x₃' ∈ cluster 2 ω x₃ ∧ (cluster 2 (removeSite 0 ω) x₁').Infinite ∧
      (cluster 2 (removeSite 0 ω) x₂').Infinite ∧ (cluster 2 (removeSite 0 ω) x₃').Infinite :=
  bc3_threeArms_cutInfinite_of_residue ω hres h1 h2 h3

-- The residue on `threeMeetBox` gives distinct witness clusters.
example (n : ℕ) (h : ∀ ω ∈ threeMeetBox 2 n, bc3_OriginCutLeavesInfinite ω) :
    bc3_DistinctWitnessClusters 2 n :=
  bc3_distinctWitnessClusters n h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutDistinctWitnesses
