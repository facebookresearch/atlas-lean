/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GeneralTrifurcationPattern

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GeneralTrifurcationPattern`

* In `ℤ²` with every horizontal edge open (`tfc_lineConfig 0`), the rows through `(0, 0)`,
  `(0, 1)` and `(0, 2)` are three distinct infinite clusters meeting `B_2`, so
  `three_sites_finite_pattern_trifurcation` and
  `three_infinite_clusters_finite_pattern_canonical_trifurcation` produce a finite pattern with a
  trifurcation resp. a canonical trifurcation (instance).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GeneralTrifurcationPattern

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

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

/-- `(0, k)` lies in `B_2` for `|k| ≤ 2`. -/
theorem row_mem_box {k : ℤ} (hk : k.natAbs ≤ 2) : (Pi.single 1 k : Site 2) ∈ box 2 2 := by
  simpa using tfc_axis_mem_box (d := 2) 1 hk

-- Three rows give a finite pattern with a trifurcation.
example : ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch 2 2)) (hub : Site 2),
    IsTrifurcation 2 (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch 2 2) eta
      (tfc_lineConfig 0)) hub :=
  three_sites_finite_pattern_trifurcation _ 2 (Pi.single 1 0) (Pi.single 1 1) (Pi.single 1 2)
    (row_mem_box (by decide)) (row_mem_box (by decide)) (row_mem_box (by decide))
    (row_cluster_infinite 0) (row_cluster_infinite 1) (row_cluster_infinite 2)
    (row_cluster_ne (by decide)) (row_cluster_ne (by decide)) (row_cluster_ne (by decide))

-- Three rows give a finite pattern with a canonical trifurcation.
example : ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch 2 2)) (hub : Site 2),
    IsCanonicalTrifurcation 2 (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch 2 2) eta
      (tfc_lineConfig 0)) hub :=
  three_infinite_clusters_finite_pattern_canonical_trifurcation _ 2
    (fun i => Pi.single 1 (i : ℤ)) (fun i => row_mem_box (by fin_cases i <;> decide))
    (fun i => row_cluster_infinite _)
    (fun i j hij => row_cluster_ne (by fin_cases i <;> fin_cases j <;> simp_all))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GeneralTrifurcationPattern
