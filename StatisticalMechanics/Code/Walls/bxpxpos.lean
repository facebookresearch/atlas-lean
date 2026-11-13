/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Walls.bmfmergefree
import Code.Percolation.AvoidingAttachment
import Code.Percolation.PrivateArmProve
import Code.Percolation.TrifurcationConstruction

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000







variable {d : ℕ}








theorem bxp_cluster_removeSite_eq (ω : ConfigSpace (Sym2 (Site d))) {b : Site d}
    (h0 : (0 : Site d) ∉ cluster d ω b) :
    cluster d (removeSite 0 ω) b = cluster d ω b := by
  apply Set.Subset.antisymm
  · exact cluster_mono (removeSite_le 0 ω) b
  · intro y hy
    have hcon : Connected d ω b y := mem_cluster.mp hy
    obtain ⟨p⟩ := hcon
    have hcl : cluster d ω b = cluster d ω y := cluster_eq_of_connected (mem_cluster.mp hy)
    have h0y : (0 : Site d) ∉ cluster d ω y := hcl ▸ h0
    have h0p : (0 : Site d) ∉ p.support :=
      ava_origin_notMem_support_of_notMem_cluster ω p h0y
    exact mem_cluster.mpr (pap_connected_removeSite_of_walk_avoid ω 0 p h0p)


theorem bxp_infinite_removeSite (ω : ConfigSpace (Sym2 (Site d))) {b : Site d}
    (h0 : (0 : Site d) ∉ cluster d ω b) (hinf : (cluster d ω b).Infinite) :
    (cluster d (removeSite 0 ω) b).Infinite := by
  rw [bxp_cluster_removeSite_eq ω h0]; exact hinf




theorem bxp_notConnected_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a b : Site d}
    (h : ¬ Connected d ω a b) : ¬ Connected d (removeSite 0 ω) a b :=
  fun hc => h (ava_connected_of_removeSite ω hc)










def bxp_Y : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω |
    ((0 : Site 2) ∉ cluster 2 ω bmf_b₁ ∧ (0 : Site 2) ∉ cluster 2 ω bmf_b₂ ∧
      (0 : Site 2) ∉ cluster 2 ω bmf_b₃) ∧
    ((cluster 2 ω bmf_b₁).Infinite ∧ (cluster 2 ω bmf_b₂).Infinite ∧
      (cluster 2 ω bmf_b₃).Infinite) ∧
    (¬ Connected 2 ω bmf_b₁ bmf_b₂ ∧ ¬ Connected 2 ω bmf_b₁ bmf_b₃ ∧
      ¬ Connected 2 ω bmf_b₂ bmf_b₃)}





theorem bxp_Y_subset_X : bxp_Y ⊆ bmf_X := by
  rintro ω ⟨⟨h01, h02, h03⟩, ⟨hi1, hi2, hi3⟩, ⟨hd12, hd13, hd23⟩⟩
  exact ⟨⟨bxp_infinite_removeSite ω h01 hi1, bxp_infinite_removeSite ω h02 hi2,
      bxp_infinite_removeSite ω h03 hi3⟩,
    bxp_notConnected_removeSite ω hd12, bxp_notConnected_removeSite ω hd13,
    bxp_notConnected_removeSite ω hd23⟩








theorem bxp_hXpos_of_fullPos (p : ℝ≥0) (hp1 : p ≤ 1)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bxp_Y) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X :=
  lt_of_lt_of_le hpos (measure_mono bxp_Y_subset_X)















def bxp_tripleEvent (d n : ℕ) (x y z : Site d) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | numInfiniteClusters d ω = ⊤ ∧ x ∈ box d n ∧ y ∈ box d n ∧ z ∈ box d n ∧
    (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧ (cluster d ω z).Infinite ∧
    cluster d ω x ≠ cluster d ω y ∧ cluster d ω x ≠ cluster d ω z ∧
    cluster d ω y ≠ cluster d ω z}



theorem bxp_threeMeetBox_subset_iUnion (d n : ℕ) :
    threeMeetBox d n ⊆ ⋃ x, ⋃ y, ⋃ z, bxp_tripleEvent d n x y z := by
  intro ω hω
  obtain ⟨htop, x, y, z, hx, hy, hz, hix, hiy, hiz, h12, h13, h23⟩ := hω
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨z,
    htop, hx, hy, hz, hix, hiy, hiz, h12, h13, h23⟩⟩⟩





theorem bxp_exists_triple_pos (p : ℝ≥0) (hp1 : p ≤ 1)
    (htop : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      {ω | numInfiniteClusters d ω = ⊤}) :
    ∃ (n : ℕ) (x y z : Site d),
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bxp_tripleEvent d n x y z) := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos μ htop
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ x, ⋃ y, ⋃ z, bxp_tripleEvent d n x y z) = 0 := by
    refine measure_iUnion_null fun x => measure_iUnion_null fun y =>
      measure_iUnion_null fun z => ?_
    exact hcon n x y z
  have h0 : μ (threeMeetBox d n) = 0 :=
    le_antisymm ((measure_mono (bxp_threeMeetBox_subset_iUnion d n)).trans_eq hu) bot_le
  exact absurd h0 (ne_of_gt hn)

end StatMech.Walls
