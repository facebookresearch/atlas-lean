/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Walls.bc4_core

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}

















theorem bc7_cutCluster_ne (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₁' x₂' : Site d}
    (hx₁' : x₁' ∈ cluster d ω x₁) (hx₂' : x₂' ∈ cluster d ω x₂)
    (hne : cluster d ω x₁ ≠ cluster d ω x₂) :
    cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' := by
  intro hcut
  
  have hmem : x₂' ∈ cluster d (removeSite 0 ω) x₁' := by
    rw [hcut]; exact self_mem_cluster _ _
  
  have hbase : x₂' ∈ cluster d ω x₁' := ctc2_cluster_removeSite_subset 0 x₁' ω hmem
  
  have e1 : cluster d ω x₁ = cluster d ω x₁' :=
    cluster_eq_of_connected (mem_cluster.mp hx₁')
  have e2 : cluster d ω x₂ = cluster d ω x₂' :=
    cluster_eq_of_connected (mem_cluster.mp hx₂')
  have e12 : cluster d ω x₁' = cluster d ω x₂' :=
    cluster_eq_of_connected (mem_cluster.mp hbase)
  exact hne (e1.trans (e12.trans e2.symm))














theorem bc7_threeArms_cutInfinite_distinct (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₃ : Site d}
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite)
    (hd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
    ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧
      x₃' ∈ cluster d ω x₃ ∧
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite ∧
      cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧
      cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧
      cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃' := by
  obtain ⟨x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃⟩ :=
    bc4c_threeArms_cutInfinite ω hi1 hi2 hi3
  exact ⟨x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃,
    bc7_cutCluster_ne ω hx₁' hx₂' hd12,
    bc7_cutCluster_ne ω hx₁' hx₃' hd13,
    bc7_cutCluster_ne ω hx₂' hx₃' hd23⟩












def bc7_DistinctWitnessClusters (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧
      (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧
      cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃ ∧
      ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧
        x₃' ∈ cluster d ω x₃ ∧
        (cluster d (removeSite 0 ω) x₁').Infinite ∧
        (cluster d (removeSite 0 ω) x₂').Infinite ∧
        (cluster d (removeSite 0 ω) x₃').Infinite ∧
        cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧
        cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧
        cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃'










theorem bc7_distinctWitnessClusters (n : ℕ) : bc7_DistinctWitnessClusters d n := by
  intro ω hω
  obtain ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23,
      x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃⟩ :=
    bc4c_distinctWitnessClusters n ω hω
  exact ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23,
    x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃,
    bc7_cutCluster_ne ω hx₁' hx₂' hd12,
    bc7_cutCluster_ne ω hx₁' hx₃' hd13,
    bc7_cutCluster_ne ω hx₂' hx₃' hd23⟩

end Walls

end StatMech
