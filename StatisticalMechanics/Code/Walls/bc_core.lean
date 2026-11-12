/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Percolation.LatticeMengerAttach
import Code.Percolation.LatticeMengerClose
import Code.Percolation.ClusterRunsAxisFE
import Code.Walls.bc_cutmeetsaxis
import Code.Walls.bc_mouthcorridor
import Code.Walls.bc_raydisjoint
import Code.Walls.bc_forcemono

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}




















def bc_NearAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) : Prop :=
  hrHD_rayPt j 1 ∈ cluster d ω x ∧
    Connected d (removeSite 0 ω) (hrHD_rayPt j 1) x ∧
    (cluster d (removeSite 0 ω) x).Infinite







theorem bc_nearAxis_of_axisAssignment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_AxisAssignment ω x j) : bc_NearAxis ω x j := by
  obtain ⟨L, _, hnear, hcut, hinf⟩ := h
  exact ⟨mem_cluster.mpr hnear, hcut.symm, hinf⟩






















theorem bc_clusterReachesRay_of_nearAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc_NearAxis ω x j) : lma_ClusterReachesRay ω x j := by
  obtain ⟨hmem, hreach, hinf⟩ := h
  refine ⟨0, hmem, ?_, ?_, hinf⟩
  · intro e he; simp [lma_corridorEdges] at he
  · have he : ((0 : ℕ) : ℤ) + 1 = (1 : ℤ) := by norm_num
    rw [he]; exact hreach

















def bc_BoxNearAxis (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      ∃ j₁ j₂ j₃ : Fin d,
        bc_NearAxis ω x₁ j₁ ∧ bc_NearAxis ω x₂ j₂ ∧ bc_NearAxis ω x₃ j₃





theorem bc_boxReachesRay_of_boxNearAxis {n : ℕ} (h : bc_BoxNearAxis d n) :
    lma_BoxClusterReachesRay d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨j₁, j₂, j₃, h1, h2, h3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨j₁, j₂, j₃, bc_clusterReachesRay_of_nearAxis ω x₁ j₁ h1,
    bc_clusterReachesRay_of_nearAxis ω x₂ j₂ h2, bc_clusterReachesRay_of_nearAxis ω x₃ j₃ h3⟩




theorem bc_boxAttachData_of_boxNearAxis {n : ℕ} (h : bc_BoxNearAxis d n) :
    tex_BoxAttachData d n :=
  lma_boxAttachData_of_reachesRay (bc_boxReachesRay_of_boxNearAxis h)










theorem bc_disjointRouting_of_boxNearAxis {n : ℕ} (h : bc_BoxNearAxis d n) :
    hrHD_DisjointRouting d n :=
  lma_disjointRouting_of_reachesRay (bc_boxReachesRay_of_boxNearAxis h)












theorem bc_boxNearAxis_of_boxAxisAssignment {n : ℕ} (h : lmg_BoxAxisAssignment d n) :
    bc_BoxNearAxis d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨j₁, j₂, j₃, _, ha1, ha2, ha3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨j₁, j₂, j₃, bc_nearAxis_of_axisAssignment ω x₁ j₁ ha1,
    bc_nearAxis_of_axisAssignment ω x₂ j₂ ha2, bc_nearAxis_of_axisAssignment ω x₃ j₃ ha3⟩






theorem bc_disjointRouting_of_boxAxisAssignment {n : ℕ} (h : lmg_BoxAxisAssignment d n) :
    hrHD_DisjointRouting d n :=
  bc_disjointRouting_of_boxNearAxis (bc_boxNearAxis_of_boxAxisAssignment h)













theorem bc_nearAxis_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    bc_NearAxis ω (hrHD_rayPt j 1) j :=
  ⟨self_mem_cluster ω (hrHD_rayPt j 1), connected_rfl, hinf⟩





theorem bc_clusterReachesRay_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay ω (hrHD_rayPt j 1) j :=
  bc_clusterReachesRay_of_nearAxis ω (hrHD_rayPt j 1) j (bc_nearAxis_neighbour ω j hinf)








theorem bc_attachData_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d}
    (hcd12 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1))
    (hcd13 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hcd23 : cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
    tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) :=
  lma_attachData_of_three_reachesRay ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)
    j₁ j₂ j₃ hcd12 hcd13 hcd23
    (bc_clusterReachesRay_neighbour ω j₁ hi1) (bc_clusterReachesRay_neighbour ω j₂ hi2)
    (bc_clusterReachesRay_neighbour ω j₃ hi3)






















theorem bc_core (n : ℕ) :
    (bc_BoxNearAxis d n →
        tex_BoxAttachData d n ∧ hrHD_DisjointRouting d n) ∧
      (∀ {j₁ j₂ j₃ : Fin d} (ω : ConfigSpace (Sym2 (Site d))),
        cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1) →
        cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1) →
        cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1) →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite →
        tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :=
  ⟨fun h => ⟨bc_boxAttachData_of_boxNearAxis h, bc_disjointRouting_of_boxNearAxis h⟩,
    fun ω hcd12 hcd13 hcd23 hi1 hi2 hi3 =>
      bc_attachData_of_neighbour_witnesses ω hcd12 hcd13 hcd23 hi1 hi2 hi3⟩

end Walls

end StatMech
