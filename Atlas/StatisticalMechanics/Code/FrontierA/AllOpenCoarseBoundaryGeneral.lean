/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.AllOpenContractionGeneral
import Code.FrontierA.FiniteCutHubCount
import Code.Walls.bc63coarseforest

open Finset Set SimpleGraph

namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation
open StatMech.Walls

variable {d : ℕ}



def BgfdFaithfulAllOpenTrifAt
    (omega : ConfigSpace (Sym2 (Site d))) (L : ℕ) (j : Site d) : Prop :=
  bc67_IsGnTrifurcation omega L (bgfdCentre L j) ∧
    BgfdIndexAllOpen omega L j


theorem bgfdFaithfulAllOpenTrifAt_boundary_witnesses
    {omega : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {j : Site d}
    (hR : 1 ≤ R) (h : BgfdFaithfulAllOpenTrifAt omega L j)
    (harms : ∀ a : Site d,
      bc67_GnIncident omega L (bgfdCentre L j) a →
      (cluster d
        (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a).Infinite →
      a ∈ box d R) :
    ∃ z1 z2 z3 : Site d,
      z1 ∈ vertexBoundary d R ∧ z2 ∈ vertexBoundary d R ∧
      z3 ∈ vertexBoundary d R ∧
      bgfdQ omega L z1 ≠ bgfdCentre L j ∧
      bgfdQ omega L z2 ≠ bgfdCentre L j ∧
      bgfdQ omega L z3 ≠ bgfdCentre L j ∧
      (bgfdGraph omega L).Reachable (bgfdCentre L j) (bgfdQ omega L z1) ∧
      (bgfdGraph omega L).Reachable (bgfdCentre L j) (bgfdQ omega L z2) ∧
      (bgfdGraph omega L).Reachable (bgfdCentre L j) (bgfdQ omega L z3) ∧
      ¬ (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable
          (bgfdQ omega L z1) (bgfdQ omega L z2) ∧
      ¬ (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable
          (bgfdQ omega L z1) (bgfdQ omega L z3) ∧
      ¬ (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable
          (bgfdQ omega L z2) (bgfdQ omega L z3) := by
  obtain ⟨htri, hj⟩ := h
  obtain ⟨a1, a2, a3, ⟨hi1, hi2, hi3⟩, ⟨hinf1, hinf2, hinf3⟩,
    hcut12, hcut13, hcut23⟩ := htri
  obtain ⟨z1, hz1, hr1⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR (bgfdCentre L j) a1
      (harms a1 hi1 hinf1) hinf1
  obtain ⟨z2, hz2, hr2⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR (bgfdCentre L j) a2
      (harms a2 hi2 hinf2) hinf2
  obtain ⟨z3, hz3, hr3⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR (bgfdCentre L j) a3
      (harms a3 hi3 hinf3) hinf3
  have ha1out := stac_infiniteCluster_notMem _ _ hinf1
  have ha2out := stac_infiniteCluster_notMem _ _ hinf2
  have ha3out := stac_infiniteCluster_notMem _ _ hinf3
  have hzout (a z : Site d)
      (ha : a ∉ bc61_boxAround d L (bgfdCentre L j))
      (hr : Connected d
        (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a z) :
      z ∉ bc61_boxAround d L (bgfdCentre L j) := by
    intro hz
    have heq := stac_removeSites_connected_eq
      (bc61_boxAround d L (bgfdCentre L j)) omega hz hr.symm
    exact ha (heq ▸ hz)
  have hz1out := hzout a1 z1 ha1out hr1
  have hz2out := hzout a2 z2 ha2out hr2
  have hz3out := hzout a3 z3 ha3out hr3
  have hnz (z : Site d)
      (hz : z ∉ bc61_boxAround d L (bgfdCentre L j)) :
      bgfdQ omega L z ≠ bgfdCentre L j := by
    intro heq
    exact hz (bgfd_mem_box_centre_iff.mpr
      ((bgfd_q_eq_centre_iff hj).mp heq))
  have hnz1 := hnz z1 hz1out
  have hnz2 := hnz z2 hz2out
  have hnz3 := hnz z3 hz3out
  have hreach (a z : Site d)
      (hi : bc67_GnIncident omega L (bgfdCentre L j) a)
      (hr : Connected d
        (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a z) :
      (bgfdGraph omega L).Reachable
        (bgfdCentre L j) (bgfdQ omega L z) := by
    obtain ⟨b, hb, hba⟩ := hi
    have hqb : bgfdQ omega L b = bgfdCentre L j :=
      (bgfd_q_eq_centre_iff hj).2 (bgfd_mem_box_centre_iff.mp hb)
    have hc : Connected d omega b z :=
      hba.reachable.trans (bc61_connected_of_cut hr)
    simpa [hqb] using bgfd_reach_of_connected (L := L) hc
  refine ⟨z1, z2, z3, hz1, hz2, hz3, hnz1, hnz2, hnz3,
    hreach a1 z1 hi1 hr1, hreach a2 z2 hi2 hr2,
    hreach a3 z3 hi3 hr3, ?_, ?_, ?_⟩
  · intro hc
    have hc' := bgfd_cut_connected_of_reach_at hj hc z1 z2 rfl rfl hnz1 hnz2
    exact hcut12 (hr1.trans (hc'.trans hr2.symm))
  · intro hc
    have hc' := bgfd_cut_connected_of_reach_at hj hc z1 z3 rfl rfl hnz1 hnz3
    exact hcut13 (hr1.trans (hc'.trans hr3.symm))
  · intro hc
    have hc' := bgfd_cut_connected_of_reach_at hj hc z2 z3 rfl rfl hnz2 hnz3
    exact hcut23 (hr2.trans (hc'.trans hr3.symm))



theorem bgfdFaithfulAllOpenTrifAt_count_le_boundary
    (omega : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (J : Finset (Site d))
    (htrif : ∀ j ∈ J, BgfdFaithfulAllOpenTrifAt omega L j)
    (harms : ∀ j ∈ J, ∀ a : Site d,
      bc67_GnIncident omega L (bgfdCentre L j) a →
      (cluster d
        (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a).Infinite →
      a ∈ box d R) :
    J.card ≤ (vertexBoundary_finite d R).toFinset.card := by
  classical
  let hubs : Finset (Site d) := J.image (bgfdCentre L)
  let boundary : Finset (Site d) :=
    (vertexBoundary_finite d R).toFinset.image (bgfdQ omega L)
  have hhubCard : hubs.card = J.card := by
    change (J.image (bgfdCentre L)).card = J.card
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact bgfd_centre_injective L hab
  have hboundaryCard : boundary.card ≤
      (vertexBoundary_finite d R).toFinset.card := by
    exact Finset.card_image_le
  have hcount : hubs.card ≤ boundary.card := by
    apply finite_cutHub_count_of_ambient (bgfdGraph omega L) hubs boundary
    intro u hu
    change u ∈ J.image (bgfdCentre L) at hu
    obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨z1, z2, z3, hz1, hz2, hz3, hnz1, hnz2, hnz3,
      hr1, hr2, hr3, hc12, hc13, hc23⟩ :=
      bgfdFaithfulAllOpenTrifAt_boundary_witnesses hR (htrif j hjJ)
        (harms j hjJ)
    have ht1 : bgfdQ omega L z1 ∈ boundary := by
      apply Finset.mem_image.mpr
      exact ⟨z1, by simpa using hz1, rfl⟩
    have ht2 : bgfdQ omega L z2 ∈ boundary := by
      apply Finset.mem_image.mpr
      exact ⟨z2, by simpa using hz2, rfl⟩
    have ht3 : bgfdQ omega L z3 ∈ boundary := by
      apply Finset.mem_image.mpr
      exact ⟨z3, by simpa using hz3, rfl⟩
    have hdel : (bgfdGraph omega L).deleteIncidenceSet (bgfdCentre L j) =
        bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j) := by
      ext a b
      rw [SimpleGraph.deleteIncidenceSet_adj, bkg_deleteVertex_adj]
    refine ⟨bgfdQ omega L z1, bgfdQ omega L z2,
      bgfdQ omega L z3, ht1, ht2, ht3, hnz1.symm, hnz2.symm,
      hnz3.symm, hr1, hr2, hr3, ?_, ?_, ?_⟩
    · rwa [hdel]
    · rwa [hdel]
    · rwa [hdel]
  rw [hhubCard] at hcount
  exact hcount.trans hboundaryCard



theorem bgfd_gnIncident_arm_mem_outer_box
    {omega : ConfigSpace (Sym2 (Site d))} {L N : ℕ} {j a : Site d}
    (hc : bgfdCentre L j ∈ box d N)
    (hi : bc67_GnIncident omega L (bgfdCentre L j) a) :
    a ∈ box d (N + L + 1) := by
  obtain ⟨b, hb, hba⟩ := hi
  have hbrel : b - bgfdCentre L j ∈ box d L :=
    bc61_mem_boxAround.mp hb
  have hbbox : b ∈ box d (N + L) := by
    rw [mem_box] at hc hbrel ⊢
    intro i
    have htri : (b i).natAbs ≤ (bgfdCentre L j i).natAbs +
        (b i - bgfdCentre L j i).natAbs := by
      have hid : b i = bgfdCentre L j i +
          (b i - bgfdCentre L j i) := by ring
      calc
        (b i).natAbs = (bgfdCentre L j i +
            (b i - bgfdCentre L j i)).natAbs := congrArg Int.natAbs hid
        _ ≤ (bgfdCentre L j i).natAbs +
            (b i - bgfdCentre L j i).natAbs := Int.natAbs_add_le _ _
    have hc' := hc i
    have hb' : (b i - bgfdCentre L j i).natAbs ≤ L := by
      simpa only [Pi.sub_apply] using hbrel i
    omega
  exact arc_neighbour_in_box_succ hbbox hba.1



theorem bgfdFaithfulAllOpenTrifAt_count_inner
    (omega : ConfigSpace (Sym2 (Site d))) (L N : ℕ)
    (J : Finset (Site d))
    (htrif : ∀ j ∈ J, BgfdFaithfulAllOpenTrifAt omega L j)
    (hcenter : ∀ j ∈ J, bgfdCentre L j ∈ box d N) :
    J.card ≤ (vertexBoundary_finite d (N + L + 1)).toFinset.card := by
  apply bgfdFaithfulAllOpenTrifAt_count_le_boundary omega L (N + L + 1)
    (by omega) J htrif
  intro j hj a hi _hinf
  exact bgfd_gnIncident_arm_mem_outer_box (hcenter j hj) hi



theorem bgfd_centre_mem_scaled_box {L N : ℕ} {j : Site d}
    (hj : j ∈ box d N) :
    bgfdCentre L j ∈ box d ((2 * L + 1) * N) := by
  rw [mem_box] at hj ⊢
  intro i
  simp only [bgfdCentre, Int.natAbs_mul]
  have hj' := hj i
  exact Nat.mul_le_mul_left (2 * L + 1) hj'

noncomputable def bgfdFaithfulAllOpenTrifIndicesInBox
    (omega : ConfigSpace (Sym2 (Site d))) (L N : ℕ) : Finset (Site d) := by
  classical
  exact (box_finite d N).toFinset.filter (BgfdFaithfulAllOpenTrifAt omega L)

@[simp] theorem mem_bgfdFaithfulAllOpenTrifIndicesInBox
    {omega : ConfigSpace (Sym2 (Site d))} {L N : ℕ} {j : Site d} :
    j ∈ bgfdFaithfulAllOpenTrifIndicesInBox omega L N ↔
      j ∈ box d N ∧ BgfdFaithfulAllOpenTrifAt omega L j := by
  classical
  simp [bgfdFaithfulAllOpenTrifIndicesInBox]



theorem bgfdFaithfulAllOpenTrifIndicesInBox_count
    (omega : ConfigSpace (Sym2 (Site d))) (L N : ℕ) :
    (bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card ≤
      (vertexBoundary_finite d
        ((2 * L + 1) * N + L + 1)).toFinset.card := by
  apply bgfdFaithfulAllOpenTrifAt_count_inner omega L ((2 * L + 1) * N)
  · intro j hj
    exact (mem_bgfdFaithfulAllOpenTrifIndicesInBox.mp hj).2
  · intro j hj
    exact bgfd_centre_mem_scaled_box
      (mem_bgfdFaithfulAllOpenTrifIndicesInBox.mp hj).1


end StatMech.FrontierA
