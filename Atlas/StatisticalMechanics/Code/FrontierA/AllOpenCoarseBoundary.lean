/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.FiniteCutHubCount
import Code.Walls.bc63coarseforest
import Code.Walls.bgf2faithcontract

open Finset Set SimpleGraph

namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation
open StatMech.Walls




theorem bgf2_deleted_reachable_of_cut_connected
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h0 : bgf2_IndexAllOpen omega L 0) {a b : Site 2}
    (h : Connected 2 (removeSites (bc61_boxAround 2 L 0) omega) a b) :
    (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable
      (bgf2_q omega L a) (bgf2_q omega L b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z b hadj p ih =>
    refine Reachable.trans ?_ ih
    have hxout : x ∉ bc61_boxAround 2 L 0 := by
      intro hx
      exact stac_removeSites_no_neighbor (bc61_boxAround 2 L 0) omega hx hadj
    have hzout : z ∉ bc61_boxAround 2 L 0 := by
      intro hz
      exact stac_removeSites_no_neighbor (bc61_boxAround 2 L 0) omega hz hadj.symm
    have hx0 : bgf2_q omega L x ≠ 0 := by
      intro hx
      exact hxout ((bgf2_q_eq_zero_iff_mem h0).1 hx)
    have hz0 : bgf2_q omega L z ≠ 0 := by
      intro hz
      exact hzout ((bgf2_q_eq_zero_iff_mem h0).1 hz)
    by_cases heq : bgf2_q omega L x = bgf2_q omega L z
    · rw [heq]
    · apply SimpleGraph.Adj.reachable
      rw [bkg_deleteVertex_adj]
      refine ⟨?_, hx0, hz0⟩
      rw [bgf2_Gf_adj]
      exact ⟨heq, x, z, rfl, rfl,
        openSubgraph_mono (daep_removeSites_le (bc61_boxAround 2 L 0) omega) hadj⟩



theorem bgf2_q_eq_centre_iff
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j x : Site 2}
    (hj : bgf2_IndexAllOpen omega L j) :
    bgf2_q omega L x = bgf2_centre L j ↔ bgn_idx L x = j := by
  unfold bgf2_q
  by_cases hP : bgf2_IndexAllOpen omega L (bgn_idx L x)
  · rw [if_pos hP]
    constructor
    · exact bgf2_centre_inj
    · intro h
      rw [h]
  · rw [if_neg hP]
    constructor
    · intro h
      exfalso
      apply hP
      have hidx : bgn_idx L x = j := by rw [h, bgf2_idx_centre]
      rwa [hidx]
    · intro h
      exfalso
      apply hP
      rwa [h]


theorem bgf2_mem_box_centre_iff {L : ℕ} {j x : Site 2} :
    x ∈ bc61_boxAround 2 L (bgf2_centre L j) ↔ bgn_idx L x = j := by
  rw [bc61_mem_boxAround, bgf2_idx_iff_inBox]
  simp only [mem_box, bgf2_inBox, Pi.sub_apply]



theorem bgf2_indexAllOpen_cut_at
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j k : Site 2}
    (hk : bgf2_IndexAllOpen omega L k) (hkj : k ≠ j) :
    bgf2_IndexAllOpen
      (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) L k := by
  intro x y hx hy hadj
  have hxout : x ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
    intro hin
    apply hkj
    rw [← hx]
    exact bgf2_mem_box_centre_iff.mp hin
  have hyout : y ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
    intro hin
    apply hkj
    rw [← hy]
    exact bgf2_mem_box_centre_iff.mp hin
  rw [bc61_removeBox_apply_of_notMem hxout hyout]
  exact hk x y hx hy hadj



theorem bgf2_cut_q_eq_connected_at
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j a b : Site 2}
    (hj : bgf2_IndexAllOpen omega L j)
    (h : bgf2_q omega L a = bgf2_q omega L b)
    (hne : bgf2_q omega L a ≠ bgf2_centre L j) :
    Connected 2
      (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a b := by
  have hja : bgn_idx L a ≠ j := fun hidx =>
    hne ((bgf2_q_eq_centre_iff hj).2 hidx)
  unfold bgf2_q at h
  by_cases hPa : bgf2_IndexAllOpen omega L (bgn_idx L a)
  · rw [if_pos hPa] at h
    by_cases hPb : bgf2_IndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      have hidx := bgf2_centre_inj h
      exact bgf2_indexAllOpen_connected
        (bgf2_indexAllOpen_cut_at hPa hja) rfl hidx.symm
    · rw [if_neg hPb] at h
      exfalso
      apply hPb
      have hbi : bgn_idx L b = bgn_idx L a := by
        rw [← h, bgf2_idx_centre]
      rwa [hbi]
  · rw [if_neg hPa] at h
    by_cases hPb : bgf2_IndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      exfalso
      apply hPa
      have hai : bgn_idx L a = bgn_idx L b := by
        rw [h, bgf2_idx_centre]
      rwa [hai]
    · rw [if_neg hPb] at h
      rw [h]


theorem bgf2_cut_connected_of_reach_at
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j : Site 2}
    (hj : bgf2_IndexAllOpen omega L j) :
    ∀ {u v : Site 2},
      (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable u v →
      ∀ a b, bgf2_q omega L a = u → bgf2_q omega L b = v →
        u ≠ bgf2_centre L j → v ≠ bgf2_centre L j →
        Connected 2
          (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a b := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
    intro a b ha hb hu hv
    exact bgf2_cut_q_eq_connected_at hj (ha.trans hb.symm)
      (by rw [ha]; exact hu)
  | @cons u z v hadj p ih =>
    intro a b ha hb hu hv
    obtain ⟨⟨huz, a', b', ha', hb', hab'⟩, hune, hzne⟩ := hadj
    have h1 : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a a' :=
      bgf2_cut_q_eq_connected_at hj (ha.trans ha'.symm)
        (by rw [ha]; exact hu)
    have ha'out : a' ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
      rw [bgf2_mem_box_centre_iff, ← bgf2_q_eq_centre_iff hj]
      rw [ha']
      exact hune
    have hb'out : b' ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
      rw [bgf2_mem_box_centre_iff, ← bgf2_q_eq_centre_iff hj]
      rw [hb']
      exact hzne
    have h2 : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a' b' :=
      bc61_cut_adj_connected hab'.1 hab'.2 ha'out hb'out
    have h3 : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) b' b :=
      ih b' b hb' hb hzne hv
    exact (h1.trans h2).trans h3



def FaithfulAllOpenTrifAt
    (omega : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j : Site 2) : Prop :=
  bc67_IsGnTrifurcation omega L (bgf2_centre L j) ∧
    bgf2_IndexAllOpen omega L j


theorem faithfulAllOpenTrifAt_boundary_witnesses
    {omega : ConfigSpace (Sym2 (Site 2))} {L R : ℕ} {j : Site 2}
    (hR : 1 ≤ R) (h : FaithfulAllOpenTrifAt omega L j)
    (harms : ∀ a : Site 2,
      bc67_GnIncident omega L (bgf2_centre L j) a →
      (cluster 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a).Infinite →
      a ∈ box 2 R) :
    ∃ z1 z2 z3 : Site 2,
      z1 ∈ vertexBoundary 2 R ∧ z2 ∈ vertexBoundary 2 R ∧
      z3 ∈ vertexBoundary 2 R ∧
      bgf2_q omega L z1 ≠ bgf2_centre L j ∧
      bgf2_q omega L z2 ≠ bgf2_centre L j ∧
      bgf2_q omega L z3 ≠ bgf2_centre L j ∧
      (bgf2_Gf omega L).Reachable (bgf2_centre L j) (bgf2_q omega L z1) ∧
      (bgf2_Gf omega L).Reachable (bgf2_centre L j) (bgf2_q omega L z2) ∧
      (bgf2_Gf omega L).Reachable (bgf2_centre L j) (bgf2_q omega L z3) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable
          (bgf2_q omega L z1) (bgf2_q omega L z2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable
          (bgf2_q omega L z1) (bgf2_q omega L z3) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable
          (bgf2_q omega L z2) (bgf2_q omega L z3) := by
  obtain ⟨htri, hj⟩ := h
  obtain ⟨a1, a2, a3, ⟨hi1, hi2, hi3⟩, ⟨hinf1, hinf2, hinf3⟩,
    hcut12, hcut13, hcut23⟩ := htri
  obtain ⟨z1, hz1, hr1⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR (bgf2_centre L j) a1
      (harms a1 hi1 hinf1) hinf1
  obtain ⟨z2, hz2, hr2⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR (bgf2_centre L j) a2
      (harms a2 hi2 hinf2) hinf2
  obtain ⟨z3, hz3, hr3⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR (bgf2_centre L j) a3
      (harms a3 hi3 hinf3) hinf3
  have ha1out := stac_infiniteCluster_notMem _ _ hinf1
  have ha2out := stac_infiniteCluster_notMem _ _ hinf2
  have ha3out := stac_infiniteCluster_notMem _ _ hinf3
  have hzout (a z : Site 2)
      (ha : a ∉ bc61_boxAround 2 L (bgf2_centre L j))
      (hr : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a z) :
      z ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
    intro hz
    have heq := stac_removeSites_connected_eq
      (bc61_boxAround 2 L (bgf2_centre L j)) omega hz hr.symm
    exact ha (heq ▸ hz)
  have hz1out := hzout a1 z1 ha1out hr1
  have hz2out := hzout a2 z2 ha2out hr2
  have hz3out := hzout a3 z3 ha3out hr3
  have hnz (z : Site 2)
      (hz : z ∉ bc61_boxAround 2 L (bgf2_centre L j)) :
      bgf2_q omega L z ≠ bgf2_centre L j := by
    intro heq
    exact hz (bgf2_mem_box_centre_iff.mpr
      ((bgf2_q_eq_centre_iff hj).mp heq))
  have hnz1 := hnz z1 hz1out
  have hnz2 := hnz z2 hz2out
  have hnz3 := hnz z3 hz3out
  have hreach (a z : Site 2)
      (hi : bc67_GnIncident omega L (bgf2_centre L j) a)
      (hr : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a z) :
      (bgf2_Gf omega L).Reachable
        (bgf2_centre L j) (bgf2_q omega L z) := by
    obtain ⟨b, hb, hba⟩ := hi
    have hqb : bgf2_q omega L b = bgf2_centre L j :=
      (bgf2_q_eq_centre_iff hj).2 (bgf2_mem_box_centre_iff.mp hb)
    have hc : Connected 2 omega b z :=
      hba.reachable.trans (bc61_connected_of_cut hr)
    simpa [hqb] using bgf2_reach_of_connected (L := L) hc
  refine ⟨z1, z2, z3, hz1, hz2, hz3, hnz1, hnz2, hnz3,
    hreach a1 z1 hi1 hr1, hreach a2 z2 hi2 hr2,
    hreach a3 z3 hi3 hr3, ?_, ?_, ?_⟩
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_at hj hc z1 z2 rfl rfl hnz1 hnz2
    exact hcut12 (hr1.trans (hc'.trans hr2.symm))
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_at hj hc z1 z3 rfl rfl hnz1 hnz3
    exact hcut13 (hr1.trans (hc'.trans hr3.symm))
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_at hj hc z2 z3 rfl rfl hnz2 hnz3
    exact hcut23 (hr2.trans (hc'.trans hr3.symm))



theorem faithfulAllOpenTrifAt_count_le_boundary
    (omega : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (hR : 1 ≤ R)
    (J : Finset (Site 2))
    (htrif : ∀ j ∈ J, FaithfulAllOpenTrifAt omega L j)
    (harms : ∀ j ∈ J, ∀ a : Site 2,
      bc67_GnIncident omega L (bgf2_centre L j) a →
      (cluster 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a).Infinite →
      a ∈ box 2 R) :
    J.card ≤ (vertexBoundary_finite 2 R).toFinset.card := by
  classical
  let hubs : Finset (Site 2) := J.image (bgf2_centre L)
  let boundary : Finset (Site 2) :=
    (vertexBoundary_finite 2 R).toFinset.image (bgf2_q omega L)
  have hhubCard : hubs.card = J.card := by
    change (J.image (bgf2_centre L)).card = J.card
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact bgf2_centre_inj hab
  have hboundaryCard : boundary.card ≤
      (vertexBoundary_finite 2 R).toFinset.card := by
    exact Finset.card_image_le
  have hcount : hubs.card ≤ boundary.card := by
    apply finite_cutHub_count_of_ambient (bgf2_Gf omega L) hubs boundary
    intro u hu
    change u ∈ J.image (bgf2_centre L) at hu
    obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨z1, z2, z3, hz1, hz2, hz3, hnz1, hnz2, hnz3,
      hr1, hr2, hr3, hc12, hc13, hc23⟩ :=
      faithfulAllOpenTrifAt_boundary_witnesses hR (htrif j hjJ)
        (harms j hjJ)
    have ht1 : bgf2_q omega L z1 ∈ boundary := by
      apply Finset.mem_image.mpr
      exact ⟨z1, by simpa using hz1, rfl⟩
    have ht2 : bgf2_q omega L z2 ∈ boundary := by
      apply Finset.mem_image.mpr
      exact ⟨z2, by simpa using hz2, rfl⟩
    have ht3 : bgf2_q omega L z3 ∈ boundary := by
      apply Finset.mem_image.mpr
      exact ⟨z3, by simpa using hz3, rfl⟩
    have hdel : (bgf2_Gf omega L).deleteIncidenceSet (bgf2_centre L j) =
        bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j) := by
      ext a b
      rw [SimpleGraph.deleteIncidenceSet_adj, bkg_deleteVertex_adj]
    refine ⟨bgf2_q omega L z1, bgf2_q omega L z2,
      bgf2_q omega L z3, ht1, ht2, ht3, hnz1.symm, hnz2.symm,
      hnz3.symm, hr1, hr2, hr3, ?_, ?_, ?_⟩
    · rwa [hdel]
    · rwa [hdel]
    · rwa [hdel]
  rw [hhubCard] at hcount
  exact hcount.trans hboundaryCard



theorem gnIncident_arm_mem_outer_box
    {omega : ConfigSpace (Sym2 (Site 2))} {L N : ℕ} {j a : Site 2}
    (hc : bgf2_centre L j ∈ box 2 N)
    (hi : bc67_GnIncident omega L (bgf2_centre L j) a) :
    a ∈ box 2 (N + L + 1) := by
  obtain ⟨b, hb, hba⟩ := hi
  have hbrel : b - bgf2_centre L j ∈ box 2 L :=
    bc61_mem_boxAround.mp hb
  have hbbox : b ∈ box 2 (N + L) := by
    rw [mem_box] at hc hbrel ⊢
    intro i
    have htri : (b i).natAbs ≤ (bgf2_centre L j i).natAbs +
        (b i - bgf2_centre L j i).natAbs := by
      have hid : b i = bgf2_centre L j i +
          (b i - bgf2_centre L j i) := by ring
      calc
        (b i).natAbs = (bgf2_centre L j i +
            (b i - bgf2_centre L j i)).natAbs := congrArg Int.natAbs hid
        _ ≤ (bgf2_centre L j i).natAbs +
            (b i - bgf2_centre L j i).natAbs := Int.natAbs_add_le _ _
    have hc' := hc i
    have hb' : (b i - bgf2_centre L j i).natAbs ≤ L := by
      simpa only [Pi.sub_apply] using hbrel i
    omega
  exact arc_neighbour_in_box_succ hbbox hba.1



theorem faithfulAllOpenTrifAt_count_inner
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ)
    (J : Finset (Site 2))
    (htrif : ∀ j ∈ J, FaithfulAllOpenTrifAt omega L j)
    (hcenter : ∀ j ∈ J, bgf2_centre L j ∈ box 2 N) :
    J.card ≤ (vertexBoundary_finite 2 (N + L + 1)).toFinset.card := by
  apply faithfulAllOpenTrifAt_count_le_boundary omega L (N + L + 1)
    (by omega) J htrif
  intro j hj a hi _hinf
  exact gnIncident_arm_mem_outer_box (hcenter j hj) hi



theorem bgf2_centre_mem_scaled_box {L N : ℕ} {j : Site 2}
    (hj : j ∈ box 2 N) :
    bgf2_centre L j ∈ box 2 ((2 * L + 1) * N) := by
  rw [mem_box] at hj ⊢
  intro i
  simp only [bgf2_centre, Int.natAbs_mul]
  have hj' := hj i
  exact Nat.mul_le_mul_left (2 * L + 1) hj'

noncomputable def faithfulAllOpenTrifIndicesInBox
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ) : Finset (Site 2) := by
  classical
  exact (box_finite 2 N).toFinset.filter (FaithfulAllOpenTrifAt omega L)

@[simp] theorem mem_faithfulAllOpenTrifIndicesInBox
    {omega : ConfigSpace (Sym2 (Site 2))} {L N : ℕ} {j : Site 2} :
    j ∈ faithfulAllOpenTrifIndicesInBox omega L N ↔
      j ∈ box 2 N ∧ FaithfulAllOpenTrifAt omega L j := by
  classical
  simp [faithfulAllOpenTrifIndicesInBox]



theorem faithfulAllOpenTrifIndicesInBox_count
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ) :
    (faithfulAllOpenTrifIndicesInBox omega L N).card ≤
      (vertexBoundary_finite 2
        ((2 * L + 1) * N + L + 1)).toFinset.card := by
  apply faithfulAllOpenTrifAt_count_inner omega L ((2 * L + 1) * N)
  · intro j hj
    exact (mem_faithfulAllOpenTrifIndicesInBox.mp hj).2
  · intro j hj
    exact bgf2_centre_mem_scaled_box
      (mem_faithfulAllOpenTrifIndicesInBox.mp hj).1




theorem allOpenTrif_boundary_witnesses
    {omega : ConfigSpace (Sym2 (Site 2))} {L R : ℕ} (hR : 1 ≤ R)
    (h : bao_AllOpenTrif omega L)
    (harms : ∀ a : Site 2, bc67_GnIncident omega L 0 a →
      (cluster 2 (removeSites (bc61_boxAround 2 L 0) omega) a).Infinite →
      a ∈ box 2 R) :
    ∃ z1 z2 z3 : Site 2,
      z1 ∈ vertexBoundary 2 R ∧ z2 ∈ vertexBoundary 2 R ∧
      z3 ∈ vertexBoundary 2 R ∧
      bgf2_q omega L z1 ≠ 0 ∧ bgf2_q omega L z2 ≠ 0 ∧
      bgf2_q omega L z3 ≠ 0 ∧
      (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z1) ∧
      (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z2) ∧
      (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z3) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable
          (bgf2_q omega L z1) (bgf2_q omega L z2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable
          (bgf2_q omega L z1) (bgf2_q omega L z3) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable
          (bgf2_q omega L z2) (bgf2_q omega L z3) := by
  obtain ⟨htri, hopen⟩ := h
  have h0 : bgf2_IndexAllOpen omega L 0 :=
    bgf2_indexAllOpen_zero_of_bff hopen
  obtain ⟨a1, a2, a3, ⟨hi1, hi2, hi3⟩, ⟨hinf1, hinf2, hinf3⟩,
    hcut12, hcut13, hcut23⟩ := htri
  obtain ⟨z1, hz1, hr1⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR 0 a1
      (harms a1 hi1 hinf1) hinf1
  obtain ⟨z2, hz2, hr2⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR 0 a2
      (harms a2 hi2 hinf2) hinf2
  obtain ⟨z3, hz3, hr3⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR 0 a3
      (harms a3 hi3 hinf3) hinf3
  have ha1out : a1 ∉ bc61_boxAround 2 L 0 := stac_infiniteCluster_notMem _ _ hinf1
  have ha2out : a2 ∉ bc61_boxAround 2 L 0 := stac_infiniteCluster_notMem _ _ hinf2
  have ha3out : a3 ∉ bc61_boxAround 2 L 0 := stac_infiniteCluster_notMem _ _ hinf3
  have hz1out : z1 ∉ bc61_boxAround 2 L 0 := by
    intro hz
    have heq := stac_removeSites_connected_eq
      (bc61_boxAround 2 L 0) omega hz hr1.symm
    exact ha1out (heq ▸ hz)
  have hz2out : z2 ∉ bc61_boxAround 2 L 0 := by
    intro hz
    have heq := stac_removeSites_connected_eq
      (bc61_boxAround 2 L 0) omega hz hr2.symm
    exact ha2out (heq ▸ hz)
  have hz3out : z3 ∉ bc61_boxAround 2 L 0 := by
    intro hz
    have heq := stac_removeSites_connected_eq
      (bc61_boxAround 2 L 0) omega hz hr3.symm
    exact ha3out (heq ▸ hz)
  have hnz1 : bgf2_q omega L z1 ≠ 0 := by
    intro hz
    exact hz1out ((bgf2_q_eq_zero_iff_mem h0).1 hz)
  have hnz2 : bgf2_q omega L z2 ≠ 0 := by
    intro hz
    exact hz2out ((bgf2_q_eq_zero_iff_mem h0).1 hz)
  have hnz3 : bgf2_q omega L z3 ≠ 0 := by
    intro hz
    exact hz3out ((bgf2_q_eq_zero_iff_mem h0).1 hz)
  have hreach (a z : Site 2) (hi : bc67_GnIncident omega L 0 a)
      (hr : Connected 2 (removeSites (bc61_boxAround 2 L 0) omega) a z) :
      (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z) := by
    obtain ⟨b, hb, hba⟩ := hi
    have hqb : bgf2_q omega L b = 0 :=
      (bgf2_q_eq_zero_iff_mem h0).2 hb
    have hc : Connected 2 omega b z := hba.reachable.trans (bc61_connected_of_cut hr)
    simpa [hqb] using bgf2_reach_of_connected (L := L) hc
  refine ⟨z1, z2, z3, hz1, hz2, hz3, hnz1, hnz2, hnz3,
    hreach a1 z1 hi1 hr1, hreach a2 z2 hi2 hr2,
    hreach a3 z3 hi3 hr3, ?_, ?_, ?_⟩
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_aux h0 hc z1 z2 rfl rfl hnz1 hnz2
    exact hcut12 (hr1.trans (hc'.trans hr2.symm))
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_aux h0 hc z1 z3 rfl rfl hnz1 hnz3
    exact hcut13 (hr1.trans (hc'.trans hr3.symm))
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_aux h0 hc z2 z3 rfl rfl hnz2 hnz3
    exact hcut23 (hr2.trans (hc'.trans hr3.symm))

end StatMech.FrontierA
