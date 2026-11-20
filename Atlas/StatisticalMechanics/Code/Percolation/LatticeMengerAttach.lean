/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.Percolation.TrifurcationExistence2
import Code.Percolation.BoxMengerAttachment

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}











noncomputable def lma_corridorEdges (j : Fin d) (L : ℕ) : Finset (Sym2 (Site d)) :=
  (Finset.range L).image
    (fun t : ℕ => s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)))


lemma lma_mem_corridorEdges {j : Fin d} {L : ℕ} {t : ℕ} (ht : t < L) :
    s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) ∈ lma_corridorEdges j L := by
  rw [lma_corridorEdges, Finset.mem_image]; exact ⟨t, Finset.mem_range.mpr ht, rfl⟩


@[simp] lemma lma_corridorEdges_zero (j : Fin d) : lma_corridorEdges j 0 = ∅ := by
  rw [lma_corridorEdges]; simp



lemma lma_origin_notMem_corridorEdges (j : Fin d) (L : ℕ) :
    ∀ e ∈ lma_corridorEdges j L, (0 : Site d) ∉ e := by
  rw [lma_corridorEdges]
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨t, _, rfl⟩ := he
  simp only [Sym2.mem_iff]
  push Not
  refine ⟨?_, ?_⟩
  · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega
  · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega










lemma lma_corridor_step_open (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) (t : ℕ)
    (ht : t < L) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω))
      (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) := by
  refine ⟨?_, ?_⟩
  · have h := hrHD_adj_rayPt j ((t : ℤ) + 1)
    have he : ((t : ℤ) + 1 + 1) = ((t : ℤ) + 2) := by ring
    rwa [he] at h
  · have hmem : s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) ∈ lma_corridorEdges j L :=
      lma_mem_corridorEdges ht
    have hno0 : (0 : Site d) ∉ s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) :=
      lma_origin_notMem_corridorEdges j L _ hmem
    rw [removeSite_apply_of_notMem hno0, forceOpenFinset_of_mem hmem]





lemma lma_corridor_connected (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) (m : ℕ)
    (hm : m ≤ L) :
    Connected d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j ((m : ℤ) + 1)) := by
  set ω' := removeSite (0 : Site d) (forceOpenFinset (lma_corridorEdges j L) ω) with hω'
  induction m with
  | zero => simpa using connected_rfl
  | succ p ih =>
    have hpL : p < L := by omega
    have hstep : IsOpenEdge d ω' (hrHD_rayPt j ((p : ℤ) + 1)) (hrHD_rayPt j ((p : ℤ) + 2)) :=
      lma_corridor_step_open ω j L p hpL
    have hrec := ih (by omega)
    have hgoal := hrec.trans hstep.connected
    have he : ((p : ℤ) + 2) = (((p : ℕ) + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rwa [he] at hgoal











def lma_corridorVerts (j : Fin d) (L : ℕ) : Set (Site d) :=
  {y | ∃ m : ℕ, 1 ≤ m ∧ m ≤ L + 1 ∧ y = hrHD_rayPt j (m : ℤ)}



lemma lma_origin_notMem_corridorVerts (j : Fin d) (L : ℕ) :
    (0 : Site d) ∉ lma_corridorVerts j L := by
  rintro ⟨m, hm1, _, heq⟩
  rw [eq_comm, hrHD_rayPt_eq_zero_iff] at heq; omega




lemma lma_corridorVerts_disjoint {j₁ j₂ : Fin d} (h : j₁ ≠ j₂) (L : ℕ) :
    Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₂ L) := by
  rw [Set.disjoint_left]
  rintro y ⟨m, hm1, _, rfl⟩ ⟨n, _, _, hn⟩
  have hm0 : (m : ℤ) ≠ 0 := by
    have : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm1
    omega
  exact hrHD_rayPt_disjoint_of_ne h hm0 hn




lemma lma_corridorEdges_endpoints_mem (j : Fin d) (L : ℕ) :
    ∀ e ∈ lma_corridorEdges j L, ∀ p, p ∈ e → p ∈ lma_corridorVerts j L := by
  rw [lma_corridorEdges]
  intro e he p hp
  rw [Finset.mem_image] at he
  obtain ⟨t, ht, rfl⟩ := he
  rw [Finset.mem_range] at ht
  rw [Sym2.mem_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨t + 1, by omega, by omega, by push_cast; ring_nf⟩
  · exact ⟨t + 2, by omega, by omega, by push_cast; ring_nf⟩










lemma lma_removeSite_le_forceOpen (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) :
    removeSite 0 ω ≤ removeSite 0 (forceOpenFinset W ω) := by
  classical
  have h := bma_removeSite_forceOpen_mono_sub ω (Wⱼ := (∅ : Finset (Sym2 (Site d)))) (W := W)
    (Finset.empty_subset W)
  have he : forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
    funext e; simp [forceOpenFinset]
  rwa [he] at h





















def lma_ClusterReachesRay (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) : Prop :=
  ∃ L : ℕ,
    hrHD_rayPt j 1 ∈ cluster d ω x ∧
    (∀ e ∈ lma_corridorEdges j L, ∀ p, p ∈ e → p ∈ cluster d ω x) ∧
    Connected d (removeSite 0 ω) (hrHD_rayPt j ((L : ℤ) + 1)) x ∧
    (cluster d (removeSite 0 ω) x).Infinite














theorem lma_clusterAttachment_of_reachesRay (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : lma_ClusterReachesRay ω x j) :
    bma_ClusterAttachment ω x := by
  obtain ⟨L, he1, hin, hreach, hinf⟩ := h
  refine ⟨hrHD_rayPt j 1, lma_corridorEdges j L, hrHD_adj_origin_rayPt_one j,
    lma_origin_notMem_corridorEdges j L, hin, he1, ?_, hinf⟩
  have hcorr : Connected d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := lma_corridor_connected ω j L L le_rfl
  have htail : Connected d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω))
      (hrHD_rayPt j ((L : ℤ) + 1)) x :=
    connected_mono (lma_removeSite_le_forceOpen ω (lma_corridorEdges j L)) hreach
  exact hcorr.trans htail

















theorem lma_attachData_of_three_reachesRay (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : lma_ClusterReachesRay ω x₁ j₁) (h2 : lma_ClusterReachesRay ω x₂ j₂)
    (h3 : lma_ClusterReachesRay ω x₃ j₃) :
    tex_AttachData ω x₁ x₂ x₃ :=
  bma_attachment_of_three_clusterAttachments ω x₁ x₂ x₃ hcd12 hcd13 hcd23
    (lma_clusterAttachment_of_reachesRay ω x₁ j₁ h1)
    (lma_clusterAttachment_of_reachesRay ω x₂ j₂ h2)
    (lma_clusterAttachment_of_reachesRay ω x₃ j₃ h3)






theorem lma_threeClustersReachOrigin_of_three_reachesRay (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : lma_ClusterReachesRay ω x₁ j₁) (h2 : lma_ClusterReachesRay ω x₂ j₂)
    (h3 : lma_ClusterReachesRay ω x₃ j₃) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ ⟨hcd12, hcd13, hcd23⟩
    (lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h1 h2 h3)













def lma_BoxClusterReachesRay (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      ∃ j₁ j₂ j₃ : Fin d,
        lma_ClusterReachesRay ω x₁ j₁ ∧ lma_ClusterReachesRay ω x₂ j₂ ∧
          lma_ClusterReachesRay ω x₃ j₃






theorem lma_boxAttachData_of_reachesRay {n : ℕ}
    (h : lma_BoxClusterReachesRay d n) : tex_BoxAttachData d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨j₁, j₂, j₃, h1, h2, h3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h1 h2 h3



theorem lma_disjointRouting_of_reachesRay {n : ℕ}
    (h : lma_BoxClusterReachesRay d n) : hrHD_DisjointRouting d n :=
  tex_disjointRouting_of_box (lma_boxAttachData_of_reachesRay h)




















theorem lma_clusterReachesRay_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay ω (hrHD_rayPt j 1) j := by
  refine ⟨0, self_mem_cluster ω (hrHD_rayPt j 1), ?_, ?_, hinf⟩
  · rw [lma_corridorEdges_zero]; intro e he; exact absurd he (Finset.notMem_empty e)
  · simpa using connected_rfl





theorem lma_attachData_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1))
    (hcd13 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hcd23 : cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
    tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) :=
  lma_attachData_of_three_reachesRay ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)
    j₁ j₂ j₃ hcd12 hcd13 hcd23
    (lma_clusterReachesRay_of_neighbour ω j₁ hi1)
    (lma_clusterReachesRay_of_neighbour ω j₂ hi2)
    (lma_clusterReachesRay_of_neighbour ω j₃ hi3)




theorem lma_corridorVerts_nonempty (j : Fin d) (L : ℕ) :
    (lma_corridorVerts j L).Nonempty :=
  ⟨hrHD_rayPt j 1, 1, le_rfl, by omega, by norm_num⟩

end Percolation

end StatMech
