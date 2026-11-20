/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































































import Mathlib
import Code.Walls.bc2_core
import Code.Walls.bc3_barrierblocks
import Code.Walls.bc3_rhoedgecases
import Code.Walls.bc3_anchordecomp

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}










def bc3_clusterNbhd (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) : Set (Site d) :=
  ⋃ (t : ℕ) (_ : 1 ≤ t ∧ t ≤ L), cluster d (removeSite 0 ω) (hrHD_rayPt j (t : ℤ))



lemma bc3_mem_clusterNbhd {ω : ConfigSpace (Sym2 (Site d))} {j : Fin d} {L : ℕ} {x : Site d} :
    x ∈ bc3_clusterNbhd ω j L ↔
      ∃ t : ℕ, (1 ≤ t ∧ t ≤ L) ∧ x ∈ cluster d (removeSite 0 ω) (hrHD_rayPt j (t : ℤ)) := by
  simp only [bc3_clusterNbhd, Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hx⟩; exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩; exact ⟨t, ht, hx⟩


lemma bc3_rayPt_mem_clusterNbhd {ω : ConfigSpace (Sym2 (Site d))} {j : Fin d} {L t : ℕ}
    (h1 : 1 ≤ t) (h2 : t ≤ L) : hrHD_rayPt j (t : ℤ) ∈ bc3_clusterNbhd ω j L := by
  rw [bc3_mem_clusterNbhd]
  exact ⟨t, ⟨h1, h2⟩, self_mem_cluster _ _⟩


lemma bc3_mouth_mem_clusterNbhd {ω : ConfigSpace (Sym2 (Site d))} {j : Fin d} {L : ℕ}
    (hL : 1 ≤ L) : (hrHD_rayPt j 1 : Site d) ∈ bc3_clusterNbhd ω j L := by
  have h : hrHD_rayPt j ((1 : ℕ) : ℤ) = hrHD_rayPt j 1 := by norm_num
  rw [← h]
  exact bc3_rayPt_mem_clusterNbhd le_rfl hL








lemma bc3_corridorEdge_structure {j : Fin d} {L : ℕ} {u v : Site d}
    (h : s(u, v) ∈ hrHD_corridorEdges j L) :
    ∃ p : ℕ, p < L ∧ s(u, v) = s(hrHD_rayPt j (p : ℤ), hrHD_rayPt j ((p : ℤ) + 1)) := by
  rw [hrHD_corridorEdges, Finset.mem_image] at h
  obtain ⟨p, hp, hpe⟩ := h
  rw [Finset.mem_range] at hp
  exact ⟨p, hp, hpe.symm⟩












def bc3_CrossDisjoint (ω : ConfigSpace (Sym2 (Site d)))
    (a c : Fin d) (R L : ℕ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → p ≤ L → hrHD_rayPt c (p : ℤ) ∉ bc3_clusterNbhd ω a R







lemma bc3_sameAxis_step_mem (ω : ConfigSpace (Sym2 (Site d))) (a : Fin d) (La : ℕ)
    {u v : Site d} (hno0 : (0 : Site d) ∉ s(u, v))
    (hmem : s(u, v) ∈ hrHD_corridorEdges a (La + 1)) :
    v ∈ bc3_clusterNbhd ω a (La + 1) := by
  obtain ⟨p, hp, hpe⟩ := bc3_corridorEdge_structure hmem
  have hp1 : 1 ≤ p := by
    by_contra hlt
    have hp0 : p = 0 := by omega
    subst hp0
    apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]; exact Sym2.mem_mk_left _ _
  have hvmem : v ∈ s(hrHD_rayPt a (p : ℤ), hrHD_rayPt a ((p : ℤ) + 1)) := by
    rw [← hpe]; exact Sym2.mem_mk_right _ _
  rw [Sym2.mem_iff] at hvmem
  rcases hvmem with rfl | rfl
  · exact bc3_rayPt_mem_clusterNbhd hp1 (by omega)
  · have h : hrHD_rayPt a ((p : ℤ) + 1) = hrHD_rayPt a ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h]; exact bc3_rayPt_mem_clusterNbhd (by omega) (by omega)





lemma bc3_crossAxis_step_absurd (ω : ConfigSpace (Sym2 (Site d))) (a c : Fin d) (La Lc : ℕ)
    (hcross : bc3_CrossDisjoint ω a c (La + 1) (Lc + 1))
    {u v : Site d} (hno0 : (0 : Site d) ∉ s(u, v))
    (hu : u ∈ bc3_clusterNbhd ω a (La + 1))
    (hmem : s(u, v) ∈ hrHD_corridorEdges c (Lc + 1)) : False := by
  obtain ⟨p, hp, hpe⟩ := bc3_corridorEdge_structure hmem
  have hp1 : 1 ≤ p := by
    by_contra hlt
    have hp0 : p = 0 := by omega
    subst hp0
    apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]; exact Sym2.mem_mk_left _ _
  have humem : u ∈ s(hrHD_rayPt c (p : ℤ), hrHD_rayPt c ((p : ℤ) + 1)) := by
    rw [← hpe]; exact Sym2.mem_mk_left _ _
  rw [Sym2.mem_iff] at humem
  rcases humem with rfl | rfl
  · exact hcross p hp1 (by omega) hu
  · have h : hrHD_rayPt c ((p : ℤ) + 1) = hrHD_rayPt c ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h] at hu
    exact hcross (p + 1) (by omega) (by omega) hu












lemma bc3_clusterNbhd_adjClosed_gen (ω : ConfigSpace (Sym2 (Site d)))
    (a c₁ c₂ : Fin d) (La Lc₁ Lc₂ : ℕ)
    (hcross1 : bc3_CrossDisjoint ω a c₁ (La + 1) (Lc₁ + 1))
    (hcross2 : bc3_CrossDisjoint ω a c₂ (La + 1) (Lc₂ + 1)) :
    bc3_AdjClosed (removeSite 0 (forceOpenFinset
        (hrHD_corridorEdges a (La + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪
          hrHD_corridorEdges c₂ (Lc₂ + 1)) ω))
      (bc3_clusterNbhd ω a (La + 1)) := by
  set G : Finset (Sym2 (Site d)) := hrHD_corridorEdges a (La + 1) ∪
    hrHD_corridorEdges c₁ (Lc₁ + 1) ∪ hrHD_corridorEdges c₂ (Lc₂ + 1) with hGdef
  intro u v hu hadj
  have hopen : removeSite 0 (forceOpenFinset G ω) s(u, v) = true := hadj.2
  obtain ⟨hno0, hcase⟩ := bc3_rhoEdge_cases ω G hopen
  rcases hcase with hωopen | hGmem
  · 
    rw [bc3_mem_clusterNbhd] at hu ⊢
    obtain ⟨t, ht, hut⟩ := hu
    refine ⟨t, ht, ?_⟩
    have hrm0 : removeSite (0 : Site d) ω s(u, v) = true := by
      rw [removeSite_apply_of_notMem hno0]; exact hωopen
    have huv : IsOpenEdge d (removeSite 0 ω) u v := ⟨hadj.1, hrm0⟩
    rw [mem_cluster] at hut ⊢
    exact hut.trans huv.connected
  · 
    rw [hGdef, Finset.mem_union, Finset.mem_union] at hGmem
    rcases hGmem with (ha | h1) | h2
    · exact bc3_sameAxis_step_mem ω a La hno0 ha
    · exact absurd (bc3_crossAxis_step_absurd ω a c₁ La Lc₁ hcross1 hno0 hu h1) (by simp)
    · exact absurd (bc3_crossAxis_step_absurd ω a c₂ La Lc₂ hcross2 hno0 hu h2) (by simp)



lemma bc3_clusterNbhd_adjClosed (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (hcross2 : bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1))
    (hcross3 : bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1)) :
    bc3_AdjClosed (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
      (bc3_clusterNbhd ω j₁ (L₁ + 1)) := by
  have h := bc3_clusterNbhd_adjClosed_gen ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3
  rwa [bc3_corridorUnion]








lemma bc3_corridorUnion_perm2 (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃ =
      hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₁ (L₁ + 1) ∪
        hrHD_corridorEdges j₃ (L₃ + 1) := by
  rw [bc3_corridorUnion]; ext e; simp only [Finset.mem_union]; tauto


lemma bc3_corridorUnion_perm3 (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃ =
      hrHD_corridorEdges j₃ (L₃ + 1) ∪ hrHD_corridorEdges j₁ (L₁ + 1) ∪
        hrHD_corridorEdges j₂ (L₂ + 1) := by
  rw [bc3_corridorUnion]; ext e; simp only [Finset.mem_union]; tauto






lemma bc3_mouth_separated_of_cross (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (hcross2 : bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1))
    (hcross3 : bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1))
    (q : Site d) (hq : q ∉ bc3_clusterNbhd ω j₁ (L₁ + 1)) :
    ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
        (hrHD_rayPt j₁ 1) q :=
  bc3_barrier_blocks _ (bc3_clusterNbhd ω j₁ (L₁ + 1)) (hrHD_rayPt j₁ 1) q
    (bc3_clusterNbhd_adjClosed ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3)
    (bc3_mouth_mem_clusterNbhd (Nat.succ_pos L₁)) hq







def bc3_CorridorClustersDisjoint (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) : Prop :=
  bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1) ∧ bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1) ∧
  bc3_CrossDisjoint ω j₂ j₁ (L₂ + 1) (L₁ + 1) ∧ bc3_CrossDisjoint ω j₂ j₃ (L₂ + 1) (L₃ + 1) ∧
  bc3_CrossDisjoint ω j₃ j₁ (L₃ + 1) (L₁ + 1) ∧ bc3_CrossDisjoint ω j₃ j₂ (L₃ + 1) (L₂ + 1)











theorem bc3_pairwiseSeparated_of_corridorClustersDisjoint (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ := by
  obtain ⟨h12, h13, h21, h23, _h31, _h32⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · 
    have hq : (hrHD_rayPt j₂ 1 : Site d) ∉ bc3_clusterNbhd ω j₁ (L₁ + 1) := by
      have h := h12 1 le_rfl (Nat.succ_le_succ (Nat.zero_le L₂)); simpa using h
    exact bc3_mouth_separated_of_cross ω j₁ j₂ j₃ L₁ L₂ L₃ h12 h13 _ hq
  · 
    have hq : (hrHD_rayPt j₃ 1 : Site d) ∉ bc3_clusterNbhd ω j₁ (L₁ + 1) := by
      have h := h13 1 le_rfl (Nat.succ_le_succ (Nat.zero_le L₃)); simpa using h
    exact bc3_mouth_separated_of_cross ω j₁ j₂ j₃ L₁ L₂ L₃ h12 h13 _ hq
  · 
    have hq : (hrHD_rayPt j₃ 1 : Site d) ∉ bc3_clusterNbhd ω j₂ (L₂ + 1) := by
      have h := h23 1 le_rfl (Nat.succ_le_succ (Nat.zero_le L₃)); simpa using h
    have hclosed :
        bc3_AdjClosed (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (bc3_clusterNbhd ω j₂ (L₂ + 1)) := by
      rw [bc3_corridorUnion_perm2]
      exact bc3_clusterNbhd_adjClosed_gen ω j₂ j₁ j₃ L₂ L₁ L₃ h21 h23
    exact bc3_barrier_blocks _ (bc3_clusterNbhd ω j₂ (L₂ + 1)) (hrHD_rayPt j₂ 1)
      (hrHD_rayPt j₃ 1) hclosed (bc3_mouth_mem_clusterNbhd (Nat.succ_pos L₂)) hq











theorem bc3_forcedCorridorRouting_of_disjoint (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} {L₁ L₂ L₃ : ℕ} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    bc2_ForcedCorridorRouting ω :=
  ⟨j₁, j₂, j₃, L₁, L₂, L₃, ⟨hj12, hj13, hj23⟩, ⟨hi1, hi2, hi3⟩,
    bc3_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h⟩




theorem bc3_csc_of_disjoint (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} {L₁ L₂ L₃ : ℕ} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    csc_DistinctClusterCorridors ω :=
  bc2_csc_of_forcedCorridorRouting ω
    (bc3_forcedCorridorRouting_of_disjoint ω hj12 hj13 hj23 hi1 hi2 hi3 h)










lemma bc3_cluster_bot_singleton (x : Site d) (_hx : x ≠ 0) :
    cluster d (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d)))) x = {x} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨self_mem_cluster _ _, ?_⟩
  intro y hy
  rw [mem_cluster] at hy
  
  obtain ⟨w⟩ := hy
  cases w with
  | nil => rfl
  | @cons _ z _ hadj _ =>
      exfalso
      
      have hval : removeSite (0 : Site d) (⊥ : ConfigSpace (Sym2 (Site d))) s(x, z) = true :=
        hadj.2
      by_cases h0 : (0 : Site d) ∈ s(x, z)
      · rw [removeSite_apply_of_mem h0] at hval; exact Bool.false_ne_true hval
      · rw [removeSite_apply_of_notMem h0] at hval; exact Bool.false_ne_true hval






theorem bc3_crossDisjoint_bot {a c : Fin d} (hac : a ≠ c) (R L : ℕ) :
    bc3_CrossDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) a c R L := by
  intro p hp1 _ hmem
  rw [bc3_mem_clusterNbhd] at hmem
  obtain ⟨t, ⟨ht1, _⟩, hin⟩ := hmem
  
  have hat_ne : (hrHD_rayPt a (t : ℤ) : Site d) ≠ 0 := by
    rw [Ne, hrHD_rayPt_eq_zero_iff]; exact_mod_cast (by omega : (t : ℤ) ≠ 0)
  rw [bc3_cluster_bot_singleton _ hat_ne, Set.mem_singleton_iff] at hin
  
  have hcp_ne : (hrHD_rayPt c (p : ℤ) : Site d) ≠ hrHD_rayPt a (t : ℤ) :=
    hrHD_rayPt_disjoint_of_ne (Ne.symm hac) (by exact_mod_cast (by omega : (p : ℤ) ≠ 0))
  exact hcp_ne hin






theorem bc3_corridorClustersDisjoint_bot {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) (L₁ L₂ L₃ : ℕ) :
    bc3_CorridorClustersDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ :=
  ⟨bc3_crossDisjoint_bot hj12 _ _, bc3_crossDisjoint_bot hj13 _ _,
    bc3_crossDisjoint_bot (Ne.symm hj12) _ _, bc3_crossDisjoint_bot hj23 _ _,
    bc3_crossDisjoint_bot (Ne.symm hj13) _ _, bc3_crossDisjoint_bot (Ne.symm hj23) _ _⟩





theorem bc3_pairwiseSeparated_bot {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) (L₁ L₂ L₃ : ℕ) :
    bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ :=
  bc3_pairwiseSeparated_of_corridorClustersDisjoint _ j₁ j₂ j₃ L₁ L₂ L₃
    (bc3_corridorClustersDisjoint_bot hj12 hj13 hj23 L₁ L₂ L₃)

end Walls

end StatMech
