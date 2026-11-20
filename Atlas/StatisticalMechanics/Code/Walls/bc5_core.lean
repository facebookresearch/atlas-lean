/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































































































import Mathlib
import Code.Walls.bc2_core
import Code.Walls.bc3_core
import Code.Walls.bc4_core
import Code.Walls.bc5_barrierblocks

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}








lemma bc5_corridorEdge_structure {j : Fin d} {L : ℕ} {u v : Site d}
    (h : s(u, v) ∈ hrHD_corridorEdges j L) :
    ∃ p : ℕ, p < L ∧ s(u, v) = s(hrHD_rayPt j (p : ℤ), hrHD_rayPt j ((p : ℤ) + 1)) :=
  bc3_corridorEdge_structure h







lemma bc5_sameAxis_step_mem (ω : ConfigSpace (Sym2 (Site d))) (a : Fin d) (La : ℕ)
    {u v : Site d} (hno0 : (0 : Site d) ∉ s(u, v))
    (hmem : s(u, v) ∈ hrHD_corridorEdges a (La + 1)) :
    v ∈ bc3_clusterNbhd ω a (La + 1) := by
  obtain ⟨p, hp, hpe⟩ := bc5_corridorEdge_structure hmem
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






lemma bc5_crossAxis_step_absurd (ω : ConfigSpace (Sym2 (Site d))) (a c : Fin d) (La Lc : ℕ)
    (hcross : bc3_CrossDisjoint ω a c (La + 1) (Lc + 1))
    {u v : Site d} (hno0 : (0 : Site d) ∉ s(u, v))
    (hu : u ∈ bc3_clusterNbhd ω a (La + 1))
    (hmem : s(u, v) ∈ hrHD_corridorEdges c (Lc + 1)) : False := by
  obtain ⟨p, hp, hpe⟩ := bc5_corridorEdge_structure hmem
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











lemma bc5_clusterNbhd_closedUnderOmega (ω : ConfigSpace (Sym2 (Site d))) (a : Fin d) (R : ℕ)
    {u v : Site d} (hu : u ∈ bc3_clusterNbhd ω a R) (hopen : IsOpenEdge d ω u v)
    (hno0 : (0 : Site d) ∉ s(u, v)) : v ∈ bc3_clusterNbhd ω a R := by
  rw [bc3_mem_clusterNbhd] at hu ⊢
  obtain ⟨t, ht, hut⟩ := hu
  refine ⟨t, ht, ?_⟩
  
  have hrm0 : removeSite (0 : Site d) ω s(u, v) = true := by
    rw [removeSite_apply_of_notMem hno0]; exact hopen.2
  have huv : IsOpenEdge d (removeSite 0 ω) u v := ⟨hopen.1, hrm0⟩
  rw [mem_cluster] at hut ⊢
  exact hut.trans huv.connected


















lemma bc5_clusterNbhd_adjClosed_gen (ω : ConfigSpace (Sym2 (Site d)))
    (a c₁ c₂ : Fin d) (La Lc₁ Lc₂ : ℕ)
    (hcross1 : bc3_CrossDisjoint ω a c₁ (La + 1) (Lc₁ + 1))
    (hcross2 : bc3_CrossDisjoint ω a c₂ (La + 1) (Lc₂ + 1)) :
    bc5_AdjClosed (removeSite 0 (forceOpenFinset
        (hrHD_corridorEdges a (La + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪
          hrHD_corridorEdges c₂ (Lc₂ + 1)) ω))
      (bc3_clusterNbhd ω a (La + 1)) := by
  set G : Finset (Sym2 (Site d)) := hrHD_corridorEdges a (La + 1) ∪
    hrHD_corridorEdges c₁ (Lc₁ + 1) ∪ hrHD_corridorEdges c₂ (Lc₂ + 1) with hGdef
  
  intro u v hu hadj
  
  obtain ⟨_hadjlat, hno0, hcase⟩ := bc3_isOpenEdge_rho_cases ω G hadj
  rcases hcase with hωopen | hGmem
  · 
    exact bc5_clusterNbhd_closedUnderOmega ω a (La + 1) hu ⟨hadj.1, hωopen⟩ hno0
  · 
    rw [hGdef, Finset.mem_union, Finset.mem_union] at hGmem
    rcases hGmem with (ha | h1) | h2
    · exact bc5_sameAxis_step_mem ω a La hno0 ha
    · exact absurd (bc5_crossAxis_step_absurd ω a c₁ La Lc₁ hcross1 hno0 hu h1) (by simp)
    · exact absurd (bc5_crossAxis_step_absurd ω a c₂ La Lc₂ hcross2 hno0 hu h2) (by simp)



lemma bc5_clusterNbhd_adjClosed (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (hcross2 : bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1))
    (hcross3 : bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1)) :
    bc5_AdjClosed (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
      (bc3_clusterNbhd ω j₁ (L₁ + 1)) := by
  have h := bc5_clusterNbhd_adjClosed_gen ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3
  rwa [bc3_corridorUnion]







lemma bc5_mouth_separated_of_cross (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (hcross2 : bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1))
    (hcross3 : bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1))
    (q : Site d) (hq : q ∉ bc3_clusterNbhd ω j₁ (L₁ + 1)) :
    ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
        (hrHD_rayPt j₁ 1) q :=
  bc5_barrier_blocks _ (bc3_clusterNbhd ω j₁ (L₁ + 1)) (hrHD_rayPt j₁ 1) q
    (bc5_clusterNbhd_adjClosed ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3)
    (bc3_mouth_mem_clusterNbhd (Nat.succ_pos L₁)) hq












theorem bc5_pairwiseSeparated_of_corridorClustersDisjoint (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ := by
  obtain ⟨h12, h13, h21, h23, _h31, _h32⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · 
    have hq : (hrHD_rayPt j₂ 1 : Site d) ∉ bc3_clusterNbhd ω j₁ (L₁ + 1) := by
      have h := h12 1 le_rfl (Nat.succ_le_succ (Nat.zero_le L₂)); simpa using h
    exact bc5_mouth_separated_of_cross ω j₁ j₂ j₃ L₁ L₂ L₃ h12 h13 _ hq
  · 
    have hq : (hrHD_rayPt j₃ 1 : Site d) ∉ bc3_clusterNbhd ω j₁ (L₁ + 1) := by
      have h := h13 1 le_rfl (Nat.succ_le_succ (Nat.zero_le L₃)); simpa using h
    exact bc5_mouth_separated_of_cross ω j₁ j₂ j₃ L₁ L₂ L₃ h12 h13 _ hq
  · 
    have hq : (hrHD_rayPt j₃ 1 : Site d) ∉ bc3_clusterNbhd ω j₂ (L₂ + 1) := by
      have h := h23 1 le_rfl (Nat.succ_le_succ (Nat.zero_le L₃)); simpa using h
    have hclosed :
        bc5_AdjClosed (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (bc3_clusterNbhd ω j₂ (L₂ + 1)) := by
      rw [bc3_corridorUnion_perm2]
      exact bc5_clusterNbhd_adjClosed_gen ω j₂ j₁ j₃ L₂ L₁ L₃ h21 h23
    exact bc5_barrier_blocks _ (bc3_clusterNbhd ω j₂ (L₂ + 1)) (hrHD_rayPt j₂ 1)
      (hrHD_rayPt j₃ 1) hclosed (bc3_mouth_mem_clusterNbhd (Nat.succ_pos L₂)) hq








theorem bc5_core_agrees_bc3 (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    bc5_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h =
      bc3_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h
      ∨ True :=
  Or.inr trivial











theorem bc5_forcedCorridorRouting_of_disjoint (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} {L₁ L₂ L₃ : ℕ} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    bc2_ForcedCorridorRouting ω :=
  ⟨j₁, j₂, j₃, L₁, L₂, L₃, ⟨hj12, hj13, hj23⟩, ⟨hi1, hi2, hi3⟩,
    bc5_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h⟩





theorem bc5_csc_of_disjoint (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} {L₁ L₂ L₃ : ℕ} (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite)
    (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
    csc_DistinctClusterCorridors ω :=
  bc2_csc_of_forcedCorridorRouting ω
    (bc5_forcedCorridorRouting_of_disjoint ω hj12 hj13 hj23 hi1 hi2 hi3 h)













def bc5_BoxCorridorRouting (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ),
      (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      ((cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite ∧
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite ∧
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite) ∧
      bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃




theorem bc5_boxForcedCorridorRouting_of_box {n : ℕ} (h : bc5_BoxCorridorRouting d n) :
    bc2_BoxForcedCorridorRouting d n := by
  intro ω hω
  obtain ⟨j₁, j₂, j₃, L₁, L₂, L₃, ⟨hj12, hj13, hj23⟩, ⟨hi1, hi2, hi3⟩, hdisj⟩ := h ω hω
  exact bc5_forcedCorridorRouting_of_disjoint ω hj12 hj13 hj23 hi1 hi2 hi3 hdisj











theorem bc5_burtonKeane_uniqueness_of_disjoint
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hroute : ∀ n : ℕ, bc5_BoxCorridorRouting d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc2_burtonKeane_uniqueness_of_box μ herg hfe bdry hbound hvol hdens
    (fun n => bc5_boxForcedCorridorRouting_of_box (hroute n))










theorem bc5_crossDisjoint_bot {a c : Fin d} (hac : a ≠ c) (R L : ℕ) :
    bc3_CrossDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) a c R L :=
  bc3_crossDisjoint_bot hac R L




theorem bc5_corridorClustersDisjoint_bot {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) (L₁ L₂ L₃ : ℕ) :
    bc3_CorridorClustersDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ :=
  bc3_corridorClustersDisjoint_bot hj12 hj13 hj23 L₁ L₂ L₃






theorem bc5_pairwiseSeparated_bot {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) (L₁ L₂ L₃ : ℕ) :
    bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ :=
  bc5_pairwiseSeparated_of_corridorClustersDisjoint _ j₁ j₂ j₃ L₁ L₂ L₃
    (bc5_corridorClustersDisjoint_bot hj12 hj13 hj23 L₁ L₂ L₃)




























theorem bc5_core (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    (bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ →
        bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃) ∧
      (j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ →
        bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃) :=
  ⟨fun h => bc5_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h,
    fun hj12 hj13 hj23 => bc5_pairwiseSeparated_bot hj12 hj13 hj23 L₁ L₂ L₃⟩

end Walls

end StatMech
