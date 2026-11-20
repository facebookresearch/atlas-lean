/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































































import Mathlib
import Code.Walls.bc3_core
import Code.Walls.bc3_barrierblocks
import Code.Walls.bc3_anchordecomp
import Code.Walls.bc6edgedichotomy
import Code.Walls.bc6corridoraxisunique
import Code.Walls.bc6raysetdef
import Code.Walls.bc6stepsameray

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}




lemma bc6_rayPt_mem_box {a : Fin d} {N p : ℕ} (hp : p ≤ N) :
    (hrHD_rayPt a (p : ℤ)) ∈ box d N := by
  rw [mem_box]; intro i
  by_cases hi : i = a
  · subst hi; rw [hrHD_rayPt_self]; simpa using hp
  · rw [hrHD_rayPt_of_ne a (p : ℤ) hi]; simp


lemma bc6_origin_mem_box {N : ℕ} : (0 : Site d) ∈ box d N := by
  rw [mem_box]; intro i; simp









lemma bc6_adj_exists_unique_diff {x y : Site d} (hadj : (hypercubicLattice d).Adj x y) :
    ∃ k : Fin d, (x k - y k).natAbs = 1 ∧ ∀ i, i ≠ k → x i = y i := by
  rw [hypercubicLattice_adj] at hadj
  have hk : ∃ k, (x k - y k).natAbs = 1 := by
    by_contra h
    push Not at h
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin d)), (x i - y i).natAbs = 0 := by
      intro i _
      have hle : (x i - y i).natAbs ≤ ∑ j, (x j - y j).natAbs :=
        Finset.single_le_sum (f := fun j => (x j - y j).natAbs) (by intros; positivity)
          (Finset.mem_univ i)
      have := h i
      omega
    rw [Finset.sum_eq_zero hzero] at hadj
    exact absurd hadj (by norm_num)
  obtain ⟨k, hk⟩ := hk
  refine ⟨k, hk, ?_⟩
  intro i hik
  have hsplit : (x k - y k).natAbs + ∑ j ∈ Finset.univ.erase k, (x j - y j).natAbs = 1 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)] at hadj
    omega
  have hi0 : (x i - y i).natAbs = 0 := by
    have hle := Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
      (s := Finset.univ.erase k) (by intros; positivity)
      (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)
    simp only at hle
    omega
  have : x i - y i = 0 := Int.natAbs_eq_zero.mp hi0
  omega






lemma bc6_rayPt_offBox_neighbor {a : Fin d} {N s : ℕ} (hs1 : 1 ≤ s) (hsN : s ≤ N) {v : Site d}
    (hadj : (hypercubicLattice d).Adj (hrHD_rayPt a (s : ℤ)) v) (hvbox : v ∉ box d N) :
    s = N ∧ v = hrHD_rayPt a ((s : ℤ) + 1) := by
  obtain ⟨k, hk1, hkrest⟩ := bc6_adj_exists_unique_diff hadj
  set u : Site d := hrHD_rayPt a (s : ℤ) with hu
  by_cases hka : k = a
  · subst hka
    have hvi : ∀ i, i ≠ k → v i = 0 := by
      intro i hi; rw [← hkrest i hi, hu, hrHD_rayPt_of_ne k (s : ℤ) hi]
    have huk : u k = (s : ℤ) := by rw [hu, hrHD_rayPt_self]
    rw [huk] at hk1
    have hcase : v k = (s : ℤ) + 1 ∨ v k = (s : ℤ) - 1 := by omega
    rcases hcase with hvk | hvk
    · have hveq : v = hrHD_rayPt k ((s : ℤ) + 1) := by
        funext i
        by_cases hi : i = k
        · subst hi; rw [hvk, hrHD_rayPt_self]
        · rw [hvi i hi, hrHD_rayPt_of_ne k ((s : ℤ) + 1) hi]
      refine ⟨?_, hveq⟩
      rw [mem_box, not_forall] at hvbox
      obtain ⟨j, hj⟩ := hvbox
      by_cases hjk : j = k
      · subst hjk
        rw [hvk] at hj
        have hnat : ((s : ℤ) + 1).natAbs = s + 1 := by omega
        rw [hnat] at hj; omega
      · rw [hvi j hjk] at hj; simp at hj
    · exfalso
      apply hvbox; rw [mem_box]
      intro i
      by_cases hi : i = k
      · subst hi; rw [hvk]
        rcases Nat.eq_zero_or_pos s with h0 | hpos
        · omega
        · have : ((s : ℤ) - 1).natAbs = s - 1 := by omega
          omega
      · rw [hvi i hi]; simp
  · exfalso
    apply hvbox; rw [mem_box]
    intro i
    by_cases hia : i = a
    · have hik : i ≠ k := by rw [hia]; exact fun h => hka h.symm
      rw [← hkrest i hik, hu, hia, hrHD_rayPt_self]
      simpa using hsN
    · by_cases hik : i = k
      · subst hik
        have hui : u i = 0 := by rw [hu, hrHD_rayPt_of_ne a (s : ℤ) hia]
        rw [hui] at hk1
        have h1 : (v i).natAbs = 1 := by simpa using hk1
        omega
      · rw [← hkrest i hik, hu, hrHD_rayPt_of_ne a (s : ℤ) hia]; simp

















lemma bc6_offBox_rho_edge_to_removeSite {N : ℕ} {G : Finset (Sym2 (Site d))}
    {ω : ConfigSpace (Sym2 (Site d))} {u v : Site d}
    (hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v)
    (hG : s(u, v) ∉ G) (hbox : s(u, v) ∉ boxEdges d N) :
    IsOpenEdge d (removeSite 0 ω) u v := by
  obtain ⟨hadj, hval⟩ := hopen
  refine ⟨hadj, ?_⟩
  have h0 : (0 : Site d) ∉ s(u, v) := bc6_origin_notMem ω N G hval
  rw [removeSite_apply_of_notMem h0] at hval ⊢
  rwa [bc6_closeBoxExcept_of_outside hG hbox] at hval












def bc6_ArmClosed (N : ℕ) (a : Fin d) (R : ℕ) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∀ u v : Site d, u ∈ bc6_offBoxCluster N a R ω →
    IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v →
    v ∈ bc6_offBoxCluster N a R ω ∨ v ∈ bc6_rayInterior a R
















lemma bc6_armRegion_adjClosed {N : ℕ} {a c₁ c₂ : Fin d} (hac1 : a ≠ c₁) (hac2 : a ≠ c₂)
    {Lc₁ Lc₂ : ℕ} {ω : ConfigSpace (Sym2 (Site d))} (G : Finset (Sym2 (Site d)))
    (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪
        hrHD_corridorEdges c₂ (Lc₂ + 1))
    (harm : bc6_ArmClosed N a (N + 1) G ω) :
    bc3_AdjClosed (removeSite 0 (bc6_closeBoxExcept N G ω)) (bc6_armRegion N a (N + 1) ω) := by
  intro u v hu hadj
  have hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v := hadj
  obtain ⟨hadjlat, hno0, hcase⟩ := bc6_edgedichotomy ω N G hopen
  rw [bc6_mem_armRegion] at hu ⊢
  rcases hu with hray | hoff
  · obtain ⟨s, ⟨hs1, _hsR⟩, hus⟩ := hray
    subst hus
    rcases hcase with hGmem | ⟨_hωopen, hnbox⟩
    · rw [hGdef, Finset.mem_union, Finset.mem_union] at hGmem
      rcases hGmem with (ha | h1) | h2
      · left
        obtain ⟨p, _hp, hpe⟩ := bc6_corridorEdge_structure ha
        have hp1 : 1 ≤ p := by
          by_contra hlt
          have hp0 : p = 0 := by omega
          subst hp0
          apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]
          exact Sym2.mem_mk_left _ _
        have hvmem : v ∈ s(hrHD_rayPt a (p : ℤ), hrHD_rayPt a ((p : ℤ) + 1)) := by
          rw [← hpe]; exact Sym2.mem_mk_right _ _
        rw [Sym2.mem_iff] at hvmem
        rcases hvmem with rfl | rfl
        · exact bc6_rayPt_mem_rayInterior hp1 (by omega)
        · have h : hrHD_rayPt a ((p : ℤ) + 1) = hrHD_rayPt a ((p + 1 : ℕ) : ℤ) := by
            push_cast; ring
          rw [h]; exact bc6_rayPt_mem_rayInterior (by omega) (by omega)
      · exfalso
        refine bc6_rayPt_notMem_crossCorridor (Ne.symm hac1)
          (q := (s : ℤ)) (by exact_mod_cast (by omega : (s : ℤ) ≠ 0)) h1 ?_
        exact Sym2.mem_mk_left _ _
      · exfalso
        refine bc6_rayPt_notMem_crossCorridor (Ne.symm hac2)
          (q := (s : ℤ)) (by exact_mod_cast (by omega : (s : ℤ) ≠ 0)) h2 ?_
        exact Sym2.mem_mk_left _ _
    · by_cases hsN : s ≤ N
      · have hubox : (hrHD_rayPt a (s : ℤ)) ∈ box d N := bc6_rayPt_mem_box hsN
        have hvbox : v ∉ box d N := by
          rcases bc6_endpoint_outside_box_of_not_boxEdge hadjlat hnbox with hb | hb
          · exact absurd hubox hb
          · exact hb
        obtain ⟨hsEq, hveq⟩ := bc6_rayPt_offBox_neighbor hs1 hsN hadjlat hvbox
        right
        have hvfar : v = hrHD_rayPt a (((N + 1 : ℕ) : ℤ)) := by
          rw [hveq, hsEq]; norm_cast
        rw [hvfar]
        exact bc6_farEnd_mem_offBoxCluster (by omega) ω
      · push Not at hsN
        have hsN1 : s = N + 1 := by omega
        have hufar : (hrHD_rayPt a (s : ℤ)) ∈ bc6_offBoxCluster N a (N + 1) ω := by
          subst hsN1
          have hfar := bc6_farEnd_mem_offBoxCluster (a := a) (N := N) (R := N + 1) (by omega) ω
          rw [show ((N + 1 : ℕ) : ℤ) = ((N : ℤ) + 1) from by push_cast; ring] at hfar
          exact hfar
        exact (harm _ v hufar hopen).symm
  · exact (harm u v hoff hopen).symm









lemma bc6_crossRayPt_notMem_armRegion {N : ℕ} {a c : Fin d} (hac : a ≠ c) {p : ℕ}
    (hp1 : 1 ≤ p) (hpR : p ≤ N + 1) (ω : ConfigSpace (Sym2 (Site d)))
    (hfar : (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω) :
    (hrHD_rayPt c (p : ℤ)) ∉ bc6_armRegion N a (N + 1) ω := by
  rw [bc6_mem_armRegion]
  rintro (hray | hoff)
  · 
    rw [bc6_mem_rayInterior] at hray
    obtain ⟨q, ⟨_hq1, _hqR⟩, heq⟩ := hray
    exact hrHD_rayPt_disjoint_of_ne (Ne.symm hac)
      (by exact_mod_cast (by omega : (p : ℤ) ≠ 0)) heq
  · 
    by_cases hpN : p ≤ N
    · have : (hrHD_rayPt c (p : ℤ)) ∉ box d N := bc6_mem_offBoxCluster_offBox hoff
      exact this (bc6_rayPt_mem_box hpN)
    · have hpEq : p = N + 1 := by omega
      apply hfar
      rwa [hpEq] at hoff










theorem bc6_crossDisjoint_of_armClosed {N : ℕ} {a c₁ c₂ : Fin d}
    (hac1 : a ≠ c₁) (hac2 : a ≠ c₂) {Lc₂ : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    (G : Finset (Sym2 (Site d)))
    (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (N + 1) ∪
        hrHD_corridorEdges c₂ (Lc₂ + 1))
    (harm : bc6_ArmClosed N a (N + 1) G ω)
    (hfar : (hrHD_rayPt c₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω) :
    bc3_CrossDisjoint (bc6_closeBoxExcept N G ω) a c₁ (N + 1) (N + 1) := by
  have hclosed := bc6_armRegion_adjClosed (Lc₁ := N) hac1 hac2 G hGdef harm
  intro p hp1 hpR hmem
  rw [bc3_mem_clusterNbhd] at hmem
  obtain ⟨t, ⟨ht1, htR⟩, hconn⟩ := hmem
  rw [mem_cluster] at hconn
  have hta : (hrHD_rayPt a (t : ℤ)) ∈ bc6_armRegion N a (N + 1) ω :=
    bc6_rayInterior_subset_armRegion (bc6_rayPt_mem_rayInterior ht1 htR)
  have hpc : (hrHD_rayPt c₁ (p : ℤ)) ∉ bc6_armRegion N a (N + 1) ω :=
    bc6_crossRayPt_notMem_armRegion hac1 hp1 hpR ω hfar
  exact bc3_barrier_blocks _ (bc6_armRegion N a (N + 1) ω) _ _ hclosed hta hpc hconn








lemma bc6_wiring_perm1 (j₁ j₂ j₃ : Fin d) (N : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ N N N =
      hrHD_corridorEdges j₁ (N + 1) ∪ hrHD_corridorEdges j₂ (N + 1) ∪
        hrHD_corridorEdges j₃ (N + 1) := by
  rw [bc3_corridorUnion]


lemma bc6_wiring_perm2 (j₁ j₂ j₃ : Fin d) (N : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ N N N =
      hrHD_corridorEdges j₂ (N + 1) ∪ hrHD_corridorEdges j₁ (N + 1) ∪
        hrHD_corridorEdges j₃ (N + 1) := by
  rw [bc3_corridorUnion]; ext e; simp only [Finset.mem_union]; tauto


lemma bc6_wiring_perm3 (j₁ j₂ j₃ : Fin d) (N : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ N N N =
      hrHD_corridorEdges j₃ (N + 1) ∪ hrHD_corridorEdges j₁ (N + 1) ∪
        hrHD_corridorEdges j₂ (N + 1) := by
  rw [bc3_corridorUnion]; ext e; simp only [Finset.mem_union]; tauto


















def bc6_CorridorArmsDisjoint (N : ℕ) (j₁ j₂ j₃ : Fin d) (ω : ConfigSpace (Sym2 (Site d))) :
    Prop :=
  let G := bc3_corridorUnion j₁ j₂ j₃ N N N
  (bc6_ArmClosed N j₁ (N + 1) G ω ∧ bc6_ArmClosed N j₂ (N + 1) G ω ∧
    bc6_ArmClosed N j₃ (N + 1) G ω) ∧
  ((hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω ∧
    (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω ∧
    (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω ∧
    (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω ∧
    (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω ∧
    (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω)












theorem bc6_corridorClustersDisjoint_of_armClosed {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    {ω : ConfigSpace (Sym2 (Site d))}
    (h : bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω) :
    bc3_CorridorClustersDisjoint
      (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N) ω) j₁ j₂ j₃ N N N := by
  obtain ⟨⟨ha1, ha2, ha3⟩, hf12, hf13, hf21, hf23, hf31, hf32⟩ := h
  set G := bc3_corridorUnion j₁ j₂ j₃ N N N with hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₃) hj12 hj13 G
      (by rw [hG, bc6_wiring_perm1]) ha1 hf12
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₂) hj13 hj12 G
      (by rw [hG]; ext e; simp only [bc3_corridorUnion, Finset.mem_union]; tauto) ha1 hf13
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₃) (Ne.symm hj12) hj23 G
      (by rw [hG, bc6_wiring_perm2]) ha2 hf21
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₁) hj23 (Ne.symm hj12) G
      (by rw [hG]; ext e; simp only [bc3_corridorUnion, Finset.mem_union]; tauto) ha2 hf23
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₂) (Ne.symm hj13) (Ne.symm hj23) G
      (by rw [hG, bc6_wiring_perm3]) ha3 hf31
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₁) (Ne.symm hj23) (Ne.symm hj13) G
      (by rw [hG]; ext e; simp only [bc3_corridorUnion, Finset.mem_union]; tauto) ha3 hf32










theorem bc6_pairwiseSeparated_of_armClosed {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    {ω : ConfigSpace (Sym2 (Site d))}
    (h : bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω) :
    bc2_PairwiseSeparated
      (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N) ω) j₁ j₂ j₃ N N N :=
  bc3_pairwiseSeparated_of_corridorClustersDisjoint _ j₁ j₂ j₃ N N N
    (bc6_corridorClustersDisjoint_of_armClosed hj12 hj13 hj23 h)











lemma bc6_bot_no_adj {S : Set (Site d)} (x y : S) :
    ¬ (openSubgraphInduce d (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d)))) S).Adj x y := by
  intro hadj
  rw [openSubgraphInduce_adj, openSubgraph_adj] at hadj
  have hval := hadj.2
  by_cases h0 : (0 : Site d) ∈ s((x : Site d), (y : Site d))
  · rw [removeSite_apply_of_mem h0] at hval; exact Bool.false_ne_true hval
  · rw [removeSite_apply_of_notMem h0] at hval; exact Bool.false_ne_true hval


lemma bc6_bot_walk_eq {S : Set (Site d)} {x y : S}
    (w : (openSubgraphInduce d (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d)))) S).Walk x y) :
    x = y := by
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (bc6_bot_no_adj _ _)



lemma bc6_offBoxCluster_bot_eq {N : ℕ} {a : Fin d} {R : ℕ} {x : Site d}
    (hx : x ∈ bc6_offBoxCluster N a R (⊥ : ConfigSpace (Sym2 (Site d)))) :
    x = hrHD_rayPt a (R : ℤ) := by
  obtain ⟨_hxS, _hoS, hconn⟩ := hx
  obtain ⟨w⟩ := hconn
  exact congrArg Subtype.val (bc6_bot_walk_eq w).symm





theorem bc6_armClosed_bot {N : ℕ} {a c₁ c₂ : Fin d} (hac1 : a ≠ c₁) (hac2 : a ≠ c₂)
    {Lc₁ Lc₂ : ℕ} (G : Finset (Sym2 (Site d)))
    (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪
        hrHD_corridorEdges c₂ (Lc₂ + 1)) :
    bc6_ArmClosed N a (N + 1) G (⊥ : ConfigSpace (Sym2 (Site d))) := by
  intro u v hu hopen
  have hueq : u = hrHD_rayPt a ((N + 1 : ℕ) : ℤ) := bc6_offBoxCluster_bot_eq hu
  obtain ⟨_hadjlat, hno0, hcase⟩ := bc6_edgedichotomy (⊥ : ConfigSpace (Sym2 (Site d))) N G hopen
  rcases hcase with hGmem | ⟨hωopen, _⟩
  · rw [hGdef, Finset.mem_union, Finset.mem_union] at hGmem
    right
    rcases hGmem with (ha | h1) | h2
    · obtain ⟨p, _hp, hpe⟩ := bc6_corridorEdge_structure ha
      have hp1 : 1 ≤ p := by
        by_contra hlt
        have hp0 : p = 0 := by omega
        subst hp0
        apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]
        exact Sym2.mem_mk_left _ _
      have hvmem : v ∈ s(hrHD_rayPt a (p : ℤ), hrHD_rayPt a ((p : ℤ) + 1)) := by
        rw [← hpe]; exact Sym2.mem_mk_right _ _
      rw [Sym2.mem_iff] at hvmem
      rcases hvmem with rfl | rfl
      · exact bc6_rayPt_mem_rayInterior hp1 (by omega)
      · have h : hrHD_rayPt a ((p : ℤ) + 1) = hrHD_rayPt a ((p + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h]; exact bc6_rayPt_mem_rayInterior (by omega) (by omega)
    · exfalso
      refine bc6_rayPt_notMem_crossCorridor (Ne.symm hac1)
        (q := ((N + 1 : ℕ) : ℤ)) (by exact_mod_cast (by omega : ((N + 1 : ℕ) : ℤ) ≠ 0)) h1 ?_
      rw [← hueq]; exact Sym2.mem_mk_left _ _
    · exfalso
      refine bc6_rayPt_notMem_crossCorridor (Ne.symm hac2)
        (q := ((N + 1 : ℕ) : ℤ)) (by exact_mod_cast (by omega : ((N + 1 : ℕ) : ℤ) ≠ 0)) h2 ?_
      rw [← hueq]; exact Sym2.mem_mk_left _ _
  · exact absurd hωopen (by simp)




theorem bc6_crossFarEnd_bot {N : ℕ} {a c : Fin d} (hac : a ≠ c) :
    (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∉
      bc6_offBoxCluster N a (N + 1) (⊥ : ConfigSpace (Sym2 (Site d))) := by
  intro hmem
  have heq : (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) = hrHD_rayPt a ((N + 1 : ℕ) : ℤ) :=
    bc6_offBoxCluster_bot_eq hmem
  exact hrHD_rayPt_disjoint_of_ne (Ne.symm hac)
    (by exact_mod_cast (by omega : ((N + 1 : ℕ) : ℤ) ≠ 0)) heq




theorem bc6_corridorArmsDisjoint_bot {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) :
    bc6_CorridorArmsDisjoint N j₁ j₂ j₃ (⊥ : ConfigSpace (Sym2 (Site d))) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bc6_armClosed_bot hj12 hj13 _ (bc6_wiring_perm1 j₁ j₂ j₃ N)
  · exact bc6_armClosed_bot (Ne.symm hj12) hj23 _ (bc6_wiring_perm2 j₁ j₂ j₃ N)
  · exact bc6_armClosed_bot (Ne.symm hj13) (Ne.symm hj23) _ (bc6_wiring_perm3 j₁ j₂ j₃ N)
  · exact bc6_crossFarEnd_bot hj12
  · exact bc6_crossFarEnd_bot hj13
  · exact bc6_crossFarEnd_bot (Ne.symm hj12)
  · exact bc6_crossFarEnd_bot hj23
  · exact bc6_crossFarEnd_bot (Ne.symm hj13)
  · exact bc6_crossFarEnd_bot (Ne.symm hj23)




theorem bc6_corridorClustersDisjoint_closeBox_bot {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) :
    bc3_CorridorClustersDisjoint
      (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N)
        (⊥ : ConfigSpace (Sym2 (Site d)))) j₁ j₂ j₃ N N N :=
  bc6_corridorClustersDisjoint_of_armClosed hj12 hj13 hj23
    (bc6_corridorArmsDisjoint_bot hj12 hj13 hj23)




theorem bc6_pairwiseSeparated_closeBox_bot {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) :
    bc2_PairwiseSeparated
      (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N)
        (⊥ : ConfigSpace (Sym2 (Site d)))) j₁ j₂ j₃ N N N :=
  bc6_pairwiseSeparated_of_armClosed hj12 hj13 hj23
    (bc6_corridorArmsDisjoint_bot hj12 hj13 hj23)

end Walls

end StatMech
