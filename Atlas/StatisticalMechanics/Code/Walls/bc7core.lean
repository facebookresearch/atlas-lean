/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































































import Mathlib
import Code.Walls.bc6core
import Code.Walls.bc7offboxedgeagree
import Code.Walls.bc7crossaxisunique
import Code.Walls.bc7rayPtoffboxneighbor
import Code.Walls.bc7nocrossing
import Code.Walls.bc7offboxsubsetcluster
import Code.Walls.bc7offboxclusterbasics
import Code.Walls.bc7distinctwitnessclusters

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}
















def bc6_ReentryOnRay (N : ℕ) (a : Fin d) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∀ u v : Site d, u ∈ bc6_offBoxCluster N a (N + 1) ω →
    IsOpenEdge d (removeSite 0 ω) u v →
    s(u, v) ∉ G → s(u, v) ∉ boxEdges d N → v ∈ box d N →
    v ∈ bc6_rayInterior a (N + 1)
















theorem bc7_armClosed_corridorEdge {N : ℕ} {a c₁ c₂ : Fin d} (hac1 : a ≠ c₁) (hac2 : a ≠ c₂)
    {ω : ConfigSpace (Sym2 (Site d))} {G : Finset (Sym2 (Site d))}
    (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (N + 1) ∪
        hrHD_corridorEdges c₂ (N + 1))
    (hf1 : (hrHD_rayPt c₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω)
    (hf2 : (hrHD_rayPt c₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω)
    {u v : Site d} (hu : u ∈ bc6_offBoxCluster N a (N + 1) ω)
    (hno0 : (0 : Site d) ∉ s(u, v)) (hGmem : s(u, v) ∈ G) :
    v ∈ bc6_rayInterior a (N + 1) := by
  have huoff : u ∉ box d N := bc6_mem_offBoxCluster_offBox hu
  
  
  
  have hcross : ∀ {c : Fin d},
      (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω →
      s(u, v) ∈ hrHD_corridorEdges c (N + 1) → False := by
    intro c hf hmem
    obtain ⟨q, hq, hqe⟩ := bc6_corridorEdge_structure hmem
    have humem : u ∈ s(hrHD_rayPt c (q : ℤ), hrHD_rayPt c ((q : ℤ) + 1)) := by
      rw [← hqe]; exact Sym2.mem_mk_left _ _
    rw [Sym2.mem_iff] at humem
    
    
    rcases humem with hua | hua
    · 
      exact huoff (hua ▸ bc6_rayPt_mem_box (by omega))
    · 
      
      by_cases hq1 : q + 1 ≤ N
      · refine huoff ?_
        have hcast : hrHD_rayPt c ((q : ℤ) + 1) = hrHD_rayPt c ((q + 1 : ℕ) : ℤ) := by
          push_cast; ring
        rw [hua, hcast]; exact bc6_rayPt_mem_box hq1
      · apply hf
        have hqN : q + 1 = N + 1 := by omega
        have hcast : hrHD_rayPt c ((q : ℤ) + 1) = hrHD_rayPt c ((N + 1 : ℕ) : ℤ) := by
          have : (q : ℤ) + 1 = ((N + 1 : ℕ) : ℤ) := by exact_mod_cast by omega
          rw [this]
        rw [← hcast, ← hua]; exact hu
  rw [hGdef, Finset.mem_union, Finset.mem_union] at hGmem
  rcases hGmem with (ha | h1) | h2
  · 
    obtain ⟨p, hp, hpe⟩ := bc6_corridorEdge_structure ha
    have hp1 : 1 ≤ p := by
      by_contra hlt
      have hp0 : p = 0 := by omega
      subst hp0
      apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]
      exact Sym2.mem_mk_left _ _
    have humem : u ∈ s(hrHD_rayPt a (p : ℤ), hrHD_rayPt a ((p : ℤ) + 1)) := by
      rw [← hpe]; exact Sym2.mem_mk_left _ _
    have hvmem : v ∈ s(hrHD_rayPt a (p : ℤ), hrHD_rayPt a ((p : ℤ) + 1)) := by
      rw [← hpe]; exact Sym2.mem_mk_right _ _
    rw [Sym2.mem_iff] at humem
    have hpN : p = N := by
      by_contra hne
      have hpltN1 : p < N + 1 := hp
      rcases humem with hua | hua
      · exact huoff (hua ▸ bc6_rayPt_mem_box (by omega))
      · refine huoff ?_
        have hcast : hrHD_rayPt a ((p : ℤ) + 1) = hrHD_rayPt a ((p + 1 : ℕ) : ℤ) := by
          push_cast; ring
        rw [hua, hcast]; exact bc6_rayPt_mem_box (by omega)
    rw [Sym2.mem_iff] at hvmem
    subst hpN
    rcases hvmem with rfl | rfl
    · exact bc6_rayPt_mem_rayInterior hp1 (by omega)
    · have hcast : hrHD_rayPt a ((p : ℤ) + 1) = hrHD_rayPt a ((p + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [hcast]; exact bc6_rayPt_mem_rayInterior (by omega) (by omega)
  · exact absurd h1 (fun h => hcross hf1 h)
  · exact absurd h2 (fun h => hcross hf2 h)


















theorem bc7_armClosed_offBoxStep {N : ℕ} {a : Fin d} {G : Finset (Sym2 (Site d))}
    {ω : ConfigSpace (Sym2 (Site d))} {u v : Site d}
    (hu : u ∈ bc6_offBoxCluster N a (N + 1) ω)
    (hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v)
    (hG : s(u, v) ∉ G) (hbox : s(u, v) ∉ boxEdges d N) (hvoff : v ∉ box d N) :
    v ∈ bc6_offBoxCluster N a (N + 1) ω := by
  
  have hopenω : IsOpenEdge d (removeSite 0 ω) u v := bc7_offBox_rho_edge_agree hopen hG hbox
  
  exact clusterWithin_closed hu hvoff hopenω





















theorem bc7_armClosed_of_reentryOnRay {N : ℕ} {a c₁ c₂ : Fin d} (hac1 : a ≠ c₁) (hac2 : a ≠ c₂)
    {ω : ConfigSpace (Sym2 (Site d))} {G : Finset (Sym2 (Site d))}
    (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (N + 1) ∪
        hrHD_corridorEdges c₂ (N + 1))
    (hf1 : (hrHD_rayPt c₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω)
    (hf2 : (hrHD_rayPt c₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω)
    (hre : bc6_ReentryOnRay N a G ω) :
    bc6_ArmClosed N a (N + 1) G ω := by
  intro u v hu hopen
  
  obtain ⟨hadj, hno0, hcase⟩ := bc6_edgedichotomy ω N G hopen
  rcases hcase with hGmem | ⟨_hωopen, hnb⟩
  · 
    exact Or.inr (bc7_armClosed_corridorEdge hac1 hac2 hGdef hf1 hf2 hu hno0 hGmem)
  · 
    
    by_cases hGe : s(u, v) ∈ G
    · exact Or.inr (bc7_armClosed_corridorEdge hac1 hac2 hGdef hf1 hf2 hu hno0 hGe)
    · 
      have hopenω : IsOpenEdge d (removeSite 0 ω) u v := bc7_offBox_rho_edge_agree hopen hGe hnb
      by_cases hvbox : v ∈ box d N
      · 
        exact Or.inr (hre u v hu hopenω hGe hnb hvbox)
      · 
        exact Or.inl (bc7_armClosed_offBoxStep hu hopen hGe hnb hvbox)

















theorem bc7_crossFarEnd_of_distinctCutClusters {N : ℕ} {a c : Fin d}
    {ω : ConfigSpace (Sym2 (Site d))}
    (hne : cluster d (removeSite 0 ω) (hrHD_rayPt a ((N + 1 : ℕ) : ℤ)) ≠
        cluster d (removeSite 0 ω) (hrHD_rayPt c ((N + 1 : ℕ) : ℤ))) :
    (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω := by
  intro hmem
  
  have hin : (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∈
      cluster d (removeSite 0 ω) (hrHD_rayPt a ((N + 1 : ℕ) : ℤ)) :=
    bc7_offBoxCluster_subset_cluster (N := N) (a := a) (R := N + 1) ω hmem
  
  exact hne (cluster_eq_of_connected (mem_cluster.mp hin))







theorem bc7_sixCrossFarEnds_of_distinctCutClusters {N : ℕ} {j₁ j₂ j₃ : Fin d}
    {ω : ConfigSpace (Sym2 (Site d))}
    (h12 : cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ≠
        cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)))
    (h13 : cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ≠
        cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)))
    (h23 : cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ≠
        cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ))) :
    (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω ∧
    (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω ∧
    (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω ∧
    (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω ∧
    (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω ∧
    (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω :=
  ⟨bc7_crossFarEnd_of_distinctCutClusters h12,
   bc7_crossFarEnd_of_distinctCutClusters h13,
   bc7_crossFarEnd_of_distinctCutClusters h12.symm,
   bc7_crossFarEnd_of_distinctCutClusters h23,
   bc7_crossFarEnd_of_distinctCutClusters h13.symm,
   bc7_crossFarEnd_of_distinctCutClusters h23.symm⟩


















theorem bc7_corridorArmsDisjoint_of_reentryOnRay {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    {ω : ConfigSpace (Sym2 (Site d))}
    (hr1 : bc6_ReentryOnRay N j₁ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
    (hr2 : bc6_ReentryOnRay N j₂ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
    (hr3 : bc6_ReentryOnRay N j₃ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
    (hf12 : (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω)
    (hf13 : (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω)
    (hf21 : (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω)
    (hf23 : (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω)
    (hf31 : (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω)
    (hf32 : (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω) :
    bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω := by
  refine ⟨⟨?_, ?_, ?_⟩, hf12, hf13, hf21, hf23, hf31, hf32⟩
  · 
    exact bc7_armClosed_of_reentryOnRay (c₁ := j₂) (c₂ := j₃) hj12 hj13
      (bc6_wiring_perm1 j₁ j₂ j₃ N) hf12 hf13 hr1
  · 
    exact bc7_armClosed_of_reentryOnRay (c₁ := j₁) (c₂ := j₃) (Ne.symm hj12) hj23
      (bc6_wiring_perm2 j₁ j₂ j₃ N) hf21 hf23 hr2
  · 
    exact bc7_armClosed_of_reentryOnRay (c₁ := j₁) (c₂ := j₂) (Ne.symm hj13) (Ne.symm hj23)
      (bc6_wiring_perm3 j₁ j₂ j₃ N) hf31 hf32 hr3














theorem bc7_corridorArmsDisjoint_of_reentryOnRay_and_distinct {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    {ω : ConfigSpace (Sym2 (Site d))}
    (hr1 : bc6_ReentryOnRay N j₁ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
    (hr2 : bc6_ReentryOnRay N j₂ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
    (hr3 : bc6_ReentryOnRay N j₃ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
    (h12 : cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ≠
        cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)))
    (h13 : cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ≠
        cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)))
    (h23 : cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ≠
        cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ))) :
    bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω := by
  obtain ⟨hf12, hf13, hf21, hf23, hf31, hf32⟩ :=
    bc7_sixCrossFarEnds_of_distinctCutClusters h12 h13 h23
  exact bc7_corridorArmsDisjoint_of_reentryOnRay hj12 hj13 hj23 hr1 hr2 hr3
    hf12 hf13 hf21 hf23 hf31 hf32











theorem bc7_reentryOnRay_bot {N : ℕ} {a : Fin d} (G : Finset (Sym2 (Site d))) :
    bc6_ReentryOnRay N a G (⊥ : ConfigSpace (Sym2 (Site d))) := by
  intro u v hu hopen _ _ _
  
  
  exfalso
  obtain ⟨_hadj, hval⟩ := hopen
  have hbot : removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d))) s(u, v) = false := by
    by_cases h0 : (0 : Site d) ∈ s(u, v)
    · rw [removeSite_apply_of_mem h0]
    · rw [removeSite_apply_of_notMem h0]; rfl
  rw [hbot] at hval
  exact Bool.false_ne_true hval




theorem bc7_corridorArmsDisjoint_bot {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) :
    bc6_CorridorArmsDisjoint N j₁ j₂ j₃ (⊥ : ConfigSpace (Sym2 (Site d))) :=
  bc6_corridorArmsDisjoint_bot hj12 hj13 hj23




theorem bc7_corridorClustersDisjoint_bot {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) :
    bc3_CorridorClustersDisjoint
      (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N)
        (⊥ : ConfigSpace (Sym2 (Site d)))) j₁ j₂ j₃ N N N :=
  bc6_corridorClustersDisjoint_closeBox_bot hj12 hj13 hj23

end Walls

end StatMech
