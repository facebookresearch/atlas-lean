/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.Walls.bc12core
import Code.Walls.bc21trifurc
import Code.Walls.bc19menger
import Code.Walls.bc20mengerroute
import Code.Percolation.TrifurcationConstruction
import Code.Percolation.MengerRouting
import Code.Percolation.BoxMengerAttachment

open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech.Walls

variable {d : ℕ}















theorem bc23_corridor_of_walk (G : Finset (Sym2 (Site d))) {a b : Site d}
    (w : (hypercubicLattice d).Walk a b)
    (hedges : ∀ e ∈ w.edges, e ∈ G)
    (h0 : (0 : Site d) ∉ w.support) :
    Relation.ReflTransGen (CorridorStep G) a b := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | @cons u v t hadj p ih =>
      rw [Walk.support_cons, List.mem_cons] at h0
      push Not at h0
      obtain ⟨hu0, hrest⟩ := h0
      have hv0 : v ≠ 0 := fun hv => hrest (hv ▸ p.start_mem_support)
      
      have hmemG : s(u, v) ∈ G := hedges s(u, v) (by rw [Walk.edges_cons]; exact List.mem_cons_self ..)
      
      have hne0 : (0 : Site d) ∉ s(u, v) := by
        rw [Sym2.mem_iff]; push Not
        exact ⟨fun h => hu0 h, fun h => hv0 h.symm⟩
      
      have hstep : CorridorStep G u v := ⟨hadj, hmemG, hne0⟩
      
      have htail : Relation.ReflTransGen (CorridorStep G) v t := by
        apply ih
        · intro e he; exact hedges e (by rw [Walk.edges_cons]; exact List.mem_cons_of_mem _ he)
        · exact hrest
      exact Relation.ReflTransGen.head hstep htail









noncomputable def bc23_walkEdges {a b : Site d} (w : (hypercubicLattice d).Walk a b) :
    Finset (Sym2 (Site d)) :=
  w.edges.toFinset

theorem bc23_mem_walkEdges {a b : Site d} (w : (hypercubicLattice d).Walk a b)
    {e : Sym2 (Site d)} (he : e ∈ w.edges) : e ∈ bc23_walkEdges w := by
  rw [bc23_walkEdges, List.mem_toFinset]; exact he



theorem bc23_corridor_of_walk_subset (G : Finset (Sym2 (Site d))) {a b : Site d}
    (w : (hypercubicLattice d).Walk a b)
    (hsub : bc23_walkEdges w ⊆ G) (h0 : (0 : Site d) ∉ w.support) :
    Relation.ReflTransGen (CorridorStep G) a b :=
  bc23_corridor_of_walk G w (fun e he => hsub (bc23_mem_walkEdges w he)) h0














theorem bc23_mengerCore_of_corridors (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) (w₁ w₂ w₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hcor : Relation.ReflTransGen (CorridorStep G) a₁ w₁ ∧
      Relation.ReflTransGen (CorridorStep G) a₂ w₂ ∧
      Relation.ReflTransGen (CorridorStep G) a₃ w₃)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite)
    (hdist : cluster d (removeSite 0 (forceOpenFinset G ω)) w₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₂ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) w₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₃ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) w₂
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₃) :
    MengerCore ω :=
  ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, hcor, hinf, hdist⟩












theorem bc23_removeSite_le_forceOpen (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) :
    removeSite 0 ω ≤ removeSite 0 (forceOpenFinset G ω) := by
  have h := bma_removeSite_forceOpen_mono_sub (ω := ω) (Wⱼ := (∅ : Finset (Sym2 (Site d))))
    (W := G) (Finset.empty_subset G)
  rwa [mng_forceOpenFinset_empty] at h





theorem bc23_forcedCluster_infinite_of_originFree (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (b : Site d)
    (h0 : (0 : Site d) ∉ cluster d ω b) (hinf : (cluster d ω b).Infinite) :
    (cluster d (removeSite 0 (forceOpenFinset G ω)) b).Infinite :=
  (bc20_removeSite_infinite_of_originFree ω b h0 hinf).mono
    (cluster_mono (bc23_removeSite_le_forceOpen ω G) b)
























theorem bc23_mengerCore_of_latticeCorridors (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (w₁ : (hypercubicLattice d).Walk a₁ b₁) (w₂ : (hypercubicLattice d).Walk a₂ b₂)
    (w₃ : (hypercubicLattice d).Walk a₃ b₃)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hw0₁ : (0 : Site d) ∉ w₁.support) (hw0₂ : (0 : Site d) ∉ w₂.support)
    (hw0₃ : (0 : Site d) ∉ w₃.support)
    (h0 : (0 : Site d) ∉ cluster d ω b₁ ∧ (0 : Site d) ∉ cluster d ω b₂ ∧
      (0 : Site d) ∉ cluster d ω b₃)
    (hinf : (cluster d ω b₁).Infinite ∧ (cluster d ω b₂).Infinite ∧ (cluster d ω b₃).Infinite)
    (S₁ S₂ S₃ : Set (Site d))
    (hb₁ : b₁ ∈ S₁) (hb₂ : b₂ ∈ S₂) (hb₃ : b₃ ∈ S₃)
    (hcl₁ : ∀ u v, u ∈ S₁ →
      (openSubgraph d (removeSite 0 (forceOpenFinset
        (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₁)
    (hcl₂ : ∀ u v, u ∈ S₂ →
      (openSubgraph d (removeSite 0 (forceOpenFinset
        (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₂)
    (hcl₃ : ∀ u v, u ∈ S₃ →
      (openSubgraph d (removeSite 0 (forceOpenFinset
        (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₃)
    (hd12 : Disjoint S₁ S₂) (hd13 : Disjoint S₁ S₃) (hd23 : Disjoint S₂ S₃) :
    MengerCore ω := by
  classical
  set G : Finset (Sym2 (Site d)) :=
    bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃ with hG
  set ϱ := removeSite 0 (forceOpenFinset G ω) with hϱ
  
  have hcor₁ : Relation.ReflTransGen (CorridorStep G) a₁ b₁ :=
    bc23_corridor_of_walk_subset G w₁
      (by intro e he; rw [hG, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl he)) hw0₁
  have hcor₂ : Relation.ReflTransGen (CorridorStep G) a₂ b₂ :=
    bc23_corridor_of_walk_subset G w₂
      (by intro e he; rw [hG, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inr he)) hw0₂
  have hcor₃ : Relation.ReflTransGen (CorridorStep G) a₃ b₃ :=
    bc23_corridor_of_walk_subset G w₃
      (by intro e he; rw [hG, Finset.mem_union]; exact Or.inr he) hw0₃
  
  have hinf₁ : (cluster d ϱ b₁).Infinite := bc23_forcedCluster_infinite_of_originFree ω G b₁ h0.1 hinf.1
  have hinf₂ : (cluster d ϱ b₂).Infinite := bc23_forcedCluster_infinite_of_originFree ω G b₂ h0.2.1 hinf.2.1
  have hinf₃ : (cluster d ϱ b₃).Infinite := bc23_forcedCluster_infinite_of_originFree ω G b₃ h0.2.2 hinf.2.2
  
  have hsub₁ : cluster d ϱ b₁ ⊆ S₁ := cluster_subset_of_adjClosed ϱ S₁ b₁ hb₁ hcl₁
  have hsub₂ : cluster d ϱ b₂ ⊆ S₂ := cluster_subset_of_adjClosed ϱ S₂ b₂ hb₂ hcl₂
  have hsub₃ : cluster d ϱ b₃ ⊆ S₃ := cluster_subset_of_adjClosed ϱ S₃ b₃ hb₃ hcl₃
  exact bc23_mengerCore_of_corridors ω a₁ a₂ a₃ G b₁ b₂ b₃ hne hadj
    ⟨hcor₁, hcor₂, hcor₃⟩ ⟨hinf₁, hinf₂, hinf₃⟩
    ⟨cluster_ne_of_disjoint ϱ b₁ b₂ S₁ S₂ hsub₁ hsub₂ hd12,
      cluster_ne_of_disjoint ϱ b₁ b₃ S₁ S₃ hsub₁ hsub₃ hd13,
      cluster_ne_of_disjoint ϱ b₂ b₃ S₂ S₃ hsub₂ hsub₃ hd23⟩





















def bc23_LatticeCorridorRouting (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
      (w₁ : (hypercubicLattice d).Walk a₁ b₁) (w₂ : (hypercubicLattice d).Walk a₂ b₂)
      (w₃ : (hypercubicLattice d).Walk a₃ b₃),
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃) ∧
      ((0 : Site d) ∉ w₁.support ∧ (0 : Site d) ∉ w₂.support ∧ (0 : Site d) ∉ w₃.support) ∧
      ((0 : Site d) ∉ cluster d ω b₁ ∧ (0 : Site d) ∉ cluster d ω b₂ ∧
        (0 : Site d) ∉ cluster d ω b₃) ∧
      ((cluster d ω b₁).Infinite ∧ (cluster d ω b₂).Infinite ∧ (cluster d ω b₃).Infinite) ∧
      ∃ S₁ S₂ S₃ : Set (Site d),
        (b₁ ∈ S₁ ∧ b₂ ∈ S₂ ∧ b₃ ∈ S₃) ∧
        (∀ u v, u ∈ S₁ →
          (openSubgraph d (removeSite 0 (forceOpenFinset
            (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₁) ∧
        (∀ u v, u ∈ S₂ →
          (openSubgraph d (removeSite 0 (forceOpenFinset
            (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₂) ∧
        (∀ u v, u ∈ S₃ →
          (openSubgraph d (removeSite 0 (forceOpenFinset
            (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₃) ∧
        (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃)




theorem bc23_mengerRoutingCover_of_latticeCorridorRouting (d n : ℕ)
    (h : bc23_LatticeCorridorRouting d n) : MengerRoutingCover d n := by
  intro ω hω
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, w₁, w₂, w₃, hne, hadj, hw0, h0, hinf,
    S₁, S₂, S₃, hb, hcl₁, hcl₂, hcl₃, hd⟩ := h ω hω
  exact bc23_mengerCore_of_latticeCorridors ω a₁ a₂ a₃ b₁ b₂ b₃ w₁ w₂ w₃ hne hadj
    hw0.1 hw0.2.1 hw0.2.2 h0 hinf S₁ S₂ S₃ hb.1 hb.2.1 hb.2.2 hcl₁ hcl₂ hcl₃
    hd.1 hd.2.1 hd.2.2










theorem bc23_burtonKeane_uniqueness_of_latticeCorridorRouting
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hr : ∀ n : ℕ, bc23_LatticeCorridorRouting d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  mng_burton_keane_uniqueness_mengerCover μ herg hfe bdry hbound hvol hdens
    (fun n => bc23_mengerRoutingCover_of_latticeCorridorRouting d n (hr n))











theorem bc23_nil_support (a : Site d) : ((Walk.nil : (hypercubicLattice d).Walk a a)).support = [a] := by
  simp





theorem bc23_mengerCore_of_originFree (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧
      (0 : Site d) ∉ cluster d ω a₃)
    (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite)
    (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧
      cluster d ω a₂ ≠ cluster d ω a₃) :
    MengerCore ω := by
  classical
  
  have hw0 : ∀ a : Site d, a ≠ 0 → (0 : Site d) ∉ ((Walk.nil : (hypercubicLattice d).Walk a a)).support := by
    intro a ha hmem; rw [bc23_nil_support] at hmem; simp only [List.mem_singleton] at hmem
    exact ha hmem.symm
  have ha0₁ : a₁ ≠ 0 := ((hypercubicLattice d).ne_of_adj hadj.1).symm
  have ha0₂ : a₂ ≠ 0 := ((hypercubicLattice d).ne_of_adj hadj.2.1).symm
  have ha0₃ : a₃ ≠ 0 := ((hypercubicLattice d).ne_of_adj hadj.2.2).symm
  
  have hGempty : (bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₁ a₁)
      ∪ bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₂ a₂)
      ∪ bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₃ a₃))
      = (∅ : Finset (Sym2 (Site d))) := by
    simp [bc23_walkEdges]
  
  set ϱ := removeSite 0 (forceOpenFinset (bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₁ a₁)
      ∪ bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₂ a₂)
      ∪ bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₃ a₃)) ω) with hϱ
  have hϱeq : ϱ = removeSite 0 ω := by rw [hϱ, hGempty, mng_forceOpenFinset_empty]
  
  have hcd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ :=
    bc20_removeSite_cluster_ne ω a₁ a₂ hdist.1
  have hcd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ :=
    bc20_removeSite_cluster_ne ω a₁ a₃ hdist.2.1
  have hcd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃ :=
    bc20_removeSite_cluster_ne ω a₂ a₃ hdist.2.2
  refine bc23_mengerCore_of_latticeCorridors ω a₁ a₂ a₃ a₁ a₂ a₃
    Walk.nil Walk.nil Walk.nil hne hadj (hw0 a₁ ha0₁) (hw0 a₂ ha0₂) (hw0 a₃ ha0₃) h0 hinf
    (cluster d ϱ a₁) (cluster d ϱ a₂) (cluster d ϱ a₃)
    (self_mem_cluster ϱ a₁) (self_mem_cluster ϱ a₂) (self_mem_cluster ϱ a₃)
    (fun u v hu hadj => mng_cluster_adjClosed ϱ a₁ hu hadj)
    (fun u v hu hadj => mng_cluster_adjClosed ϱ a₂ hu hadj)
    (fun u v hu hadj => mng_cluster_adjClosed ϱ a₃ hu hadj)
    ?_ ?_ ?_
  · rw [hϱeq]; exact mng_disjoint_of_cluster_ne (removeSite 0 ω) a₁ a₂ hcd12
  · rw [hϱeq]; exact mng_disjoint_of_cluster_ne (removeSite 0 ω) a₁ a₃ hcd13
  · rw [hϱeq]; exact mng_disjoint_of_cluster_ne (removeSite 0 ω) a₂ a₃ hcd23



section AxiomAudit


#guard_msgs in
#print axioms bc23_corridor_of_walk


#guard_msgs in
#print axioms bc23_corridor_of_walk_subset


#guard_msgs in
#print axioms bc23_mengerCore_of_corridors


#guard_msgs in
#print axioms bc23_forcedCluster_infinite_of_originFree


#guard_msgs(whitespace := lax) in
#print axioms bc23_mengerCore_of_latticeCorridors


#guard_msgs(whitespace := lax) in
#print axioms bc23_mengerRoutingCover_of_latticeCorridorRouting


#guard_msgs(whitespace := lax) in
#print axioms bc23_burtonKeane_uniqueness_of_latticeCorridorRouting


#guard_msgs(whitespace := lax) in
#print axioms bc23_mengerCore_of_originFree

end AxiomAudit

end StatMech.Walls
