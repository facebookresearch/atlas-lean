/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Code.Walls.bc20mengerroute
import Code.Walls.bc21trifurc
import Code.Percolation.BurtonKeaneAttachment

open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech.Walls

variable {d : ℕ}









universe u
variable {V : Type u} {GG : SimpleGraph V}



theorem bc22_through_index_unique {A B : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily GG A B ι) (z₀ : V) {i j : ι}
    (hi : z₀ ∈ (F.p i).support) (hj : z₀ ∈ (F.p j).support) : i = j := by
  by_contra hne
  exact F.hdisj hne hi hj








theorem bc22_subfamily_avoiding {A B : Set V} {k : ℕ}
    (F : bc16_DisjointPathFamily GG A B (Fin (k + 1))) (z₀ : V) :
    ∃ G : bc16_DisjointPathFamily GG A B (Fin k),
      ∀ i : Fin k, z₀ ∉ (G.p i).support := by
  classical
  
  by_cases hex : ∃ i₀ : Fin (k + 1), z₀ ∈ (F.p i₀).support
  · obtain ⟨i₀, hi₀⟩ := hex
    
    refine ⟨⟨fun i => F.a (i₀.succAbove i), fun i => F.b (i₀.succAbove i),
      fun i => F.p (i₀.succAbove i), fun i => F.ha _, fun i => F.hb _, fun i => F.hp _, ?_⟩, ?_⟩
    · intro i j hij x hxi hxj
      exact F.hdisj (fun h => hij (i₀.succAbove_right_injective h)) hxi hxj
    · intro i hmem
      
      have heq : i₀.succAbove i = i₀ := bc22_through_index_unique F z₀ hmem hi₀
      exact (i₀.succAbove_ne i) heq
  · push Not at hex
    
    refine ⟨⟨fun i => F.a i.castSucc, fun i => F.b i.castSucc, fun i => F.p i.castSucc,
      fun i => F.ha _, fun i => F.hb _, fun i => F.hp _, ?_⟩, ?_⟩
    · intro i j hij x hxi hxj
      exact F.hdisj (fun h => hij (Fin.castSucc_injective k h)) hxi hxj
    · intro i; exact hex i.castSucc











theorem bc22_three_origin_avoiding_boxPaths_of_min4 (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {A B : Set (box d m)}
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 4 ≤ C.ncard) :
    ∃ G : bc16_DisjointPathFamily (bc20_boxGraph d m ω) A B (Fin 3),
      ∀ i : Fin 3, bc20_originBox d m ∉ (G.p i).support := by
  obtain ⟨F⟩ := bc20_hardDir_boxGraph d m ω A B 4 hmin
  exact bc22_subfamily_avoiding F (bc20_originBox d m)












theorem bc22_connected_removeSite_of_path (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v) (h0 : bc20_originBox d m ∉ p.support) :
    Connected d (removeSite 0 ω) (u : Site d) (v : Site d) :=
  bc20_connected_removeSite_of_avoiding ω (bc20_mapWalk d m ω p)
    (bc20_origin_avoid_of_boxAvoid d m ω p h0)




















theorem bc22_branch_origin_cut_survival (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {A B : Set (box d m)}
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 2 ≤ C.ncard) :
    ∃ (u v : box d m), u ∈ A ∧ v ∈ B ∧
      Connected d (removeSite 0 ω) (u : Site d) (v : Site d) :=
  bc20_connected_removeSite_of_min2 d m ω hmin



theorem bc22_mem_cluster_of_connected (ϱ : ConfigSpace (Sym2 (Site d))) {a u v : Site d}
    (hu : u ∈ cluster d ϱ a) (huv : Connected d ϱ u v) : v ∈ cluster d ϱ a := by
  rw [mem_cluster] at hu ⊢
  exact hu.trans huv




















def bc22_BoxThreeBranchMinCut (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, bka_MergeFree ω





theorem bc22_mengerCore_of_mergeFree (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_MergeFree ω) : MengerCore ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hdist⟩ := h
  exact mng_mengerCore_of_neighborClusters ω a₁ a₂ a₃ hne hadj hinf hdist





theorem bc22_mengerRoutingCover_of_boxThreeBranchMinCut (d n : ℕ)
    (h : bc22_BoxThreeBranchMinCut d n) : MengerRoutingCover d n :=
  fun ω hω => bc22_mengerCore_of_mergeFree ω (h ω hω)












theorem bc22_burtonKeane_uniqueness_of_boxThreeBranchMinCut
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site d))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hr : ∀ n : ℕ, bc22_BoxThreeBranchMinCut d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  mng_burton_keane_uniqueness_mengerCover μ herg hfe bdry hbound hvol hdens
    (fun n => bc22_mengerRoutingCover_of_boxThreeBranchMinCut d n (hr n))
























theorem bc22_mergeFree_of_threeBranchPaths (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hconn : Connected d (removeSite 0 ω) a₁ b₁ ∧ Connected d (removeSite 0 ω) a₂ b₂ ∧
      Connected d (removeSite 0 ω) a₃ b₃)
    (h0 : (0 : Site d) ∉ cluster d ω b₁ ∧ (0 : Site d) ∉ cluster d ω b₂ ∧
      (0 : Site d) ∉ cluster d ω b₃)
    (hinf : (cluster d ω b₁).Infinite ∧ (cluster d ω b₂).Infinite ∧ (cluster d ω b₃).Infinite)
    (hdist : cluster d ω b₁ ≠ cluster d ω b₂ ∧ cluster d ω b₁ ≠ cluster d ω b₃ ∧
      cluster d ω b₂ ≠ cluster d ω b₃) :
    bka_MergeFree ω := by
  
  have hclA₁ : cluster d (removeSite 0 ω) a₁ = cluster d (removeSite 0 ω) b₁ :=
    cluster_eq_of_connected hconn.1
  have hclA₂ : cluster d (removeSite 0 ω) a₂ = cluster d (removeSite 0 ω) b₂ :=
    cluster_eq_of_connected hconn.2.1
  have hclA₃ : cluster d (removeSite 0 ω) a₃ = cluster d (removeSite 0 ω) b₃ :=
    cluster_eq_of_connected hconn.2.2
  
  have hbi₁ : (cluster d (removeSite 0 ω) b₁).Infinite :=
    bc20_removeSite_infinite_of_originFree ω b₁ h0.1 hinf.1
  have hbi₂ : (cluster d (removeSite 0 ω) b₂).Infinite :=
    bc20_removeSite_infinite_of_originFree ω b₂ h0.2.1 hinf.2.1
  have hbi₃ : (cluster d (removeSite 0 ω) b₃).Infinite :=
    bc20_removeSite_infinite_of_originFree ω b₃ h0.2.2 hinf.2.2
  
  have hbd₁₂ : cluster d (removeSite 0 ω) b₁ ≠ cluster d (removeSite 0 ω) b₂ :=
    bc20_removeSite_cluster_ne ω b₁ b₂ hdist.1
  have hbd₁₃ : cluster d (removeSite 0 ω) b₁ ≠ cluster d (removeSite 0 ω) b₃ :=
    bc20_removeSite_cluster_ne ω b₁ b₃ hdist.2.1
  have hbd₂₃ : cluster d (removeSite 0 ω) b₂ ≠ cluster d (removeSite 0 ω) b₃ :=
    bc20_removeSite_cluster_ne ω b₂ b₃ hdist.2.2
  exact ⟨a₁, a₂, a₃, hne, hadj,
    ⟨hclA₁ ▸ hbi₁, hclA₂ ▸ hbi₂, hclA₃ ▸ hbi₃⟩,
    ⟨hclA₁ ▸ hclA₂ ▸ hbd₁₂, hclA₁ ▸ hclA₃ ▸ hbd₁₃, hclA₂ ▸ hclA₃ ▸ hbd₂₃⟩⟩










theorem bc22_mergeFree_of_originFree (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧
      (0 : Site d) ∉ cluster d ω a₃)
    (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite)
    (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧
      cluster d ω a₂ ≠ cluster d ω a₃) :
    bka_MergeFree ω :=
  bc22_mergeFree_of_threeBranchPaths ω a₁ a₂ a₃ a₁ a₂ a₃ hne hadj
    ⟨connected_rfl, connected_rfl, connected_rfl⟩ h0 hinf hdist



theorem bc22_mengerCore_of_originFree (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧
      (0 : Site d) ∉ cluster d ω a₃)
    (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite)
    (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧
      cluster d ω a₂ ≠ cluster d ω a₃) :
    MengerCore ω :=
  bc22_mengerCore_of_mergeFree ω (bc22_mergeFree_of_originFree ω a₁ a₂ a₃ hne hadj h0 hinf hdist)




theorem bc22_subfamily_avoiding_nonvacuous {A B : Set V} {k : ℕ}
    (F : bc16_DisjointPathFamily GG A B (Fin (k + 1))) (z₀ : V) :
    ∃ G : bc16_DisjointPathFamily GG A B (Fin k), ∀ i : Fin k, z₀ ∉ (G.p i).support :=
  bc22_subfamily_avoiding F z₀














theorem bc22_mengerCore_of_mergeFree' (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_MergeFree ω) : MengerCore ω :=
  bc22_mengerCore_of_mergeFree ω h



section AxiomAudit


#guard_msgs in
#print axioms bc22_subfamily_avoiding


#guard_msgs(whitespace := lax) in
#print axioms bc22_three_origin_avoiding_boxPaths_of_min4


#guard_msgs in
#print axioms bc22_connected_removeSite_of_path


#guard_msgs in
#print axioms bc22_mengerCore_of_mergeFree


#guard_msgs(whitespace := lax) in
#print axioms bc22_mengerRoutingCover_of_boxThreeBranchMinCut


#guard_msgs(whitespace := lax) in
#print axioms bc22_burtonKeane_uniqueness_of_boxThreeBranchMinCut


#guard_msgs(whitespace := lax) in
#print axioms bc22_mergeFree_of_threeBranchPaths


#guard_msgs in
#print axioms bc22_mergeFree_of_originFree

end AxiomAudit

end StatMech.Walls
