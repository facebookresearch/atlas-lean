/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.BurtonKeaneMerge
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose2
import Code.Percolation.DisjointArmEndsClose
import Code.Percolation.DisjointArmEndsProve

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}












theorem daep2_armEnds_share_forces_branch_connection (ω : ConfigSpace (Sym2 (Site d)))
    {x a b w : Site d}
    (hwa : Connected d (removeSite x ω) a w) (hwb : Connected d (removeSite x ω) b w) :
    Connected d (removeSite x ω) a b :=
  hwa.trans hwb.symm






theorem daep2_no_shared_boundary_of_disconnected_branches (ω : ConfigSpace (Sym2 (Site d)))
    {x a b : Site d} (hdis : ¬ Connected d (removeSite x ω) a b) :
    ∀ w, ¬ (Connected d (removeSite x ω) a w ∧ Connected d (removeSite x ω) b w) := by
  intro w ⟨hwa, hwb⟩
  exact hdis (daep2_armEnds_share_forces_branch_connection ω hwa hwb)













theorem daep2_globalCut_disconnected_of_omega_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {u v : Site d} (hdis : ¬ Connected d ω u v) :
    ¬ Connected d (removeSites T ω) u v :=
  fun hc => hdis (connected_mono (daep_removeSites_le T ω) hc)










theorem daep2_crossCluster_branches_globalCut_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x y a b : Site d}
    (hxa : Connected d ω x a) (hyb : Connected d ω y b)
    (hxy : ¬ Connected d ω x y) :
    ¬ Connected d (removeSites T ω) a b := by
  intro hc
  
  have hab : Connected d ω a b := connected_mono (daep_removeSites_le T ω) hc
  exact hxy (hxa.trans (hab.trans hyb.symm))














theorem daep2_removeSites_le_removeSite (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (hxT : x ∈ T) :
    removeSites T ω ≤ removeSite x ω := by
  intro e
  unfold removeSites removeSite
  by_cases hx : x ∈ e
  · 
    rw [if_pos hx, if_pos ⟨x, hxT, hx⟩]
  · 
    rw [if_neg hx]
    by_cases hT : ∃ t ∈ T, t ∈ e
    · rw [if_pos hT]; exact Bool.false_le _
    · rw [if_neg hT]





theorem daep2_globalCut_disconnected_of_singleCut (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x u v : Site d} (hxT : x ∈ T)
    (hdis : ¬ Connected d (removeSite x ω) u v) :
    ¬ Connected d (removeSites T ω) u v :=
  fun hc => hdis (connected_mono (daep2_removeSites_le_removeSite T ω hxT) hc)






















def daep2_SameClusterCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y))













theorem daep2_globalCutSeparation_of_sameCluster (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep2_SameClusterCutSeparation ω n) :
    daep_GlobalCutSeparation ω n := by
  classical
  obtain ⟨b, hb, hsame⟩ := h
  refine ⟨b, hb, ?_⟩
  intro x hxbox htri y hybox htriy hxy
  by_cases hconn : Connected d ω x y
  · 
    exact hsame x hxbox htri y hybox htriy hxy hconn
  · 
    obtain ⟨_, hbxconn, _⟩ := hb x hxbox htri
    obtain ⟨_, hbyconn, _⟩ := hb y hybox htriy
    exact daep2_crossCluster_branches_globalCut_disconnected (tfc_trifFinset ω n) ω
      hbxconn hbyconn hconn
















theorem daep2_meets_at_most_one_branch (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧
    ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) :=
  ⟨fun ⟨h1, h2⟩ => hd12 (h1.trans h2.symm),
   fun ⟨h1, h3⟩ => hd13 (h1.trans h3.symm),
   fun ⟨h2, h3⟩ => hd23 (h2.trans h3.symm)⟩








theorem daep2_two_branches_avoid (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v) ∨
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨
    (¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) := by
  classical
  by_cases h1 : Connected d (removeSite x ω) a₁ v
  · 
    refine Or.inr (Or.inr ⟨fun h2 => hd12 (h1.trans h2.symm), fun h3 => hd13 (h1.trans h3.symm)⟩)
  · by_cases h2 : Connected d (removeSite x ω) a₂ v
    · 
      exact Or.inr (Or.inl ⟨h1, fun h3 => hd23 (h2.trans h3.symm)⟩)
    · 
      exact Or.inl ⟨h1, h2⟩

























def daep2_SingleCutBranchSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ Connected d (removeSite x ω) (b x) (b y))






theorem daep2_sameClusterCutSeparation_of_singleCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep2_SingleCutBranchSeparation ω n) :
    daep2_SameClusterCutSeparation ω n := by
  obtain ⟨b, hb, hsep⟩ := h
  refine ⟨b, hb, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  
  have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  exact daep2_globalCut_disconnected_of_singleCut (tfc_trifFinset ω n) ω hxT
    (hsep x hxbox htri y hybox htriy hxy hconn)









theorem daep2_sameClusterCutSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    daep2_SameClusterCutSeparation ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)









theorem daep2_sameClusterCutSeparation_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    daep2_SameClusterCutSeparation ω n := by
  classical
  
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy
    rw [tfc_mem_trifFinset] at hy
    exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    refine ⟨habox, haconn, ?_⟩
    rw [hcut]; exact hainf
  · intro x hxbox htri y hybox htriy hxy _
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy





















theorem daep2_singleCutBranchSeparation_of_distinctClusters (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (b : Site d → Site d)
    (hb : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y) :
    daep2_SingleCutBranchSeparation ω n := by
  refine ⟨b, hb, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  exact absurd hconn (hsep x hxbox htri y hybox htriy hxy)


theorem daep2_singleCutBranchSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    daep2_SingleCutBranchSeparation ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)




theorem daep2_Tcount_le_boundary_of_sameCluster (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daep2_SameClusterCutSeparation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep_Tcount_le_boundary_of_globalCutSeparation ω n hn
    (daep2_globalCutSeparation_of_sameCluster ω n h)














theorem daep2_burton_keane_bernoulli_of_sameCluster (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      daep2_SameClusterCutSeparation ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  daep_burton_keane_bernoulli_of_globalCutSeparation hd p hp1 hp0
    (fun ω n hn => daep2_globalCutSeparation_of_sameCluster ω n (hres ω n hn))
    htrif





theorem daep2_Tcount_le_boundary_of_singleCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daep2_SingleCutBranchSeparation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep2_Tcount_le_boundary_of_sameCluster ω n hn
    (daep2_sameClusterCutSeparation_of_singleCut ω n h)









theorem daep2_burton_keane_bernoulli_of_singleCut (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      daep2_SingleCutBranchSeparation ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  daep2_burton_keane_bernoulli_of_sameCluster hd p hp1 hp0
    (fun ω n hn => daep2_sameClusterCutSeparation_of_singleCut ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
