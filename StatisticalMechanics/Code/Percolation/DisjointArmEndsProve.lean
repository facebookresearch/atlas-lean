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

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}











open Classical in




noncomputable def daep_cutArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x a : Site d) :
    Finset (Site d) :=
  (tfc_boundaryFinset d n).filter (fun z => Connected d (removeSite x ω) a z)

theorem daep_mem_cutArmEnds {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x a z : Site d} :
    z ∈ daep_cutArmEnds ω n x a ↔ z ∈ vertexBoundary d n ∧ Connected d (removeSite x ω) a z := by
  classical
  rw [daep_cutArmEnds, Finset.mem_filter, tfc_mem_boundaryFinset]


theorem daep_cutArmEnds_subset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x a : Site d) :
    daep_cutArmEnds ω n x a ⊆ tfc_boundaryFinset d n := by
  classical
  exact Finset.filter_subset _ _





theorem daep_cutArmEnds_disjoint_of_disconnected (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a₁ a₂ : Site d} (hdis : ¬ Connected d (removeSite x ω) a₁ a₂) :
    Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₂) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_cutArmEnds] at hw1 hw2
  exact hdis (hw1.2.trans hw2.2.symm)





theorem daep_cutArmEnds_nonempty (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x a : Site d) (habox : a ∈ box d n) (hinf : (cluster d (removeSite x ω) a).Infinite) :
    (daep_cutArmEnds ω n x a).Nonempty := by
  classical
  obtain ⟨z, hzb, hzc⟩ := bk2_branch_reaches_boundary_rem ω n hn x a habox hinf
  exact ⟨z, daep_mem_cutArmEnds.mpr ⟨hzb, hzc⟩⟩






















theorem daep_three_cut_blocks_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    {x a₁ a₂ a₃ : Site d}
    (ha1box : a₁ ∈ box d n) (ha2box : a₂ ∈ box d n) (ha3box : a₃ ∈ box d n)
    (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite x ω) a₃).Infinite)
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
    ((daep_cutArmEnds ω n x a₁).Nonempty ∧ (daep_cutArmEnds ω n x a₂).Nonempty ∧
      (daep_cutArmEnds ω n x a₃).Nonempty) ∧
    (daep_cutArmEnds ω n x a₁ ⊆ tfc_boundaryFinset d n ∧
      daep_cutArmEnds ω n x a₂ ⊆ tfc_boundaryFinset d n ∧
      daep_cutArmEnds ω n x a₃ ⊆ tfc_boundaryFinset d n) ∧
    (Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₂) ∧
      Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₃) ∧
      Disjoint (daep_cutArmEnds ω n x a₂) (daep_cutArmEnds ω n x a₃)) :=
  ⟨⟨daep_cutArmEnds_nonempty ω n hn x a₁ ha1box hi1,
    daep_cutArmEnds_nonempty ω n hn x a₂ ha2box hi2,
    daep_cutArmEnds_nonempty ω n hn x a₃ ha3box hi3⟩,
   ⟨daep_cutArmEnds_subset ω n x a₁, daep_cutArmEnds_subset ω n x a₂,
    daep_cutArmEnds_subset ω n x a₃⟩,
   ⟨daep_cutArmEnds_disjoint_of_disconnected ω n hd12,
    daep_cutArmEnds_disjoint_of_disconnected ω n hd13,
    daep_cutArmEnds_disjoint_of_disconnected ω n hd23⟩⟩


















theorem daep_doubleCut_le (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    removeSite x (removeSite y ω) ≤ ω := by
  intro e
  unfold removeSite
  by_cases hx : x ∈ e
  · simp [hx]
  · by_cases hy : y ∈ e <;> simp [hx, hy]










theorem daep_doubleCut_arms_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y a b : Site d}
    (hdis : ¬ Connected d (removeSite x (removeSite y ω)) a b) :
    Disjoint (daep_cutArmEnds (removeSite y ω) n x a)
      (daep_cutArmEnds (removeSite x ω) n y b) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_cutArmEnds] at hw1 hw2
  
  have hsymm : removeSite y (removeSite x ω) = removeSite x (removeSite y ω) := by
    funext e
    unfold removeSite
    by_cases hx : x ∈ e <;> by_cases hy : y ∈ e <;> simp [hx, hy]
  have hwa : Connected d (removeSite x (removeSite y ω)) a w := hw1.2
  have hwb : Connected d (removeSite x (removeSite y ω)) b w := by
    rw [← hsymm]; exact hw2.2
  exact hdis (hwa.trans hwb.symm)






























def daep_CutDisjointArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ A : Site d → Finset (Site d),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → (A x).Nonempty) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ z ∈ A x, z ∈ vertexBoundary d n ∧ Connected d ω x z) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y → Disjoint (A x) (A y))








theorem daep_distinctArmEnds_of_cutDisjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep_CutDisjointArmEnds ω n) :
    tfc_DistinctArmEnds ω n := by
  classical
  obtain ⟨A, hne, hmem, hdisj⟩ := h
  
  set sel : Site d → Site d := fun x =>
    if hx : x ∈ box d n ∧ IsTrifurcation d ω x then (hne x hx.1 hx.2).choose else x with hsel
  refine ⟨sel, ?_, ?_⟩
  · intro x hxbox htri
    have hchoose := (hne x hxbox htri).choose_spec
    have := hmem x hxbox htri _ hchoose
    simp only [hsel, dif_pos (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x)]
    exact this
  · intro x hxbox htri y hybox htriy hxy
    by_contra hne'
    have hxchoose := (hne x hxbox htri).choose_spec
    have hychoose := (hne y hybox htriy).choose_spec
    simp only [hsel, dif_pos (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x),
      dif_pos (⟨hybox, htriy⟩ : y ∈ box d n ∧ IsTrifurcation d ω y)] at hxy
    have hmem' : (hne x hxbox htri).choose ∈ A x ∩ A y :=
      Finset.mem_inter.mpr ⟨hxchoose, hxy ▸ hychoose⟩
    rw [Finset.disjoint_iff_inter_eq_empty.mp (hdisj x hxbox htri y hybox htriy hne')] at hmem'
    exact absurd hmem' (Finset.notMem_empty _)


theorem daep_Tcount_le_boundary_of_cutDisjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep_CutDisjointArmEnds ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds ω n (daep_distinctArmEnds_of_cutDisjoint ω n h)













theorem daep_cutDisjoint_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    daep_CutDisjointArmEnds ω n := by
  classical
  refine ⟨bk2_armEndFinset ω n, ?_, ?_, ?_⟩
  · intro x hxbox htri
    exact bk2_armEndFinset_nonempty ω n hn x hxbox htri
  · intro x _ _ z hz
    exact bk2_mem_armEndFinset.mp hz
  · intro x hxbox htri y hybox htriy hxy
    exact absurd (hsub x y hxbox htri hybox htriy) hxy







theorem daep_cutDisjoint_of_disjointArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hdisj : bk2_DisjointArmEnds ω n) :
    daep_CutDisjointArmEnds ω n := by
  classical
  refine ⟨bk2_armEndFinset ω n, ?_, ?_, ?_⟩
  · intro x hxbox htri
    exact bk2_armEndFinset_nonempty ω n hn x hxbox htri
  · intro x _ _ z hz
    exact bk2_mem_armEndFinset.mp hz
  · intro x hxbox htri y hybox htriy hxy
    exact hdisj x hxbox htri y hybox htriy hxy
















theorem daep_burton_keane_bernoulli (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      daep_CutDisjointArmEnds ω n)
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
  tfc_burton_keane_bernoulli hd p hp1 hp0
    (fun ω n hn => daep_distinctArmEnds_of_cutDisjoint ω n (hres ω n hn))
    htrif

















noncomputable def removeSites (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    ConfigSpace (Sym2 (Site d)) :=
  fun e => if ∃ t ∈ T, t ∈ e then false else ω e



theorem daep_removeSites_le (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites T ω ≤ ω := by
  intro e
  unfold removeSites
  by_cases h : ∃ t ∈ T, t ∈ e <;> simp [h]

open Classical in


noncomputable def daep_globalCutArmEnds (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (a : Site d) : Finset (Site d) :=
  (tfc_boundaryFinset d n).filter (fun z => Connected d (removeSites T ω) a z)

theorem daep_mem_globalCutArmEnds {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))}
    {n : ℕ} {a z : Site d} :
    z ∈ daep_globalCutArmEnds T ω n a ↔
      z ∈ vertexBoundary d n ∧ Connected d (removeSites T ω) a z := by
  classical
  rw [daep_globalCutArmEnds, Finset.mem_filter, tfc_mem_boundaryFinset]



theorem daep_globalCutArmEnds_connected (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) {a z : Site d} (hz : z ∈ daep_globalCutArmEnds T ω n a) : Connected d ω a z :=
  connected_mono (daep_removeSites_le T ω) (daep_mem_globalCutArmEnds.mp hz).2




theorem daep_globalCutArmEnds_disjoint_of_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {a₁ a₂ : Site d}
    (hdis : ¬ Connected d (removeSites T ω) a₁ a₂) :
    Disjoint (daep_globalCutArmEnds T ω n a₁) (daep_globalCutArmEnds T ω n a₂) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_globalCutArmEnds] at hw1 hw2
  exact hdis (hw1.2.trans hw2.2.symm)






theorem daep_infinite_reaches_boundary (ω' : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (a : Site d) (habox : a ∈ box d n) (hinf : (cluster d ω' a).Infinite) :
    ∃ z ∈ vertexBoundary d n, Connected d ω' a z := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff ω' a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨c, e, hce, hc, he, hr⟩ :=
    tfc_walk_crossing (openSubgraph d ω') (fun v => v ∈ box d n) w habox hybox
  have hclat : (hypercubicLattice d).Adj c e := (openSubgraph_le ω') hce
  exact ⟨c, tfc_boundary_cross_vertex n hn c e hc he hclat, hr⟩



theorem daep_globalCutArmEnds_nonempty (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (a : Site d) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSites T ω) a).Infinite) :
    (daep_globalCutArmEnds T ω n a).Nonempty := by
  classical
  obtain ⟨z, hzb, hzc⟩ := daep_infinite_reaches_boundary (removeSites T ω) n hn a habox hinf
  exact ⟨z, daep_mem_globalCutArmEnds.mpr ⟨hzb, hzc⟩⟩













def daep_GlobalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y))















theorem daep_cutDisjoint_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daep_GlobalCutSeparation ω n) :
    daep_CutDisjointArmEnds ω n := by
  classical
  obtain ⟨b, hb, hsep⟩ := h
  refine ⟨fun x => daep_globalCutArmEnds (tfc_trifFinset ω n) ω n (b x), ?_, ?_, ?_⟩
  · 
    intro x hxbox htri
    obtain ⟨hbbox, _, hbinf⟩ := hb x hxbox htri
    exact daep_globalCutArmEnds_nonempty (tfc_trifFinset ω n) ω n hn (b x) hbbox hbinf
  · 
    intro x hxbox htri z hz
    obtain ⟨_, hbconn, _⟩ := hb x hxbox htri
    refine ⟨(daep_mem_globalCutArmEnds.mp hz).1, ?_⟩
    exact hbconn.trans (daep_globalCutArmEnds_connected (tfc_trifFinset ω n) ω n hz)
  · 
    intro x hxbox htri y hybox htriy hxy
    exact daep_globalCutArmEnds_disjoint_of_disconnected (tfc_trifFinset ω n) ω n
      (hsep x hxbox htri y hybox htriy hxy)



theorem daep_removeSites_singleton (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites {x} ω = removeSite x ω := by
  funext e
  unfold removeSites removeSite
  by_cases h : x ∈ e
  · rw [if_pos ⟨x, Finset.mem_singleton_self x, h⟩, if_pos h]
  · rw [if_neg (by rintro ⟨t, ht, hte⟩; rw [Finset.mem_singleton] at ht; exact h (ht ▸ hte)),
      if_neg h]




theorem daep_globalCutSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    daep_GlobalCutSeparation ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _; exact absurd htri (hno x hxbox)











theorem daep_globalCutSeparation_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    daep_GlobalCutSeparation ω n := by
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
  · intro x hxbox htri y hybox htriy hxy
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy


theorem daep_Tcount_le_boundary_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : daep_GlobalCutSeparation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep_Tcount_le_boundary_of_cutDisjoint ω n (daep_cutDisjoint_of_globalCutSeparation ω n hn h)
















theorem daep_burton_keane_bernoulli_of_globalCutSeparation (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      daep_GlobalCutSeparation ω n)
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
  daep_burton_keane_bernoulli hd p hp1 hp0
    (fun ω n hn => daep_cutDisjoint_of_globalCutSeparation ω n hn (hres ω n hn))
    htrif

end Percolation

end StatMech
