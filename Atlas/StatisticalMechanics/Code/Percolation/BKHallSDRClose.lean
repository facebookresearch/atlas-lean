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
import Code.Percolation.DisjointArmEndsProve2

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}














theorem bhs_exists_injOn_of_hall {V : Type*} [DecidableEq V] (T : Finset V)
    (armEnds : V → Finset V)
    (hHall : ∀ S : Finset V, S ⊆ T → S.card ≤ (S.biUnion armEnds).card) :
    ∃ φ : V → V, (∀ x ∈ T, φ x ∈ armEnds x) ∧ Set.InjOn φ T := by
  classical
  
  set t : {x // x ∈ T} → Finset V := fun i => armEnds i.1 with ht
  have hHallSub : ∀ s : Finset {x // x ∈ T}, s.card ≤ (s.biUnion t).card := by
    intro s
    set S : Finset V := s.image (fun i => i.1) with hS
    have hSsub : S ⊆ T := by
      intro x hx
      rw [hS, Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact i.2
    have hcardS : S.card = s.card := by
      rw [hS, Finset.card_image_of_injective]
      exact fun a b hab => Subtype.ext hab
    have hbiUnion : s.biUnion t = S.biUnion armEnds := by
      ext z
      simp only [Finset.mem_biUnion, ht, hS, Finset.mem_image]
      constructor
      · rintro ⟨i, hi, hz⟩; exact ⟨i.1, ⟨i, hi, rfl⟩, hz⟩
      · rintro ⟨x, ⟨i, hi, rfl⟩, hz⟩; exact ⟨i, hi, hz⟩
    rw [← hcardS, hbiUnion]
    exact hHall S hSsub
  obtain ⟨f, hinj, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHallSub
  refine ⟨fun x => if hx : x ∈ T then f ⟨x, hx⟩ else x, ?_, ?_⟩
  · intro x hx
    simp only [dif_pos hx]
    exact hmem ⟨x, hx⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    simp only [dif_pos hx, dif_pos hy] at hxy
    exact congrArg Subtype.val (hinj hxy)





theorem bhs_hall_of_pairwiseDisjoint {V : Type*} [DecidableEq V] (T : Finset V)
    (armEnds : V → Finset V)
    (hne : ∀ x ∈ T, (armEnds x).Nonempty)
    (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (armEnds x) (armEnds y)) :
    ∀ S : Finset V, S ⊆ T → S.card ≤ (S.biUnion armEnds).card := by
  classical
  intro S hS
  rw [Finset.card_biUnion (fun x hx y hy hxy => hdisj x (hS hx) y (hS hy) hxy)]
  calc S.card = ∑ _x ∈ S, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ x ∈ S, (armEnds x).card :=
        Finset.sum_le_sum (fun x hx => Finset.Nonempty.card_pos (hne x (hS hx)))











open Classical in















def bhs_HallArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ S : Finset (Site d), S ⊆ tfc_trifFinset ω n →
      S.card ≤ (S.biUnion
        (fun x => daep_globalCutArmEnds (tfc_trifFinset ω n) ω n (b x))).card)






theorem bhs_distinctArmEnds_of_hall (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bhs_HallArmEnds ω n) :
    tfc_DistinctArmEnds ω n := by
  classical
  obtain ⟨b, hexist, hHall⟩ := h
  set T := tfc_trifFinset ω n with hT
  set armEnds : Site d → Finset (Site d) :=
    fun x => daep_globalCutArmEnds T ω n (b x) with harm
  
  obtain ⟨φ, hφmem, hφinj⟩ := bhs_exists_injOn_of_hall T armEnds hHall
  refine ⟨φ, ?_, ?_⟩
  · 
    intro x hxbox htri
    have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hmem := hφmem x hxT
    rw [harm, daep_mem_globalCutArmEnds] at hmem
    obtain ⟨_, hbconn, _⟩ := hexist x hxbox htri
    refine ⟨hmem.1, ?_⟩
    
    exact hbconn.trans (connected_mono (daep_removeSites_le T ω) hmem.2)
  · 
    intro x hxbox htri y hybox htriy hxy
    have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hyT : y ∈ T := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    exact hφinj hxT hyT hxy



theorem bhs_Tcount_le_boundary_of_hall (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bhs_HallArmEnds ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds ω n (bhs_distinctArmEnds_of_hall ω n h)


















theorem bhs_hallArmEnds_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daep_GlobalCutSeparation ω n) :
    bhs_HallArmEnds ω n := by
  classical
  obtain ⟨b, hexist, hsep⟩ := h
  refine ⟨b, hexist, ?_⟩
  set T := tfc_trifFinset ω n with hT
  
  apply bhs_hall_of_pairwiseDisjoint T
    (fun x => daep_globalCutArmEnds T ω n (b x))
  · 
    intro x hxT
    rw [hT, tfc_mem_trifFinset] at hxT
    obtain ⟨hbbox, _, hbinf⟩ := hexist x hxT.1 hxT.2
    exact daep_globalCutArmEnds_nonempty T ω n hn (b x) hbbox hbinf
  · 
    intro x hxT y hyT hxy
    rw [hT, tfc_mem_trifFinset] at hxT hyT
    exact daep_globalCutArmEnds_disjoint_of_disconnected T ω n
      (hsep x hxT.1 hxT.2 y hyT.1 hyT.2 hxy)






theorem bhs_hallArmEnds_of_singleCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (h : daep2_SingleCutBranchSeparation ω n) :
    bhs_HallArmEnds ω n :=
  bhs_hallArmEnds_of_globalCutSeparation ω n hn
    (daep2_globalCutSeparation_of_sameCluster ω n
      (daep2_sameClusterCutSeparation_of_singleCut ω n h))















theorem bhs_hallArmEnds_of_disjointSep (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (b : Site d → Site d)
    (hexist : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y →
      ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y)) :
    bhs_HallArmEnds ω n :=
  bhs_hallArmEnds_of_globalCutSeparation ω n hn ⟨b, hexist, hsep⟩




theorem bhs_hallArmEnds_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bhs_HallArmEnds ω n := by
  classical
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro S hS
    
    have hTempty : tfc_trifFinset ω n = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [tfc_mem_trifFinset] at hx
      exact hno x hx.1 hx.2
    rw [hTempty] at hS
    rw [Finset.subset_empty.mp hS, Finset.card_empty]
    exact Nat.zero_le _


















theorem bhs_burton_keane_bernoulli_of_hall (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bhs_HallArmEnds ω n)
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
    (fun ω n _hn => bhs_distinctArmEnds_of_hall ω n (hres ω n _hn))
    htrif

end Percolation

end StatMech
