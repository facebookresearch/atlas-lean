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
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose
import Code.Percolation.ForestLeafCountClose
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.BKHallSDRClose
import Code.Percolation.ArmEndDisjointClose
import Code.Percolation.SpanningTreeRealiseClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}




















theorem tfh_twoFold_hall_root {V : Type*} [DecidableEq V] (T : Finset V)
    (rootEnds : Finset V) (armEnds : V → Fin 2 → Finset V)
    (hrne : rootEnds.Nonempty)
    (hne : ∀ x ∈ T, ∀ i, (armEnds x i).Nonempty)
    (hrdisj : ∀ x ∈ T, ∀ i, Disjoint rootEnds (armEnds x i))
    (hdisj : ∀ x ∈ T, ∀ i, ∀ y ∈ T, ∀ j, (x, i) ≠ (y, j) →
      Disjoint (armEnds x i) (armEnds y j)) :
    ∃ (r₀ : V) (ℓ : V → Fin 2 → V),
      r₀ ∈ rootEnds ∧
      (∀ x ∈ T, ∀ i, ℓ x i ∈ armEnds x i) ∧
      (∀ x ∈ T, ∀ i, ℓ x i ≠ r₀) ∧
      (∀ x ∈ T, ∀ i, ∀ y ∈ T, ∀ j, ℓ x i = ℓ y j → x = y ∧ i = j) := by
  classical
  
  set ι := Option ({x // x ∈ T} × Fin 2) with hι
  set t : ι → Finset V := fun p => p.elim rootEnds (fun q => armEnds q.1.1 q.2) with ht
  
  have hHall : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
    intro s
    rw [Finset.card_biUnion]
    · calc s.card = ∑ _p ∈ s, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ p ∈ s, (t p).card := by
            apply Finset.sum_le_sum
            intro p _
            cases p with
            | none => exact Finset.Nonempty.card_pos hrne
            | some q => exact Finset.Nonempty.card_pos (hne q.1.1 q.1.2 q.2)
    · 
      intro p _ q _ hpq
      cases p with
      | none =>
        cases q with
        | none => exact absurd rfl hpq
        | some q' => exact hrdisj q'.1.1 q'.1.2 q'.2
      | some p' =>
        cases q with
        | none => exact (hrdisj p'.1.1 p'.1.2 p'.2).symm
        | some q' =>
          apply hdisj p'.1.1 p'.1.2 p'.2 q'.1.1 q'.1.2 q'.2
          intro hcontra
          apply hpq
          rw [Prod.mk.injEq] at hcontra
          exact congrArg some (Prod.ext (Subtype.ext hcontra.1) hcontra.2)
  obtain ⟨f, hinj, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  refine ⟨f none, fun x i => if hx : x ∈ T then f (some (⟨x, hx⟩, i)) else x, ?_, ?_, ?_, ?_⟩
  · exact hmem none
  · intro x hx i; simp only [dif_pos hx]; exact hmem (some (⟨x, hx⟩, i))
  · intro x hx i hcontra
    simp only [dif_pos hx] at hcontra
    have : (some (⟨x, hx⟩, i) : ι) = none := hinj hcontra
    exact absurd this (by simp)
  · intro x hx i y hy j hxy
    simp only [dif_pos hx, dif_pos hy] at hxy
    have := hinj hxy
    rw [Option.some.injEq, Prod.mk.injEq] at this
    exact ⟨congrArg Subtype.val this.1, this.2⟩












open Classical in


















def tfh_TwoFoldForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (r : Site d) (b : Site d → Fin 2 → Site d),
    (r ∈ box d n ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) r).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ i,
      b x i ∈ box d n ∧ Connected d ω x (b x i) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x i)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ i,
      ¬ aed_sameGlobalComponent (tfc_trifFinset ω n) ω r (b x i)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ i, ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ∀ j, (x, i) ≠ (y, j) →
      ¬ aed_sameGlobalComponent (tfc_trifFinset ω n) ω (b x i) (b y j))










open Classical in






theorem tfh_forestLeafSelection_of_twoFoldForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : tfh_TwoFoldForestArms ω n) :
    str_ForestLeafSelection ω n := by
  classical
  obtain ⟨r, b, ⟨hrbox, hrinf⟩, hexist, hrootSep, hbranchSep⟩ := h
  set T := tfc_trifFinset ω n with hT
  
  set rootEnds : Finset (Site d) := daep_globalCutArmEnds T ω n r with hrootEnds
  set armEnds : Site d → Fin 2 → Finset (Site d) :=
    fun x i => daep_globalCutArmEnds T ω n (b x i) with harmEnds
  
  have hrne : rootEnds.Nonempty := daep_globalCutArmEnds_nonempty T ω n hn r hrbox hrinf
  
  have hne : ∀ x ∈ T, ∀ i, (armEnds x i).Nonempty := by
    intro x hxT i
    rw [hT, tfc_mem_trifFinset] at hxT
    obtain ⟨hbbox, _, hbinf⟩ := hexist x hxT.1 hxT.2 i
    exact daep_globalCutArmEnds_nonempty T ω n hn (b x i) hbbox hbinf
  
  have hrdisj : ∀ x ∈ T, ∀ i, Disjoint rootEnds (armEnds x i) := by
    intro x hxT i
    rw [hT, tfc_mem_trifFinset] at hxT
    exact aed_globalCutArmEnds_disjoint_of_distinct T ω n (hrootSep x hxT.1 hxT.2 i)
  
  have hdisj : ∀ x ∈ T, ∀ i, ∀ y ∈ T, ∀ j, (x, i) ≠ (y, j) →
      Disjoint (armEnds x i) (armEnds y j) := by
    intro x hxT i y hyT j hne'
    rw [hT, tfc_mem_trifFinset] at hxT hyT
    exact aed_globalCutArmEnds_disjoint_of_distinct T ω n
      (hbranchSep x hxT.1 hxT.2 i y hyT.1 hyT.2 j hne')
  
  obtain ⟨r₀, ℓ, hr₀mem, hℓmem, hℓne, hℓinj⟩ :=
    tfh_twoFold_hall_root T rootEnds armEnds hrne hne hrdisj hdisj
  
  refine ⟨r₀, ℓ, ?_, ?_, ?_, ?_, ?_⟩
  · 
    exact (daep_mem_globalCutArmEnds.mp hr₀mem).1
  · 
    intro x hxbox htri j
    have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    exact (daep_mem_globalCutArmEnds.mp (hℓmem x hxT j)).1
  · 
    intro x hxbox htri j
    have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    obtain ⟨_, hbconn, _⟩ := hexist x hxbox htri j
    have hleaf : Connected d (removeSites T ω) (b x j) (ℓ x j) :=
      (daep_mem_globalCutArmEnds.mp (hℓmem x hxT j)).2
    exact hbconn.trans (connected_mono (daep_removeSites_le T ω) hleaf)
  · 
    intro x hxbox htri j
    have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    exact hℓne x hxT j
  · 
    intro x hxbox htri y hybox htriy j j' hjj
    have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hyT : y ∈ T := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    exact hℓinj x hxT j y hyT j' hjj












open Classical in






theorem tfh_twoFoldForestArms_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a₀ a₁ a₂ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (ha0box : a₀ ∈ box d n) (ha1box : a₁ ∈ box d n) (ha2box : a₂ ∈ box d n)
    (hc0 : Connected d ω x₀ a₀) (hc1 : Connected d ω x₀ a₁)
    (hinf0 : (cluster d (removeSite x₀ ω) a₀).Infinite)
    (hinf1 : (cluster d (removeSite x₀ ω) a₁).Infinite)
    (hinf2 : (cluster d (removeSite x₀ ω) a₂).Infinite)
    (hsep01 : ¬ Connected d (removeSite x₀ ω) a₀ a₁)
    (hsep0r : ¬ Connected d (removeSite x₀ ω) a₂ a₀)
    (hsep1r : ¬ Connected d (removeSite x₀ ω) a₂ a₁)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    tfh_TwoFoldForestArms ω n := by
  classical
  
  have hTeq : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy
    rw [tfc_mem_trifFinset] at hy
    exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hTeq, daep_removeSites_singleton]
  
  refine ⟨a₂, fun _ i => if i = 0 then a₀ else a₁, ⟨ha2box, ?_⟩, ?_, ?_, ?_⟩
  · rw [hcut]; exact hinf2
  · 
    intro x hxbox htri i
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with hi | hi <;> simp only [hi] <;>
      first
        | exact ⟨ha0box, by simpa using hc0, by rw [hcut]; exact hinf0⟩
        | exact ⟨ha1box, by simpa using hc1, by rw [hcut]; exact hinf1⟩
  · 
    intro x hxbox htri i
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    rw [aed_sameGlobalComponent, hcut]
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with hi | hi <;> simp only [hi]
    · simpa using hsep0r
    · simpa using hsep1r
  · 
    intro x hxbox htri i y hybox htriy j hne'
    have hx0 : x = x₀ := huniq x hxbox htri
    have hy0 : y = x₀ := huniq y hybox htriy
    subst hx0; subst hy0
    
    have hij : i ≠ j := fun hc => hne' (by rw [hc])
    rw [aed_sameGlobalComponent, hcut]
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with hi | hi <;>
      rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;>
      simp only [hi, hj] at hij ⊢
    · exact absurd rfl hij
    · simpa using hsep01
    · 
      intro hcon; exact hsep01 hcon.symm
    · exact absurd rfl hij










theorem tfh_spanningTreeLeafCount_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d n) (hz₁ : z₁ ∈ vertexBoundary d n)
    (hzne : z₀ ≠ z₁) (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    flc2_SpanningTreeLeafCount ω n :=
  str_base_of_twoBoundary ω n hz₀ hz₁ hzne hno











theorem tfh_spanningTreeLeafCount_of_twoFoldForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : tfh_TwoFoldForestArms ω n)
    (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
    flc2_SpanningTreeLeafCount ω n :=
  str_spanningTreeLeafCount_of_forestLeafSelection ω n
    (tfh_forestLeafSelection_of_twoFoldForestArms ω n hn h) hbase


theorem tfh_Tcount_le_boundary_of_twoFoldForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : tfh_TwoFoldForestArms ω n)
    (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  flc2_Tcount_le_boundary_of_spanningTree ω n
    (tfh_spanningTreeLeafCount_of_twoFoldForestArms ω n hn h hbase)



theorem tfh_spanningTree_of_twoFoldForestArms
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfh_TwoFoldForestArms ω n)
    (hbase : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
    ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → flc2_SpanningTreeLeafCount ω n :=
  fun ω n hn =>
    tfh_spanningTreeLeafCount_of_twoFoldForestArms ω n hn (hres ω n hn) (hbase ω n hn)















theorem tfh_burton_keane_bernoulli_of_twoFoldForestArms (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfh_TwoFoldForestArms ω n)
    (hbase : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n)
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
  str_burton_keane_bernoulli_of_forestLeafSelection hd p hp1 hp0
    (fun ω n hn => tfh_forestLeafSelection_of_twoFoldForestArms ω n hn (hres ω n hn))
    hbase htrif

end Percolation

end StatMech
