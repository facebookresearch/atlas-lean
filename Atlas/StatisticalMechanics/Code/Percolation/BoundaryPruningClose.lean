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
import Code.Percolation.SingleLeafHallClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}










theorem bpr_treeForestData_slh_refutable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ¬ slh_TreeForestData ω n := by
  classical
  rintro ⟨W, _, _, G, _, π, ιT, sec, lamL, hTree, hWcard, hπ, hπinj,
    hπιT, hιinj, hsec, hlammap, hlaminj⟩
  
  have hinf : (cluster d ω x).Infinite := tfc_trif_cluster_infinite ω x htri
  
  have hinjOn : Set.InjOn (sec x) (cluster d ω x) := by
    intro a ha b hb hab
    obtain ⟨hπa, _, _⟩ := hsec x hxbox htri a ha
    obtain ⟨hπb, _, _⟩ := hsec x hxbox htri b hb
    rw [← hπa, ← hπb, hab]
  
  exact (hinf.image hinjOn) (Set.toFinite _)









open Classical in

















def bpr_TreeForestData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj)
    (π : W → Site d) (ιT : Site d → W) (br : Site d → Fin 3 → W) (lamL : W → Site d),
    G.IsTree ∧ 2 ≤ Fintype.card W ∧
    (∀ u v, G.Adj u v → (openSubgraph d ω).Adj (π u) (π v)) ∧
    Function.Injective π ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → π (ιT x) = x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ιT x = ιT y → x = y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      (∀ i, Connected d ω x (π (br x i)) ∧ br x i ≠ ιT x ∧ G.Reachable (ιT x) (br x i)) ∧
      (π (br x 0) ≠ π (br x 1) ∧ π (br x 0) ≠ π (br x 2) ∧ π (br x 1) ≠ π (br x 2)) ∧
      (¬ Connected d (removeSite x ω) (π (br x 0)) (π (br x 1)) ∧
       ¬ Connected d (removeSite x ω) (π (br x 0)) (π (br x 2)) ∧
       ¬ Connected d (removeSite x ω) (π (br x 1)) (π (br x 2)))) ∧
    (∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d n) ∧
    Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))







theorem bpr_spanningTreeLeafCount_of_treeForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bpr_TreeForestData ω n) :
    flc2_SpanningTreeLeafCount ω n := by
  classical
  obtain ⟨W, _, _, G, _, π, ιT, br, lamL, hTree, hWcard, hπ, hπinj,
    hπιT, hιinj, hbr, hlammap, hlaminj⟩ := h
  refine ⟨W, inferInstance, inferInstance, G, inferInstance, ιT, lamL, hTree, hWcard,
    ?_, hιinj, hlammap, hlaminj⟩
  intro x hxbox htri
  set p := ιT x with hp
  have hpx : π p = x := hπιT x hxbox htri
  obtain ⟨hreach, _hdist, hcut⟩ := hbr x hxbox htri
  obtain ⟨_hc1, hb1p, hr1⟩ := hreach 0
  obtain ⟨_hc2, hb2p, hr2⟩ := hreach 1
  obtain ⟨_hc3, hb3p, hr3⟩ := hreach 2
  obtain ⟨hcut12, hcut13, hcut23⟩ := hcut
  
  have hcutG : ∀ (u v : W) (hup : u ≠ p) (hvp : v ≠ p),
      ¬ Connected d (removeSite x ω) (π u) (π v) →
      ¬ (G.induce ({p}ᶜ : Set W)).Reachable
        ⟨u, by simpa using hup⟩ ⟨v, by simpa using hvp⟩ := by
    intro u v hup hvp hcut hreach2
    apply hcut
    have := slh_connected_removeSite_of_G_induce π hπ hπinj hup hvp hreach2
    rwa [hpx] at this
  refine slh_deg_ge_three_of_cut hr1 hr2 hr3 hb1p.symm hb2p.symm hb3p.symm
    (hcutG _ _ hb1p hb2p hcut12)
    (hcutG _ _ hb1p hb3p hcut13)
    (hcutG _ _ hb2p hb3p hcut23)


theorem bpr_Tcount_le_boundary_of_treeForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bpr_TreeForestData ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  flc2_Tcount_le_boundary_of_spanningTree ω n (bpr_spanningTreeLeafCount_of_treeForest ω n h)








open Classical in





theorem bpr_treeForestData_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d n) (hz₁ : z₁ ∈ vertexBoundary d n)
    (hopen : (openSubgraph d ω).Adj z₀ z₁)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bpr_TreeForestData ω n := by
  classical
  have hzne : z₀ ≠ z₁ := (openSubgraph d ω).ne_of_adj hopen
  refine ⟨Fin 2, inferInstance, inferInstance, Flc2Witness.pathG, inferInstance,
    (fun v => if v = 0 then z₀ else z₁), (fun _ => (0 : Fin 2)), (fun _ _ => (0 : Fin 2)),
    (fun v => if v = 0 then z₀ else z₁), Flc2Witness.pathG_isTree, by decide, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · 
    intro u v huv
    have h01 : (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
      revert huv; fin_cases u <;> fin_cases v <;> simp_all
    rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using hopen
    · simpa using hopen.symm
  · 
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all
  · 
    intro x hxbox htri; exact absurd htri (hno x hxbox)
  · 
    intro x hxbox htri; exact absurd htri (hno x hxbox)
  · 
    intro x hxbox htri; exact absurd htri (hno x hxbox)
  · 
    intro v _; fin_cases v
    · simpa using hz₀
    · simpa using hz₁
  · 
    intro u hu v hv huv
    fin_cases u <;> fin_cases v <;> simp_all

open Classical in








theorem bpr_treeForestData_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    bpr_TreeForestData ω n := by
  classical
  set π : Fin 4 → Site d := fun v => match v with
    | 0 => x | 1 => a 0 | 2 => a 1 | 3 => a 2 with hπdef
  set ιT : Site d → Fin 4 := fun _ => 0 with hιTdef
  set br : Site d → Fin 3 → Fin 4 := fun _ i => i.succ with hbrdef
  set lamL : Fin 4 → Site d := fun v => match v with
    | 0 => a 0 | 1 => a 0 | 2 => a 1 | 3 => a 2 with hlamLdef
  
  have hπinj : Function.Injective π := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp only [hπdef] at huv <;>
      first
        | rfl
        | (exact absurd huv (hxne 0).symm) | (exact absurd huv (hxne 1).symm)
        | (exact absurd huv (hxne 2).symm) | (exact absurd huv.symm (hxne 0).symm)
        | (exact absurd huv.symm (hxne 1).symm) | (exact absurd huv.symm (hxne 2).symm)
        | (exact absurd (hainj huv) (by decide))
  refine ⟨Fin 4, inferInstance, inferInstance, Flc2Witness.starG, inferInstance,
    π, ιT, br, lamL, Flc2Witness.starG_isTree, by decide, ?_, hπinj, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp only [] at huv ⊢ <;>
      first
        | (exact absurd huv (by decide))
        | exact hadj 0 | exact hadj 1 | exact hadj 2
        | exact (hadj 0).symm | exact (hadj 1).symm | exact (hadj 2).symm
  · 
    intro x' hx'box htri'
    rw [hsingle x' hx'box htri']
  · 
    intro x' hx'box htri' y' hy'box htriy' _
    rw [hsingle x' hx'box htri', hsingle y' hy'box htriy']
  · 
    intro x' hx'box htri'
    have hxx : x' = x := hsingle x' hx'box htri'
    subst hxx
    refine ⟨?_, ?_, ?_⟩
    · 
      intro i
      fin_cases i <;> refine ⟨?_, ?_, ?_⟩ <;>
        first
          | (exact (hadj 0).reachable) | (exact (hadj 1).reachable) | (exact (hadj 2).reachable)
          | (simp only [hbrdef]; decide)
    · 
      refine ⟨?_, ?_, ?_⟩
      · intro hh; exact absurd (hainj hh) (by decide)
      · intro hh; exact absurd (hainj hh) (by decide)
      · intro hh; exact absurd (hainj hh) (by decide)
    · 
      exact hsep
  · 
    intro v hv
    rw [Flc2Witness.starG_deg1_iff] at hv
    fin_cases v
    · exact absurd rfl hv
    · exact habdry 0
    · exact habdry 1
    · exact habdry 2
  · 
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_filter] at hu hv
    rw [Flc2Witness.starG_deg1_iff] at hu hv
    have hu' := hu.2; have hv' := hv.2
    fin_cases u <;> fin_cases v <;>
      first
        | (exact absurd rfl hu') | (exact absurd rfl hv') | rfl
        | (revert huv; simp only [hlamLdef]; intro huv;
            exact absurd (hainj huv) (by decide))






















theorem bpr_burton_keane_bernoulli_of_treeForest (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bpr_TreeForestData ω n)
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
  flc2_burton_keane_bernoulli_of_spanningTree hd p hp1 hp0
    (fun ω n hn => bpr_spanningTreeLeafCount_of_treeForest ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
