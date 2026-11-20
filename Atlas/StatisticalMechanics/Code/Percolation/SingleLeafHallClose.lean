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

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}









theorem slh_cut_neighbor {W : Type*} [DecidableEq W] {G : SimpleGraph W} {x a : W} (hxa : x ≠ a)
    (h : G.Reachable x a) :
    ∃ (c : W) (hc : c ≠ x) (ha : a ≠ x), G.Adj x c ∧
      (G.induce ({x}ᶜ : Set W)).Reachable ⟨c, by simpa using hc⟩ ⟨a, by simpa using ha⟩ := by
  classical
  obtain ⟨p⟩ := h
  set q : G.Walk x a := (p.toPath : G.Walk x a) with hq
  have hqp : q.IsPath := (p.toPath).2
  have hnnil : ¬ q.Nil := Walk.not_nil_of_ne hxa
  set c := q.snd with hc
  have hadj : G.Adj x c := q.adj_snd hnnil
  have hcx : c ≠ x := (G.ne_of_adj hadj).symm
  have hax : a ≠ x := fun h => hxa h.symm
  have hsupp : ∀ y ∈ q.tail.support, y ∈ ({x}ᶜ : Set W) := by
    intro y hy
    have hcons : q.support = x :: q.tail.support := by
      rw [Walk.support_tail_of_not_nil q hnnil, Walk.cons_tail_support]
    have hnd := hqp.support_nodup
    rw [hcons, List.nodup_cons] at hnd
    intro hyx
    simp only [Set.mem_singleton_iff] at hyx
    subst hyx
    exact hnd.1 hy
  have hind := q.tail.induce ({x}ᶜ : Set W) hsupp
  exact ⟨c, hcx, hax, hadj, ⟨hind.copy (by simp [hc]) rfl⟩⟩




theorem slh_deg_ge_three_of_cut {W : Type*} [DecidableEq W] [Fintype W] {G : SimpleGraph W}
    [DecidableRel G.Adj] {x a₁ a₂ a₃ : W}
    (hr₁ : G.Reachable x a₁) (hr₂ : G.Reachable x a₂) (hr₃ : G.Reachable x a₃)
    (hx₁ : x ≠ a₁) (hx₂ : x ≠ a₂) (hx₃ : x ≠ a₃)
    (hcut₁₂ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₂, by simpa using hx₂.symm⟩)
    (hcut₁₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩)
    (hcut₂₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₂, by simpa using hx₂.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩) :
    3 ≤ G.degree x := by
  classical
  obtain ⟨c₁, _, _, hadj₁, hreach₁⟩ := slh_cut_neighbor hx₁ hr₁
  obtain ⟨c₂, _, _, hadj₂, hreach₂⟩ := slh_cut_neighbor hx₂ hr₂
  obtain ⟨c₃, _, _, hadj₃, hreach₃⟩ := slh_cut_neighbor hx₃ hr₃
  have h12 : c₁ ≠ c₂ := by rintro rfl; exact hcut₁₂ (hreach₁.symm.trans hreach₂)
  have h13 : c₁ ≠ c₃ := by rintro rfl; exact hcut₁₃ (hreach₁.symm.trans hreach₃)
  have h23 : c₂ ≠ c₃ := by rintro rfl; exact hcut₂₃ (hreach₂.symm.trans hreach₃)
  have hsub : ({c₁, c₂, c₃} : Finset W) ⊆ G.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [G.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact hadj₁
    · exact hadj₂
    · exact hadj₃
  have hcard : ({c₁, c₂, c₃} : Finset W).card = 3 :=
    Finset.card_eq_three.mpr ⟨c₁, c₂, c₃, h12, h13, h23, rfl⟩
  calc 3 = ({c₁, c₂, c₃} : Finset W).card := hcard.symm
    _ ≤ (G.neighborFinset x).card := Finset.card_le_card hsub
    _ = G.degree x := G.card_neighborFinset_eq_degree x










theorem slh_edge_transfer (x u v : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    (hadj : (openSubgraph d ω).Adj u v) (hux : u ≠ x) (hvx : v ≠ x) :
    (openSubgraph d (removeSite x ω)).Adj u v := by
  obtain ⟨hl, ho⟩ := hadj
  refine ⟨hl, ?_⟩
  rw [removeSite_apply_of_notMem]
  · exact ho
  · intro hx
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact hux rfl
    · exact hvx rfl



theorem slh_walk_avoid_transfer {x u v : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (w : (openSubgraph d ω).Walk u v) (hw : x ∉ w.support) :
    (openSubgraph d (removeSite x ω)).Reachable u v := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih =>
    rw [Walk.support_cons, List.mem_cons, not_or] at hw
    obtain ⟨hax, hw'⟩ := hw
    have hbx : x ≠ b := fun h => by subst h; exact hw' (w.start_mem_support)
    exact (Adj.reachable
      (slh_edge_transfer x a b ω hab (Ne.symm hax) (Ne.symm hbx))).trans (ih hw')




theorem slh_connected_removeSite_of_G_induce {W : Type*} {ω : ConfigSpace (Sym2 (Site d))}
    {G : SimpleGraph W} (π : W → Site d)
    (hπ : ∀ u v, G.Adj u v → (openSubgraph d ω).Adj (π u) (π v))
    (hπinj : Function.Injective π)
    {p wi wj : W} (hwi : wi ≠ p) (hwj : wj ≠ p)
    (h : (G.induce ({p}ᶜ : Set W)).Reachable ⟨wi, by simpa using hwi⟩ ⟨wj, by simpa using hwj⟩) :
    Connected d (removeSite (π p) ω) (π wi) (π wj) := by
  obtain ⟨w⟩ := h
  set f : (G.induce ({p}ᶜ : Set W)) →g (openSubgraph d ω) :=
    { toFun := fun u => π u.1
      map_rel' := fun {a b} hab => hπ a.1 b.1 hab } with hf
  set w' := w.map f with hw'
  have hsupp : (π p) ∉ w'.support := by
    intro hx
    rw [hw', Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨c, hc⟩, _, hcx⟩ := hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    exact hc (hπinj (by simpa [hf] using hcx))
  exact slh_walk_avoid_transfer w' hsupp










open Classical in















def slh_TreeForestData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj)
    (π : W → Site d) (ιT : Site d → W) (sec : Site d → Site d → W) (lamL : W → Site d),
    G.IsTree ∧ 2 ≤ Fintype.card W ∧
    (∀ u v, G.Adj u v → (openSubgraph d ω).Adj (π u) (π v)) ∧
    Function.Injective π ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → π (ιT x) = x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ιT x = ιT y → x = y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, Connected d ω x a →
      π (sec x a) = a ∧ sec x a ≠ ιT x ∧ G.Reachable (ιT x) (sec x a)) ∧
    (∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d n) ∧
    Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))








theorem slh_spanningTreeLeafCount_of_treeForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : slh_TreeForestData ω n) :
    flc2_SpanningTreeLeafCount ω n := by
  classical
  obtain ⟨W, _, _, G, _, π, ιT, sec, lamL, hTree, hWcard, hπ, hπinj,
    hπιT, hιinj, hsec, hlammap, hlaminj⟩ := h
  refine ⟨W, inferInstance, inferInstance, G, inferInstance, ιT, lamL, hTree, hWcard,
    ?_, hιinj, hlammap, hlaminj⟩
  
  intro x hxbox htri
  have htri' := htri
  
  obtain ⟨a₁, a₂, a₃, ⟨hne12, hne13, hne23⟩, ⟨hc1, hc2, hc3⟩, _, ⟨hcut12, hcut13, hcut23⟩⟩ := htri'
  set p := ιT x with hp
  have hpx : π p = x := hπιT x hxbox htri
  
  obtain ⟨hπw1, hw1p, hr1⟩ := hsec x hxbox htri a₁ hc1
  obtain ⟨hπw2, hw2p, hr2⟩ := hsec x hxbox htri a₂ hc2
  obtain ⟨hπw3, hw3p, hr3⟩ := hsec x hxbox htri a₃ hc3
  
  have hcutG : ∀ (u v : W) (b c : Site d), π u = b → π v = c →
      (hup : u ≠ p) → (hvp : v ≠ p) →
      ¬ Connected d (removeSite x ω) b c →
      ¬ (G.induce ({p}ᶜ : Set W)).Reachable
        ⟨u, by simpa using hup⟩ ⟨v, by simpa using hvp⟩ := by
    intro u v b c hub hvc hup hvp hcut hreach
    apply hcut
    have := slh_connected_removeSite_of_G_induce π hπ hπinj hup hvp hreach
    rwa [hpx, hub, hvc] at this
  refine slh_deg_ge_three_of_cut hr1 hr2 hr3 hw1p.symm hw2p.symm hw3p.symm
    (hcutG _ _ _ _ hπw1 hπw2 hw1p hw2p hcut12)
    (hcutG _ _ _ _ hπw1 hπw3 hw1p hw3p hcut13)
    (hcutG _ _ _ _ hπw2 hπw3 hw2p hw3p hcut23)


theorem slh_Tcount_le_boundary_of_treeForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : slh_TreeForestData ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  flc2_Tcount_le_boundary_of_spanningTree ω n (slh_spanningTreeLeafCount_of_treeForest ω n h)








open Classical in






theorem slh_treeForestData_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d n) (hz₁ : z₁ ∈ vertexBoundary d n)
    (hopen : (openSubgraph d ω).Adj z₀ z₁)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    slh_TreeForestData ω n := by
  classical
  have hzne : z₀ ≠ z₁ := (openSubgraph d ω).ne_of_adj hopen
  refine ⟨Fin 2, inferInstance, inferInstance, Flc2Witness.pathG, inferInstance,
    (fun v => if v = 0 then z₀ else z₁), (fun _ => (0 : Fin 2)), (fun _ _ => (0 : Fin 2)),
    (fun v => if v = 0 then z₀ else z₁), Flc2Witness.pathG_isTree, by decide, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · 
    intro u v huv
    
    have h01 : (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
      revert huv; fin_cases u <;> fin_cases v <;> simp_all <;> decide
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



















theorem slh_claw_survives_branchingCount {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hTree : G.IsTree) (hWcard : 2 ≤ Fintype.card W) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      < (univ.filter (fun v => G.degree v = 1)).card :=
  flc2_tree_internal_lt_leaves G hTree hWcard






















theorem slh_burton_keane_bernoulli_of_treeForest (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → slh_TreeForestData ω n)
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
  tfc_burton_keane_uniqueness_full (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_isErgodic hd p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0)
    (fun n => boxSV_boundaryCard d n)
    (fun ω n hn => slh_Tcount_le_boundary_of_treeForest ω n (hres ω n hn))
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd)
    htrif

end Percolation

end StatMech
