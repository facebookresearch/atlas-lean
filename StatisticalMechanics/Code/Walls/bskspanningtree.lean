/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Walls.bctconnectedtree

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}






theorem bsk_exists_spanningTree {V : Type*} (G : SimpleGraph V) (h : G.Connected) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree :=
  h.exists_isTree_le




theorem bsk_three_le_degree {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {v a b c : W}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) : 3 ≤ G.degree v := by
  have hsub : ({a, b, c} : Finset W) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      simp only [SimpleGraph.mem_neighborFinset, ha, hb, hc]
  have hcard : ({a, b, c} : Finset W).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  calc 3 = ({a, b, c} : Finset W).card := hcard.symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub
    _ = G.degree v := rfl










def bsk_augRel {V Leaf : Type*} (H : SimpleGraph V) (par : Leaf → V) :
    (V ⊕ Leaf) → (V ⊕ Leaf) → Prop
  | Sum.inl a, Sum.inl b => H.Adj a b
  | Sum.inl a, Sum.inr l => par l = a
  | Sum.inr l, Sum.inl a => par l = a
  | Sum.inr _, Sum.inr _ => False



def bsk_augG {V Leaf : Type*} (H : SimpleGraph V) (par : Leaf → V) : SimpleGraph (V ⊕ Leaf) :=
  SimpleGraph.fromRel (bsk_augRel H par)

noncomputable instance {V Leaf : Type*} (H : SimpleGraph V) (par : Leaf → V) :
    DecidableRel (bsk_augG H par).Adj := Classical.decRel _


theorem bsk_augG_adj_inl_inl {V Leaf : Type*} {H : SimpleGraph V} {par : Leaf → V} {a b : V} :
    (bsk_augG H par).Adj (Sum.inl a) (Sum.inl b) ↔ H.Adj a b := by
  unfold bsk_augG
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact h
    · exact H.symm h
  · intro h
    exact ⟨fun hh => (H.ne_of_adj h) (Sum.inl_injective hh), Or.inl h⟩


theorem bsk_augG_adj_inr_inl {V Leaf : Type*} {H : SimpleGraph V} {par : Leaf → V} {l : Leaf}
    {a : V} : (bsk_augG H par).Adj (Sum.inr l) (Sum.inl a) ↔ par l = a := by
  unfold bsk_augG
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩ <;> exact h
  · intro h; exact ⟨by simp, Or.inl h⟩


theorem bsk_augG_adj_inl_inr {V Leaf : Type*} {H : SimpleGraph V} {par : Leaf → V} {l : Leaf}
    {a : V} : (bsk_augG H par).Adj (Sum.inl a) (Sum.inr l) ↔ par l = a := by
  rw [SimpleGraph.adj_comm]; exact bsk_augG_adj_inr_inl


theorem bsk_augG_not_adj_inr_inr {V Leaf : Type*} {H : SimpleGraph V} {par : Leaf → V}
    {l l' : Leaf} : ¬ (bsk_augG H par).Adj (Sum.inr l) (Sum.inr l') := by
  unfold bsk_augG
  rw [SimpleGraph.fromRel_adj]
  rintro ⟨hne, h | h⟩ <;> exact h


theorem bsk_augG_neighborSet_inr {V Leaf : Type*} {H : SimpleGraph V} {par : Leaf → V} {l : Leaf} :
    (bsk_augG H par).neighborSet (Sum.inr l) = {Sum.inl (par l)} := by
  ext y
  simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
  cases y with
  | inl a =>
    rw [bsk_augG_adj_inr_inl]
    exact ⟨fun h => by rw [h], fun h => (Sum.inl_injective h).symm⟩
  | inr l' =>
    constructor
    · intro h; exact absurd h bsk_augG_not_adj_inr_inr
    · intro h; exact absurd h (by simp)







theorem bsk_augG_acyclic {V Leaf : Type*} (H : SimpleGraph V) (par : Leaf → V)
    (hH : H.IsAcyclic) : (bsk_augG H par).IsAcyclic := by
  intro v c hc
  
  have hsupp : ∀ x ∈ c.support, ∃ a : V, x = Sum.inl a := by
    intro x hx
    match x, hx with
    | Sum.inl a, _ => exact ⟨a, rfl⟩
    | Sum.inr l, hx =>
      exfalso
      have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hx
      have hsub : c.toSubgraph.neighborSet (Sum.inr l) ⊆
          (bsk_augG H par).neighborSet (Sum.inr l) := by
        intro y hy
        rw [SimpleGraph.mem_neighborSet]
        exact c.toSubgraph.adj_sub hy
      rw [bsk_augG_neighborSet_inr] at hsub
      have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      rw [h2, Set.ncard_singleton] at hle
      omega
  
  set φ : (V ⊕ Leaf) → V := Sum.elim id par with hφ
  set G₀ : SimpleGraph (V ⊕ Leaf) := H.comap φ with hG0
  
  let phiHom : G₀ →g H := SimpleGraph.Hom.comap φ H
  
  have hedges : ∀ e ∈ c.edges, e ∈ G₀.edgeSet := by
    intro e he
    induction e using Sym2.ind with | _ x y =>
    have hxy : (bsk_augG H par).Adj x y := by
      have hmem := c.edges_subset_edgeSet he; rwa [SimpleGraph.mem_edgeSet] at hmem
    have hx : x ∈ c.support := c.fst_mem_support_of_mem_edges he
    have hy : y ∈ c.support := c.snd_mem_support_of_mem_edges he
    obtain ⟨a, rfl⟩ := hsupp x hx
    obtain ⟨b, rfl⟩ := hsupp y hy
    rw [bsk_augG_adj_inl_inl] at hxy
    rw [SimpleGraph.mem_edgeSet, hG0, SimpleGraph.comap_adj]
    simpa [hφ] using hxy
  
  have key : ∀ (w : G₀.Walk v v), w.IsCycle →
      (∀ x ∈ w.support, ∃ a : V, x = Sum.inl a) → False := by
    intro w hw hws
    have hinj : Set.InjOn φ {x | x ∈ w.support} := by
      intro x hx y hy hxy
      obtain ⟨a, rfl⟩ := hws x hx
      obtain ⟨b, rfl⟩ := hws y hy
      simp only [hφ, Sum.elim_inl, id_eq] at hxy
      rw [hxy]
    have hcm : (w.map phiHom).IsCycle := by
      rw [SimpleGraph.Walk.isCycle_def] at hw ⊢
      obtain ⟨htr, hne, hnodup⟩ := hw
      refine ⟨?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isTrail_def] at htr ⊢
        rw [SimpleGraph.Walk.edges_map]
        apply List.Nodup.map_on _ htr
        intro e1 he1 e2 he2 hee
        induction e1 using Sym2.ind with | _ a1 b1 =>
        induction e2 using Sym2.ind with | _ a2 b2 =>
        have ha1 : a1 ∈ w.support := w.fst_mem_support_of_mem_edges he1
        have hb1 : b1 ∈ w.support := w.snd_mem_support_of_mem_edges he1
        have ha2 : a2 ∈ w.support := w.fst_mem_support_of_mem_edges he2
        have hb2 : b2 ∈ w.support := w.snd_mem_support_of_mem_edges he2
        simp only [Sym2.map_mk] at hee
        rw [Sym2.eq_iff] at hee ⊢
        rcases hee with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · left; exact ⟨hinj ha1 ha2 e1, hinj hb1 hb2 e2⟩
        · right; exact ⟨hinj ha1 hb2 e1, hinj hb1 ha2 e2⟩
      · intro h
        apply hne
        cases w with
        | nil => rfl
        | cons hh w' => simp [SimpleGraph.Walk.map_cons] at h
      · rw [SimpleGraph.Walk.support_map, ← List.map_tail]
        apply List.Nodup.map_on _ hnodup
        intro x hx y hy hxy
        exact hinj (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hy) hxy
    exact hH _ hcm
  
  refine key (c.transfer G₀ hedges) (hc.transfer hedges) ?_
  intro x hx
  rw [SimpleGraph.Walk.support_transfer] at hx
  exact hsupp x hx


theorem bsk_augG_leaf_deg_one {V Leaf : Type} [Fintype V] [DecidableEq V] [Fintype Leaf]
    [DecidableEq Leaf] (H : SimpleGraph V) (par : Leaf → V) (l : Leaf) :
    (bsk_augG H par).degree (Sum.inr l) = 1 := by
  have hnf : (bsk_augG H par).neighborFinset (Sum.inr l) = {Sum.inl (par l)} := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton, ← SimpleGraph.mem_neighborSet,
      bsk_augG_neighborSet_inr, Set.mem_singleton_iff]
  rw [SimpleGraph.degree, hnf, Finset.card_singleton]










open Classical in








theorem bsk_exploration_of_augmentedTree (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {V Leaf : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype Leaf] [DecidableEq Leaf]
    (H : SimpleGraph V) (par : Leaf → V) (hH : H.IsAcyclic)
    (trifIdx : Site d → V) (compLeaf : Leaf → Set (Site d))
    (hall3 : ∀ a : V, 3 ≤ (bsk_augG H par).degree (Sum.inl a))
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z)
    (hcompB : ∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty)
    (hcompD : ∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l')) :
    bfg_GenuineExploration ω L R := by
  classical
  
  have hdeg1_inr : ∀ v : V ⊕ Leaf, (bsk_augG H par).degree v = 1 → ∃ l : Leaf, v = Sum.inr l := by
    intro v hv
    cases v with
    | inl a => exact absurd (hv ▸ hall3 a) (by norm_num)
    | inr l => exact ⟨l, rfl⟩
  refine bct_exploration_of_carrier ω L R (V ⊕ Leaf) (bsk_augG H par)
    (fun y => Sum.inl (trifIdx y)) (Sum.elim (fun _ => (∅ : Set (Site d))) compLeaf)
    (bsk_augG_acyclic H par hH) ?_ ?_ ?_ ?_ ?_
  · 
    intro v
    cases v with
    | inl a => exact le_trans (by norm_num) (hall3 a)
    | inr l => rw [bsk_augG_leaf_deg_one]
  · 
    intro y _ _; exact hall3 (trifIdx y)
  · 
    intro y hybox hygen z hzbox hzgen hyz
    exact hinj y hybox hygen z hzbox hzgen (Sum.inl_injective hyz)
  · 
    intro v hv
    obtain ⟨l, rfl⟩ := hdeg1_inr v hv
    exact hcompB l
  · 
    intro u hu v hv huv
    obtain ⟨lu, rfl⟩ := hdeg1_inr u hu
    obtain ⟨lv, rfl⟩ := hdeg1_inr v hv
    exact hcompD lu lv (fun h => huv (by rw [h]))








open Classical in



theorem bsk_exploration_of_armTree (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {V Leaf : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype Leaf] [DecidableEq Leaf]
    (H : SimpleGraph V) (par : Leaf → V) (hH : H.IsAcyclic)
    (trifIdx : Site d → V) (compLeaf : Leaf → Set (Site d))
    (harm : ∀ a : V, ∃ x y z : V ⊕ Leaf, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      (bsk_augG H par).Adj (Sum.inl a) x ∧ (bsk_augG H par).Adj (Sum.inl a) y ∧
      (bsk_augG H par).Adj (Sum.inl a) z)
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z)
    (hcompB : ∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty)
    (hcompD : ∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l')) :
    bfg_GenuineExploration ω L R := by
  classical
  refine bsk_exploration_of_augmentedTree ω L R H par hH trifIdx compLeaf ?_ hinj hcompB hcompD
  intro a
  obtain ⟨x, y, z, hxy, hxz, hyz, hax, hay, haz⟩ := harm a
  exact bsk_three_le_degree (bsk_augG H par) hxy hxz hyz hax hay haz


theorem bsk_genuineForest_of_augmentedTree (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {V Leaf : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype Leaf] [DecidableEq Leaf]
    (H : SimpleGraph V) (par : Leaf → V) (hH : H.IsAcyclic)
    (trifIdx : Site d → V) (compLeaf : Leaf → Set (Site d))
    (hall3 : ∀ a : V, 3 ≤ (bsk_augG H par).degree (Sum.inl a))
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z)
    (hcompB : ∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty)
    (hcompD : ∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l')) :
    bgt_GenuineForest ω L R :=
  bfg_genuineForest_of_exploration ω L R
    (bsk_exploration_of_augmentedTree ω L R H par hH trifIdx compLeaf hall3 hinj hcompB hcompD)


theorem bsk_genuineTcount_of_augmentedTree (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {V Leaf : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype Leaf] [DecidableEq Leaf]
    (H : SimpleGraph V) (par : Leaf → V) (hH : H.IsAcyclic)
    (trifIdx : Site d → V) (compLeaf : Leaf → Set (Site d))
    (hall3 : ∀ a : V, 3 ≤ (bsk_augG H par).degree (Sum.inl a))
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z)
    (hcompB : ∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty)
    (hcompD : ∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l')) :
    (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  bfg_genuineTcount_le_boundary ω L R
    (bsk_exploration_of_augmentedTree ω L R H par hH trifIdx compLeaf hall3 hinj hcompB hcompD)














def bsk_ConnectedForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (V Leaf : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Nonempty V) (_ : Fintype Leaf)
    (_ : DecidableEq Leaf) (H : SimpleGraph V) (par : Leaf → V) (trifIdx : Site d → V)
    (compLeaf : Leaf → Set (Site d)),
    H.IsAcyclic ∧
    (∀ a : V, 3 ≤ (bsk_augG H par).degree (Sum.inl a)) ∧
    (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → trifIdx y = trifIdx z → y = z) ∧
    (∀ l : Leaf, (compLeaf l ∩ vertexBoundary d R).Nonempty) ∧
    (∀ l l' : Leaf, l ≠ l' → Disjoint (compLeaf l) (compLeaf l'))



theorem bsk_exploration_of_connectedForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bsk_ConnectedForestData ω L R) : bfg_GenuineExploration ω L R := by
  obtain ⟨V, Leaf, _, _, _, _, _, H, par, trifIdx, compLeaf, hH, hall3, hinj, hcompB, hcompD⟩ := h
  exact bsk_exploration_of_augmentedTree ω L R H par hH trifIdx compLeaf hall3 hinj hcompB hcompD




theorem bsk_bk_count_of_connectedForest (L R : ℕ)
    (hdata : ∀ ω : ConfigSpace (Sym2 (Site d)), bsk_ConnectedForestData ω L R) :
    ∀ ω : ConfigSpace (Sym2 (Site d)),
      (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  fun ω => bfg_genuineTcount_le_boundary ω L R (bsk_exploration_of_connectedForestData ω L R (hdata ω))



























theorem bsk_status :
    
    (∀ {V Leaf : Type*} (H : SimpleGraph V) (par : Leaf → V), H.IsAcyclic →
      (bsk_augG H par).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bsk_ConnectedForestData ω L R →
      bfg_GenuineExploration ω L R) ∧
    
    (∀ {V : Type} (G : SimpleGraph V), G.Connected → ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree) ∧
    
    (∀ (L R : ℕ), (∀ ω : ConfigSpace (Sym2 (Site d)), bsk_ConnectedForestData ω L R) →
      ∀ ω : ConfigSpace (Sym2 (Site d)),
        (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) :=
  ⟨fun H par hH => bsk_augG_acyclic H par hH,
   fun ω L R h => bsk_exploration_of_connectedForestData ω L R h,
   fun G h => bsk_exists_spanningTree G h,
   fun L R hdata ω => bsk_bk_count_of_connectedForest L R hdata ω⟩

end StatMech.Walls
