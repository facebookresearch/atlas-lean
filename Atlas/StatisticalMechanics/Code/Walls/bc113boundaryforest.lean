/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib

open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls



variable {V : Type*} [Fintype V] [DecidableEq V]




theorem bc113_exists_closer_neighbour (G : SimpleGraph V) {v b : V}
    (hr : G.Reachable v b) (hne : v ≠ b) :
    ∃ u, G.Adj v u ∧ G.dist u b < G.dist v b := by
  
  
  obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
  have hpvb : p.length = G.dist v b := by rw [hp, @SimpleGraph.dist_comm _ G b v]
  have hdvpos : 0 < G.dist v b := by
    apply Nat.pos_of_ne_zero
    rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
    exact ⟨hne, hr⟩
  have hpnn : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hpvb]; omega
  refine ⟨p.penultimate, (p.adj_penultimate hpnn).symm, ?_⟩
  have hdl : G.dist b p.penultimate ≤ p.dropLast.length := SimpleGraph.dist_le p.dropLast
  rw [SimpleGraph.Walk.length_dropLast, hpvb, @SimpleGraph.dist_comm _ G b p.penultimate] at hdl
  omega










noncomputable def bc113_toB (G : SimpleGraph V) (B : V → Prop) (v : V) : ℕ := by
  classical
  exact if h : ∃ b, B b ∧ G.Reachable v b then
    (Finset.univ.filter (fun b => B b ∧ G.Reachable v b)).inf'
      (by
        obtain ⟨b, hb⟩ := h
        exact ⟨b, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb⟩)
      (fun b => G.dist v b)
  else 0


def bc113_ReachesB (G : SimpleGraph V) (B : V → Prop) : Prop :=
  ∀ v, ∃ b, B b ∧ G.Reachable v b



theorem bc113_toB_witness (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) (v : V) :
    ∃ b, B b ∧ G.Reachable v b ∧ G.dist v b = bc113_toB G B v := by
  classical
  have hex : ∃ b, B b ∧ G.Reachable v b := hreach v
  have hne : (Finset.univ.filter (fun b => B b ∧ G.Reachable v b)).Nonempty := by
    obtain ⟨b, hb⟩ := hex
    exact ⟨b, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb⟩
  
  obtain ⟨b, hbmem, hbeq⟩ := Finset.exists_mem_eq_inf' hne (fun b => G.dist v b)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbmem
  refine ⟨b, hbmem.1, hbmem.2, ?_⟩
  simp only [bc113_toB, dif_pos hex]
  exact hbeq.symm


theorem bc113_toB_le (G : SimpleGraph V) (B : V → Prop) {v b : V}
    (hb : B b) (hr : G.Reachable v b) : bc113_toB G B v ≤ G.dist v b := by
  classical
  have hex : ∃ b, B b ∧ G.Reachable v b := ⟨b, hb, hr⟩
  simp only [bc113_toB, dif_pos hex]
  refine Finset.inf'_le _ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hb, hr⟩


theorem bc113_toB_eq_zero_of_mem (G : SimpleGraph V) (B : V → Prop) {v : V} (hv : B v) :
    bc113_toB G B v = 0 := by
  have := bc113_toB_le G B hv (SimpleGraph.Reachable.refl v)
  simpa using Nat.le_zero.mp (by simpa using this)


theorem bc113_toB_pos_of_not_mem (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {v : V} (hv : ¬ B v) : 0 < bc113_toB G B v := by
  classical
  rcases Nat.eq_zero_or_pos (bc113_toB G B v) with h0 | hpos
  · exfalso
    obtain ⟨b, hb, hr, hdeq⟩ := bc113_toB_witness G B hreach v
    rw [h0] at hdeq
    have : v = b := by
      by_contra hne
      have : 0 < G.dist v b := by
        apply Nat.pos_of_ne_zero
        rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]; exact ⟨hne, hr⟩
      omega
    exact hv (this ▸ hb)
  · exact hpos





theorem bc113_exists_parent (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {v : V} (hv : ¬ B v) :
    ∃ u, G.Adj v u ∧ bc113_toB G B u < bc113_toB G B v := by
  obtain ⟨b, hb, hr, hdeq⟩ := bc113_toB_witness G B hreach v
  have hvb : v ≠ b := fun h => hv (h ▸ hb)
  obtain ⟨u, hadj, hlt⟩ := bc113_exists_closer_neighbour G hr hvb
  refine ⟨u, hadj, ?_⟩
  
  have hru : G.Reachable u b := (hadj.symm.reachable).trans hr
  calc bc113_toB G B u ≤ G.dist u b := bc113_toB_le G B hb hru
    _ < G.dist v b := hlt
    _ = bc113_toB G B v := hdeq



open Classical in


noncomputable def bc113_parent (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    (v : V) : V := by
  classical
  exact if h : ¬ B v then (bc113_exists_parent G B hreach h).choose else v


theorem bc113_parent_spec (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {v : V} (hv : ¬ B v) :
    G.Adj v (bc113_parent G B hreach v) ∧
      bc113_toB G B (bc113_parent G B hreach v) < bc113_toB G B v := by
  classical
  simp only [bc113_parent, dif_pos hv]
  exact (bc113_exists_parent G B hreach hv).choose_spec

open Classical in



noncomputable def bc113_bForest (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) :
    SimpleGraph V := by
  classical
  exact SimpleGraph.fromEdgeSet
    {e : Sym2 V | ∃ v : V, ¬ B v ∧ e = s(v, bc113_parent G B hreach v)}



theorem bc113_bForest_adj (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {x y : V} :
    (bc113_bForest G B hreach).Adj x y ↔
      (∃ v, ¬ B v ∧ s(x, y) = s(v, bc113_parent G B hreach v)) ∧ x ≠ y := by
  classical
  simp only [bc113_bForest, SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq]


theorem bc113_bForest_le (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) :
    bc113_bForest G B hreach ≤ G := by
  classical
  intro x y hxy
  rw [bc113_bForest_adj] at hxy
  obtain ⟨⟨v, hvB, he⟩, hne⟩ := hxy
  rw [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (bc113_parent_spec G B hreach hvB).1
  · exact (bc113_parent_spec G B hreach hvB).1.symm



theorem bc113_bForest_toB_ne (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {x y : V} (hxy : (bc113_bForest G B hreach).Adj x y) :
    bc113_toB G B x ≠ bc113_toB G B y := by
  classical
  rw [bc113_bForest_adj] at hxy
  obtain ⟨⟨v, hvB, he⟩, hne⟩ := hxy
  rw [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fun h => absurd h (by have := (bc113_parent_spec G B hreach hvB).2; omega)
  · exact fun h => absurd h.symm (by have := (bc113_parent_spec G B hreach hvB).2; omega)





theorem bc113_bForest_down_is_parent (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {x y : V} (hxy : (bc113_bForest G B hreach).Adj x y)
    (hlt : bc113_toB G B y < bc113_toB G B x) :
    ¬ B x ∧ y = bc113_parent G B hreach x := by
  classical
  rw [bc113_bForest_adj] at hxy
  obtain ⟨⟨v, hvB, he⟩, hne⟩ := hxy
  rw [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · 
    exact ⟨hvB, rfl⟩
  · 
    exfalso
    have := (bc113_parent_spec G B hreach hvB).2
    omega




theorem bc113_bForest_down_unique (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {x y₁ y₂ : V} (h₁ : (bc113_bForest G B hreach).Adj x y₁)
    (h₂ : (bc113_bForest G B hreach).Adj x y₂)
    (hlt₁ : bc113_toB G B y₁ < bc113_toB G B x) (hlt₂ : bc113_toB G B y₂ < bc113_toB G B x) :
    y₁ = y₂ := by
  obtain ⟨_, he₁⟩ := bc113_bForest_down_is_parent G B hreach h₁ hlt₁
  obtain ⟨_, he₂⟩ := bc113_bForest_down_is_parent G B hreach h₂ hlt₂
  rw [he₁, he₂]












theorem bc113_bForest_adj_parent (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {v : V} (hv : ¬ B v) : (bc113_bForest G B hreach).Adj v (bc113_parent G B hreach v) := by
  classical
  rw [bc113_bForest_adj]
  refine ⟨⟨v, hv, rfl⟩, ?_⟩
  
  have hlt := (bc113_parent_spec G B hreach hv).2
  exact fun h => (Nat.ne_of_lt hlt) (congrArg (bc113_toB G B) h.symm)


theorem bc113_bForest_degree_pos_of_not_mem (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    {v : V} (hv : ¬ B v) : 1 ≤ (bc113_bForest G B hreach).degree v := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    (bc113_bForest G B hreach).degree_pos_iff_exists_adj]
  exact ⟨_, bc113_bForest_adj_parent G B hreach hv⟩






theorem bc113_leaf_is_tip (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    [DecidableRel (bc113_bForest G B hreach).Adj]
    {v : V} (hv : ¬ B v) (hdeg : (bc113_bForest G B hreach).degree v = 1) :
    ∀ u, (bc113_bForest G B hreach).Adj v u → u = bc113_parent G B hreach v := by
  classical
  intro u hu
  
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hdeg
  obtain ⟨w, hw, huniq⟩ := hdeg
  have hpar := bc113_bForest_adj_parent G B hreach hv
  rw [huniq u hu, huniq _ hpar]











theorem bc113_bForest_acyclic (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) :
    (bc113_bForest G B hreach).IsAcyclic := by
  classical
  set F := bc113_bForest G B hreach with hF
  set pot : V → ℕ := bc113_toB G B with hpot
  have hne : ∀ {x y : V}, F.Adj x y → pot x ≠ pot y := fun h => bc113_bForest_toB_ne G B hreach h
  have hunique : ∀ {x y₁ y₂ : V}, F.Adj x y₁ → F.Adj x y₂ →
      pot y₁ < pot x → pot y₂ < pot x → y₁ = y₂ :=
    fun h1 h2 l1 l2 => bc113_bForest_down_unique G B hreach h1 h2 l1 l2
  intro v c hc
  have hsupp_ne : c.support.toFinset.Nonempty := ⟨v, by simp⟩
  obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image c.support.toFinset pot hsupp_ne
  rw [List.mem_toFinset] at hm_mem
  set d := c.rotate m hm_mem with hd
  have hcd : d.IsCycle := hc.rotate hm_mem
  have hdnn : ¬ d.Nil := hcd.not_nil
  have hadj_snd : F.Adj m d.snd := d.adj_snd hdnn
  have hadj_pen : F.Adj d.penultimate m := d.adj_penultimate hdnn
  have hadj_pen' : F.Adj m d.penultimate := hadj_pen.symm
  have hsupp_eq : d.support.toFinset = c.support.toFinset := by
    apply Finset.ext; intro x
    simp only [List.mem_toFinset]; rw [hd, SimpleGraph.Walk.mem_support_rotate_iff]
  have hsnd_supp : d.snd ∈ c.support := by
    have hmem : d.snd ∈ d.support := List.mem_of_mem_tail (d.snd_mem_tail_support hdnn)
    rw [← List.mem_toFinset, hsupp_eq, List.mem_toFinset] at hmem; exact hmem
  have hpen_supp : d.penultimate ∈ c.support := by
    have hmem : d.penultimate ∈ d.support := by
      have h2 : d.penultimate = d.reverse.snd := (SimpleGraph.Walk.snd_reverse d).symm
      rw [h2]
      have hrn : ¬ d.reverse.Nil := by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length] at hdnn ⊢; simpa using hdnn
      have hmt : d.reverse.snd ∈ d.reverse.support :=
        List.mem_of_mem_tail (d.reverse.snd_mem_tail_support hrn)
      rw [SimpleGraph.Walk.support_reverse] at hmt; exact List.mem_reverse.mp hmt
    rw [← List.mem_toFinset, hsupp_eq, List.mem_toFinset] at hmem; exact hmem
  have hle_snd : pot d.snd ≤ pot m := hm_max _ (List.mem_toFinset.mpr hsnd_supp)
  have hle_pen : pot d.penultimate ≤ pot m := hm_max _ (List.mem_toFinset.mpr hpen_supp)
  have hlt_snd : pot d.snd < pot m := lt_of_le_of_ne hle_snd (fun h => (hne hadj_snd) h.symm)
  have hlt_pen : pot d.penultimate < pot m :=
    lt_of_le_of_ne hle_pen (fun h => (hne hadj_pen') h.symm)
  have heq : d.snd = d.penultimate := hunique hadj_snd hadj_pen' hlt_snd hlt_pen
  exact hcd.snd_ne_penultimate heq













def bc113_HasChild (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) : Prop :=
  ∀ v, ¬ B v → ∃ w, (bc113_bForest G B hreach).Adj v w ∧ bc113_toB G B v < bc113_toB G B w



theorem bc113_bForest_degree_ge_two_of_child (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    {v w : V} (hv : ¬ B v) (hadjw : (bc113_bForest G B hreach).Adj v w)
    (hltw : bc113_toB G B v < bc113_toB G B w) :
    2 ≤ (bc113_bForest G B hreach).degree v := by
  classical
  
  have hpar := bc113_bForest_adj_parent G B hreach hv
  have hparlt := (bc113_parent_spec G B hreach hv).2
  set p := bc113_parent G B hreach v with hp
  have hpw : p ≠ w := by
    intro h; rw [h] at hparlt; omega
  
  have hsub : {p, w} ⊆ (bc113_bForest G B hreach).neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl
    · exact hpar
    · exact hadjw
  calc 2 = ({p, w} : Finset V).card := by rw [Finset.card_pair hpw]
    _ ≤ ((bc113_bForest G B hreach).neighborFinset v).card := Finset.card_le_card hsub
    _ = (bc113_bForest G B hreach).degree v := SimpleGraph.card_neighborFinset_eq_degree _ _





theorem bc113_bForest_leaves_on_boundary (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    (hchild : bc113_HasChild G B hreach)
    {v : V} (hdeg : (bc113_bForest G B hreach).degree v = 1) : B v := by
  by_contra hv
  obtain ⟨w, hadjw, hltw⟩ := hchild v hv
  have h2 := bc113_bForest_degree_ge_two_of_child G B hreach hv hadjw hltw
  omega











def bc113_BoundaryHasChild (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) : Prop :=
  ∀ b, B b → ∃ w, (bc113_bForest G B hreach).Adj b w


theorem bc113_bForest_degree_pos_of_mem (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    (hbc : bc113_BoundaryHasChild G B hreach) {b : V} (hb : B b) :
    1 ≤ (bc113_bForest G B hreach).degree b := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    (bc113_bForest G B hreach).degree_pos_iff_exists_adj]
  exact hbc b hb



theorem bc113_bForest_min_degree (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    [DecidableRel (bc113_bForest G B hreach).Adj] (hbc : bc113_BoundaryHasChild G B hreach)
    (v : V) : 1 ≤ (bc113_bForest G B hreach).degree v := by
  by_cases hv : B v
  · exact bc113_bForest_degree_pos_of_mem G B hreach hbc hv
  · exact bc113_bForest_degree_pos_of_not_mem G B hreach hv









theorem bc113_boundaryAnchored_forest_exists (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B)
    (hchild : bc113_HasChild G B hreach) (hbc : bc113_BoundaryHasChild G B hreach) :
    ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
      F ≤ G ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
      (∀ v, F.degree v = 1 → B v) := by
  classical
  refine ⟨bc113_bForest G B hreach, Classical.decRel _, bc113_bForest_le G B hreach,
    bc113_bForest_acyclic G B hreach, ?_, ?_⟩
  · intro v; exact bc113_bForest_min_degree G B hreach hbc v
  · intro v hdeg; exact bc113_bForest_leaves_on_boundary G B hreach hchild hdeg











theorem bc113_maxPotential_has_no_child (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) {v : V} (hv : ¬ B v)
    (hmax : ∀ w, bc113_toB G B w ≤ bc113_toB G B v) :
    ¬ ∃ w, (bc113_bForest G B hreach).Adj v w ∧ bc113_toB G B v < bc113_toB G B w := by
  rintro ⟨w, _, hlt⟩
  exact absurd (hmax w) (by omega)
















theorem bc113_no_boundaryAnchored_on_triangle :
    ¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj),
        F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
        (∀ v, F.degree v = 1 → v = 0) := by
  classical
  rintro ⟨F, hFdec, _hle, hac, hmin, hleaf⟩
  
  have hdeg_le : ∀ v : Fin 3, F.degree v ≤ 2 := by
    intro v
    have hb : F.degree v ≤ (⊤ : SimpleGraph (Fin 3)).degree v := by
      
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      apply Finset.card_le_card
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      exact _hle hw
    have htop : (⊤ : SimpleGraph (Fin 3)).degree v = 2 := by fin_cases v <;> decide
    omega
  have hne1 : F.degree 1 ≠ 1 := fun h => absurd (hleaf 1 h) (by decide)
  have hne2 : F.degree 2 ≠ 1 := fun h => absurd (hleaf 2 h) (by decide)
  have hd1 : F.degree 1 = 2 := by have := hmin 1; have := hdeg_le 1; omega
  have hd2 : F.degree 2 = 2 := by have := hmin 2; have := hdeg_le 2; omega
  
  have hadj12 : F.Adj 1 2 := by
    by_contra hn
    
    have hsub : F.neighborFinset 1 ⊆ {0} := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      fin_cases w
      · simp
      · exact absurd hw F.irrefl
      · exact absurd hw hn
    have := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd1] at this
    simp at this
  have hadj10 : F.Adj 1 0 := by
    by_contra hn
    have hsub : F.neighborFinset 1 ⊆ {2} := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      fin_cases w
      · exact absurd hw hn
      · exact absurd hw F.irrefl
      · simp
    have := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd1] at this
    simp at this
  have hadj20 : F.Adj 2 0 := by
    by_contra hn
    have hsub : F.neighborFinset 2 ⊆ {1} := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      fin_cases w
      · exact absurd hw hn
      · simp
      · exact absurd hw F.irrefl
    have := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, hd2] at this
    simp at this
  
  set w : F.Walk 0 0 := SimpleGraph.Walk.cons hadj10.symm
      (SimpleGraph.Walk.cons hadj12 (SimpleGraph.Walk.cons hadj20 SimpleGraph.Walk.nil)) with hw
  refine hac w ?_
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · 
    rw [SimpleGraph.Walk.isTrail_def, hw]
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
    decide
  · 
    rw [hw]; exact fun h => (SimpleGraph.Walk.not_nil_cons) (h ▸ SimpleGraph.Walk.nil_nil)
  · 
    rw [hw]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
    decide







theorem bc113_boundaryAnchored_nonvacuous :
    ∃ (F : SimpleGraph (Fin 2)) (_ : DecidableRel F.Adj),
      F ≤ (⊤ : SimpleGraph (Fin 2)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
      (∀ v, F.degree v = 1 → (fun _ : Fin 2 => True) v) := by
  classical
  refine ⟨SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro x y hxy; rw [SimpleGraph.top_adj]
    exact (SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}).ne_of_adj hxy
  · 
    rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
    intro u v huv
    rw [SimpleGraph.fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rw [SimpleGraph.isBridge_iff]
    refine ⟨by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp [hmem], hne⟩, ?_⟩
    intro hreach
    obtain ⟨wlk⟩ := hreach
    have hbot : ((SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}).deleteEdges {s(u, v)}) = ⊥ := by
      ext p q
      rw [SimpleGraph.deleteEdges_adj]
      simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.bot_adj,
        iff_false, not_and]
      rintro ⟨hpq, hpqne⟩ hnpq
      apply hnpq
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hpq with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        subst_vars <;> tauto
    rw [hbot] at wlk
    exact hne (wlk.eq_of_length_eq_zero
      (by cases wlk with | nil => rfl | cons h _ => exact absurd h (by simp)))
  · intro v
    
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
      (SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}).degree_pos_iff_exists_adj]
    fin_cases v
    · exact ⟨1, by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp, by decide⟩⟩
    · exact ⟨0, by rw [SimpleGraph.fromEdgeSet_adj]
                   refine ⟨by simp, by decide⟩⟩
  · intro v _; trivial















theorem bc113_hub_degree_ge_three (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    [DecidableRel (bc113_bForest G B hreach).Adj] {v w₁ w₂ : V} (hv : ¬ B v)
    (ha₁ : (bc113_bForest G B hreach).Adj v w₁) (ha₂ : (bc113_bForest G B hreach).Adj v w₂)
    (hlt₁ : bc113_toB G B v < bc113_toB G B w₁) (hlt₂ : bc113_toB G B v < bc113_toB G B w₂)
    (hne : w₁ ≠ w₂) :
    3 ≤ (bc113_bForest G B hreach).degree v := by
  classical
  have hpar := bc113_bForest_adj_parent G B hreach hv
  have hparlt := (bc113_parent_spec G B hreach hv).2
  set p := bc113_parent G B hreach v with hp
  
  have hpw₁ : p ≠ w₁ := by intro h; rw [h] at hparlt; omega
  have hpw₂ : p ≠ w₂ := by intro h; rw [h] at hparlt; omega
  have hsub : {p, w₁, w₂} ⊆ (bc113_bForest G B hreach).neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl | rfl
    · exact hpar
    · exact ha₁
    · exact ha₂
  have hcard : ({p, w₁, w₂} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hpw₁, hpw₂⟩
  calc 3 = ({p, w₁, w₂} : Finset V).card := hcard.symm
    _ ≤ ((bc113_bForest G B hreach).neighborFinset v).card := Finset.card_le_card hsub
    _ = (bc113_bForest G B hreach).degree v := SimpleGraph.card_neighborFinset_eq_degree _ _










































theorem bc113_status :
    
    (∀ (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B),
      (bc113_bForest G B hreach) ≤ G ∧ (bc113_bForest G B hreach).IsAcyclic) ∧
    
    (∀ (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B),
      bc113_HasChild G B hreach → bc113_BoundaryHasChild G B hreach →
      ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
        F ≤ G ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v)) ∧
    
    (¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj),
        F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
        (∀ v, F.degree v = 1 → v = 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro G B hreach
    exact ⟨bc113_bForest_le G B hreach, bc113_bForest_acyclic G B hreach⟩
  · intro G B hreach hchild hbc
    exact bc113_boundaryAnchored_forest_exists G B hreach hchild hbc
  · exact bc113_no_boundaryAnchored_on_triangle

end StatMech.Walls
