/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/WrittenOnTheWallII/GraphConjecture314.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

import Mathlib
















import FormalConjecturesUtil









namespace WrittenOnTheWallII.GraphConjecture314

set_option linter.all false

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]














noncomputable def largestInducedPathSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { n | ∃ s : Finset α,
              s.card = n ∧
              (G.induce (s : Set α)).IsTree ∧
              ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 }


private lemma pathGraph_five_isTree : (pathGraph 5).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨pathGraph_connected 4, ?_⟩
  let f : Fin 4 → (pathGraph 5).edgeSet := fun i =>
    ⟨s(i.castSucc, i.succ), by
      rw [mem_edgeSet]
      simp [pathGraph_adj]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      simp only [f, Subtype.mk.injEq, Sym2.eq_iff] at hij
      rcases hij with h | h
      · apply Fin.ext
        exact congrArg (fun x : Fin 5 => x.val) h.1
      · have h1 := congrArg Fin.val h.1
        have h2 := congrArg Fin.val h.2
        simp at h1 h2
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.inductionOn with | _ u v =>
        rw [mem_edgeSet, pathGraph_adj] at he
        rcases he with huv | hvu
        · let i : Fin 4 := ⟨u.val, by omega⟩
          refine ⟨i, ?_⟩
          apply Subtype.ext
          rw [Sym2.eq_iff]
          left
          constructor <;> apply Fin.ext <;> simp [f, i, huv]
        · let i : Fin 4 := ⟨v.val, by omega⟩
          refine ⟨i, ?_⟩
          apply Subtype.ext
          rw [Sym2.eq_iff]
          right
          constructor <;> apply Fin.ext <;> simp [f, i, hvu]
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_eq_fintype_card]

private lemma pathGraph_five_degree (i : Fin 5)
    [Fintype ↑((pathGraph 5).neighborSet i)] : (pathGraph 5).degree i ≤ 2 := by
  have hs : (pathGraph 5).neighborFinset i ⊆ (cycleGraph 5).neighborFinset i := by
    intro w hw
    rw [mem_neighborFinset] at hw ⊢
    exact pathGraph_le_cycleGraph hw
  calc
    (pathGraph 5).degree i ≤ (cycleGraph 5).degree i := Finset.card_le_card hs
    _ = 2 := cycleGraph_degree_three_le

private lemma five_tuple_injective (a b c d e : α)
    (habn : a ≠ b) (hacn : a ≠ c) (hadn : a ≠ d) (haen : a ≠ e)
    (hbcn : b ≠ c) (hbdn : b ≠ d) (hben : b ≠ e)
    (hcdn : c ≠ d) (hcen : c ≠ e) (hden : d ≠ e) :
    Function.Injective (![a, b, c, d, e] : Fin 5 → α) := by
  simp only [Matrix.vecCons, Fin.cons_injective_iff]
  simp [habn, hacn, hadn, haen, hbcn, hbdn, hben, hcdn, hcen, hden,
    Function.Injective]

private lemma five_tuple_path_adj (G : SimpleGraph α) (a b c d e : α)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hae : ¬ G.Adj a e)
    (hbd : ¬ G.Adj b d) (hbe : ¬ G.Adj b e) (hce : ¬ G.Adj c e)
    (i j : Fin 5) :
    (pathGraph 5).Adj i j ↔ G.Adj (![a, b, c, d, e] i) (![a, b, c,d,e] j) := by
  fin_cases i <;> fin_cases j <;>
    simp [pathGraph_adj, G.adj_comm, hab, hbc, hcd, hde, hac, had, hae, hbd, hbe, hce]

private lemma inducedP5_witness (G : SimpleGraph α) [DecidableRel G.Adj]
    (a b c d e : α)
    (habn : a ≠ b) (hacn : a ≠ c) (hadn : a ≠ d) (haen : a ≠ e)
    (hbcn : b ≠ c) (hbdn : b ≠ d) (hben : b ≠ e)
    (hcdn : c ≠ d) (hcen : c ≠ e) (hden : d ≠ e)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hae : ¬ G.Adj a e)
    (hbd : ¬ G.Adj b d) (hbe : ¬ G.Adj b e) (hce : ¬ G.Adj c e) :
    ∃ s : Finset α, s.card = 5 ∧ (G.induce (s : Set α)).IsTree ∧
      ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 := by
  set_option maxHeartbeats 100000 in
    let s : Finset α := {a, b, c, d, e}
    have hcard : s.card = 5 := by
      simp [s, habn, hacn, hadn, haen, hbcn, hbdn, hben, hcdn, hcen, hden]
    let f : Fin 5 → (s : Set α) := fun i =>
      ⟨![a, b, c, d, e] i, by fin_cases i <;> simp [s]⟩
    have hv : Function.Injective (![a, b, c, d, e] : Fin 5 → α) :=
      five_tuple_injective a b c d e habn hacn hadn haen hbcn hbdn hben hcdn hcen hden
    have hfinj : Function.Injective f := by
      intro i j hij
      apply hv
      exact congrArg Subtype.val hij
    have hfbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, by simp [hcard]⟩
    let ef : Fin 5 ≃ (s : Set α) := Equiv.ofBijective f hfbij
    let gi : pathGraph 5 ≃g G.induce (s : Set α) :=
      { ef with
        map_rel_iff' := by
          intro i j
          simpa [ef, f] using
            (five_tuple_path_adj G a b c d e hab hbc hcd hde hac had hae hbd hbe hce i j).symm }
    refine ⟨s, hcard, gi.isTree_iff.mp pathGraph_five_isTree, ?_⟩
    intro v
    letI (i : Fin 5) : Fintype ↑((pathGraph 5).neighborSet i) := Fintype.ofFinite _
    calc
      (G.induce (s : Set α)).degree v =
          (G.induce (s : Set α)).degree (gi (gi.symm v)) := by simp
      _ = (pathGraph 5).degree (gi.symm v) := gi.degree_eq _
      _ ≤ 2 := pathGraph_five_degree _

private lemma no_inducedP5 (G : SimpleGraph α) [DecidableRel G.Adj]
    (hPath : largestInducedPathSize G ≤ 4)
    (a b c d e : α)
    (habn : a ≠ b) (hacn : a ≠ c) (hadn : a ≠ d) (haen : a ≠ e)
    (hbcn : b ≠ c) (hbdn : b ≠ d) (hben : b ≠ e)
    (hcdn : c ≠ d) (hcen : c ≠ e) (hden : d ≠ e)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hae : ¬ G.Adj a e)
    (hbd : ¬ G.Adj b d) (hbe : ¬ G.Adj b e) (hce : ¬ G.Adj c e) : False := by
  obtain ⟨s, hs, htree, hdeg⟩ := inducedP5_witness G a b c d e
    habn hacn hadn haen hbcn hbdn hben hcdn hcen hden
    hab hbc hcd hde hac had hae hbd hbe hce
  have hbdd : BddAbove {n : ℕ | ∃ s : Finset α, s.card = n ∧
      (G.induce (s : Set α)).IsTree ∧
      ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2} := by
    refine ⟨Fintype.card α, ?_⟩
    rintro n ⟨t, rfl, -, -⟩
    exact Finset.card_le_univ t
  have hfive : 5 ≤ largestInducedPathSize G := by
    apply le_csSup hbdd
    exact ⟨s, hs, htree, hdeg⟩
  omega

omit [Fintype α] in
private lemma exists_private_neighbor (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S) {x : α} (hx : x ∈ S) :
    ∃ p : α, G.Adj p x ∧ ∀ y ∈ S, y ≠ x → ¬ G.Adj p y := by
  classical
  unfold IsMinimalTotalDominatingSet IsTotalDominatingSet at hS
  have hn := hS.2 (S.erase x) (Finset.erase_ssubset hx)
  push Not at hn
  obtain ⟨p, hp⟩ := hn
  obtain ⟨w, hwS, hpw⟩ := hS.1 p
  have hwx : w = x := by
    by_contra hne
    exact hp w (Finset.mem_erase.mpr ⟨hne, hwS⟩) hpw
  subst w
  refine ⟨p, hpw, ?_⟩
  intro y hyS hyx hpy
  exact hp y (Finset.mem_erase.mpr ⟨hyx, hyS⟩) hpy

omit [Fintype α] in
private lemma two_le_card_of_minimal_total_dominating [Nonempty α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S) : 2 ≤ S.card := by
  unfold IsMinimalTotalDominatingSet IsTotalDominatingSet at hS
  let v : α := Classical.choice ‹Nonempty α›
  obtain ⟨x, hxS, -⟩ := hS.1 v
  obtain ⟨y, hyS, hxy⟩ := hS.1 x
  have hxyne : x ≠ y := hxy.ne
  have hsub : {x, y} ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  simpa [hxyne] using hc

omit [Fintype α] in
private lemma structure_of_card_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S) (hc : S.card = 2) :
    ∃ x y, x ≠ y ∧ G.Adj x y ∧ (∀ v, G.Adj v x ∨ G.Adj v y) := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
  unfold IsMinimalTotalDominatingSet IsTotalDominatingSet at hS
  have hdom := hS.1
  obtain ⟨w, hw, hxw⟩ := hdom x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  have hadj : G.Adj x y := by
    rcases hw with hw | hw
    · exact (hxw.ne hw.symm).elim
    · simpa [hw] using hxw
  refine ⟨x, y, hxy, hadj, ?_⟩
  intro v
  obtain ⟨w, hw, hvw⟩ := hdom v
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact Or.inl hvw
  · exact Or.inr hvw

private lemma no_inducedP4_in_minimal (G : SimpleGraph α) [DecidableRel G.Adj]
    (hPath : largestInducedPathSize G ≤ 4)
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S)
    {a b c d : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (habn : a ≠ b) (hacn : a ≠ c) (hadn : a ≠ d)
    (hbcn : b ≠ c) (hbdn : b ≠ d) (hcdn : c ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hbd : ¬ G.Adj b d) : False := by
  obtain ⟨p, hpa, hp⟩ := exists_private_neighbor G S hS ha
  have hpb : ¬ G.Adj p b := hp b hb habn.symm
  have hpc : ¬ G.Adj p c := hp c hc hacn.symm
  have hpd : ¬ G.Adj p d := hp d hd hadn.symm
  have hpa_ne : p ≠ a := hpa.ne
  have hpb_ne : p ≠ b := by
    intro h
    subst p
    exact hpc hbc
  have hpc_ne : p ≠ c := by
    intro h
    subst p
    exact hpb hbc.symm
  have hpd_ne : p ≠ d := by
    intro h
    subst p
    exact hpc hcd.symm
  exact no_inducedP5 G hPath p a b c d hpa_ne hpb_ne hpc_ne hpd_ne
    habn hacn hadn hbcn hbdn hcdn hpa hab hbc hcd hpb hpc hpd hac had hbd

private lemma forced_private_edge (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S)
    {x z m p q : α}
    (hx : x ∈ S) (hz : z ∈ S) (hm : m ∈ S) (hxz : x ≠ z)
    (hxm : G.Adj x m) (hzm : G.Adj z m)
    (hpx : G.Adj p x) (hp : ∀ y ∈ S, y ≠ x → ¬ G.Adj p y)
    (hqz : G.Adj q z) (hq : ∀ y ∈ S, y ≠ z → ¬ G.Adj q y) : G.Adj p q := by
  by_contra hpq
  have hxm_ne : x ≠ m := hxm.ne
  have hzm_ne : z ≠ m := hzm.ne
  have hpm : ¬ G.Adj p m := hp m hm hxm_ne.symm
  have hpz : ¬ G.Adj p z := hp z hz hxz.symm
  have hqx : ¬ G.Adj q x := hq x hx hxz
  have hqm : ¬ G.Adj q m := hq m hm hzm_ne.symm
  have hxz_adj : ¬ G.Adj x z := by
    intro h
    exact hTriFree x m z hxm hzm.symm h.symm
  have hpnx : p ≠ x := hpx.ne
  have hpnm : p ≠ m := by
    intro h; subst p; exact hpz hzm.symm
  have hpnz : p ≠ z := by
    intro h; subst p; exact hpm hzm
  have hpnq : p ≠ q := by
    intro h; subst p; exact hqx hpx
  have hxnm : x ≠ m := hxm.ne
  have hxnz : x ≠ z := hxz
  have hxnq : x ≠ q := by
    intro h; subst q; exact hqm hxm
  have hmnz : m ≠ z := hzm.symm.ne
  have hmnq : m ≠ q := by
    intro h; subst q; exact hqx hxm.symm
  have hznq : z ≠ q := hqz.symm.ne
  exact no_inducedP5 G hPath p x m z q hpnx hpnm hpnz hpnq
    hxnm hxnz hxnq hmnz hmnq hznq hpx hxm hzm.symm hqz.symm hpm hpz hpq hxz_adj
      (fun h => hqx h.symm) (fun h => hqm h.symm)

private lemma same_neighbor_reachable (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S)
    (u : α) (a b : (S : Set α))
    (hua : G.Adj u a) (hub : G.Adj u b) :
    (G.induce (S : Set α)).Reachable a b := by
  let H := G.induce (S : Set α)
  have hTD : IsTotalDominatingSet G S := hS.1
  have hedge {x y : (S : Set α)} (hxy : G.Adj (x : α) (y : α)) : H.Reachable x y :=
    (show H.Adj x y from hxy).reachable
  by_contra hn
  have hab : ¬ G.Adj (a : α) b := fun h => hn (hedge h)
  obtain ⟨av, havS, haa'⟩ := hTD (a : α)
  obtain ⟨bv, hbvS, hbb'⟩ := hTD (b : α)
  let a' : (S : Set α) := ⟨av, havS⟩
  let b' : (S : Set α) := ⟨bv, hbvS⟩
  have haa'' : G.Adj (a : α) a' := haa'
  have hbb'' : G.Adj (b : α) b' := hbb'
  have haaR : H.Reachable a a' := hedge haa''
  have hbbR : H.Reachable b b' := hedge hbb''
  have hcross {x y : (S : Set α)} (hxa : H.Reachable x a)
      (hby : H.Reachable b y) : ¬ G.Adj (x : α) y := by
    intro hxy
    exact hn (hxa.symm.trans ((hedge hxy).trans hby.symm))
  have ha'b : ¬ G.Adj (a' : α) b := hcross haaR.symm .rfl
  have ha'b' : ¬ G.Adj (a' : α) b' := hcross haaR.symm hbbR
  have hab' : ¬ G.Adj (a : α) b' := hcross .rfl hbbR
  have ha'u : ¬ G.Adj (a' : α) u := by
    intro h
    exact hTriFree (a' : α) (a : α) u haa''.symm hua.symm h.symm
  have hub' : ¬ G.Adj u (b' : α) := by
    intro h
    exact hTriFree u (b : α) (b' : α) hub hbb'' h.symm
  have e1 : G.Adj (a' : α) a := haa''.symm
  have e2 : G.Adj (a : α) u := hua.symm
  have e3 : G.Adj u b := hub
  have e4 : G.Adj (b : α) b' := hbb''
  have n12 : (a' : α) ≠ a := e1.ne
  have n23 : (a : α) ≠ u := e2.ne
  have n34 : u ≠ b := e3.ne
  have n45 : (b : α) ≠ b' := e4.ne
  have n13 : (a' : α) ≠ u := by intro h; subst u; exact ha'b e3
  have n14 : (a' : α) ≠ b := by
    intro h; apply hab; rw [← h]; exact e1.symm
  have n15 : (a' : α) ≠ b' := by
    intro h; apply hab'; rw [← h]; exact e1.symm
  have n24 : (a : α) ≠ b := by
    intro h
    have : a = b := Subtype.ext h
    subst b
    exact hn .rfl
  have n25 : (a : α) ≠ b' := by
    intro h; apply hab; rw [h]; exact e4.symm
  have n35 : u ≠ b' := by
    intro h; apply hab'; rw [← h]; exact e2
  exact no_inducedP5 G hPath (a' : α) a u b b'
    n12 n13 n14 n15 n23 n24 n25 n34 n35 n45
    e1 e2 e3 e4 ha'u ha'b ha'b' hab hab' hub'

private lemma adjacent_vertices_have_reachable_choices
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S)
    (u v : α) (a b : (S : Set α))
    (huv : G.Adj u v) (hua : G.Adj u a) (hvb : G.Adj v b) :
    (G.induce (S : Set α)).Reachable a b := by
  let H := G.induce (S : Set α)
  have hTD : IsTotalDominatingSet G S := hS.1
  have hedge {x y : (S : Set α)} (hxy : G.Adj (x : α) (y : α)) : H.Reachable x y :=
    (show H.Adj x y from hxy).reachable
  by_contra hn
  obtain ⟨av, havS, haa'⟩ := hTD (a : α)
  let a' : (S : Set α) := ⟨av, havS⟩
  have haa'' : G.Adj (a : α) a' := haa'
  have haaR : H.Reachable a a' := hedge haa''
  have ha'u : ¬ G.Adj (a' : α) u := by
    intro h
    exact hTriFree (a' : α) (a : α) u haa''.symm hua.symm h.symm
  have ha'v : ¬ G.Adj (a' : α) v := by
    intro h
    exact hn (haaR.trans (same_neighbor_reachable G hTriFree hPath S hS v a' b h.symm hvb))
  have ha'b : ¬ G.Adj (a' : α) b := by
    intro h
    exact hn (haaR.trans (hedge h))
  have hav : ¬ G.Adj (a : α) v := by
    intro h
    exact hn (same_neighbor_reachable G hTriFree hPath S hS v a b h.symm hvb)
  have hab : ¬ G.Adj (a : α) b := fun h => hn (hedge h)
  have hub : ¬ G.Adj u (b : α) := by
    intro h
    exact hn (same_neighbor_reachable G hTriFree hPath S hS u a b hua h)
  have e1 : G.Adj (a' : α) a := haa''.symm
  have e2 : G.Adj (a : α) u := hua.symm
  have e3 : G.Adj u v := huv
  have e4 : G.Adj v b := hvb
  have n12 := e1.ne
  have n23 := e2.ne
  have n34 := e3.ne
  have n45 := e4.ne
  have n13 : (a' : α) ≠ u := by
    intro h; apply ha'v; rw [h]; exact e3
  have n14 : (a' : α) ≠ v := by
    intro h; apply hav; rw [← h]; exact e1.symm
  have n15 : (a' : α) ≠ b := by
    intro h
    apply hab
    rw [← h]
    exact e1.symm
  have n24 : (a : α) ≠ v := by
    intro h; apply hn; apply hedge; rw [h]; exact e4
  have n25 : (a : α) ≠ b := by
    intro h
    apply hn
    exact Eq.recOn (Subtype.ext h) (.rfl : H.Reachable a a)
  have n35 : u ≠ b := by
    intro h; apply hn; apply hedge; rw [← h]; exact hua.symm
  exact no_inducedP5 G hPath (a' : α) a u v b
    n12 n13 n14 n15 n23 n24 n25 n34 n35 n45
    e1 e2 e3 e4 ha'u ha'v ha'b hav hab hub

private lemma induced_minimal_connected (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S) :
    (G.induce (S : Set α)).Connected := by
  classical
  let H := G.induce (S : Set α)
  have hTD : IsTotalDominatingSet G S := hS.1
  let f : α → (S : Set α) := fun v =>
    ⟨Classical.choose (hTD v), (Classical.choose_spec (hTD v)).1⟩
  have hfadj (v : α) : G.Adj v (f v : α) := (Classical.choose_spec (hTD v)).2
  have hedge {x y : (S : Set α)} (hxy : G.Adj (x : α) (y : α)) : H.Reachable x y := by
    exact (show H.Adj x y from hxy).reachable
  have hadjmap {u v : α} (huv : G.Adj u v) : H.Reachable (f u) (f v) :=
    adjacent_vertices_have_reachable_choices G hTriFree hPath S hS
      u v (f u) (f v) huv (hfadj u) (hfadj v)
  have hwalk {u v : α} (w : G.Walk u v) : H.Reachable (f u) (f v) := by
    induction w with
    | nil => exact .rfl
    | cons h w ih => exact (hadjmap h).trans ih
  rw [connected_iff]
  constructor
  · intro x y
    have hxf : H.Reachable x (f (x : α)) := hedge (hfadj (x : α))
    have hyf : H.Reachable y (f (y : α)) := hedge (hfadj (y : α))
    obtain ⟨w⟩ := hG (x : α) (y : α)
    exact hxf.trans ((hwalk w).trans hyf.symm)
  · obtain ⟨v⟩ := hG.nonempty
    exact ⟨f v⟩

private lemma edge_neighborhood_covers_minimal
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S)
    (hconn : (G.induce (S : Set α)).Connected)
    (a b : (S : Set α)) (hab : G.Adj (a : α) b) :
    ∀ x : (S : Set α), G.Adj (x : α) a ∨ G.Adj (x : α) b := by
  let H := G.induce (S : Set α)
  let D := fun z : (S : Set α) => G.Adj (z : α) a ∨ G.Adj (z : α) b
  have hstep {u v : (S : Set α)} (huv : H.Adj u v) (hu : D u) : D v := by
    have huv' : G.Adj (u : α) v := huv
    by_contra hv
    simp only [D, not_or] at hv
    rcases hu with hua | hub
    · have hubn : ¬ G.Adj (u : α) b := by
        intro h
        exact hTriFree (u : α) a b hua hab h.symm
      have hvu : (v : α) ≠ u := huv'.symm.ne
      have hva : (v : α) ≠ a := by
        intro h; apply hv.2; rw [h]; exact hab
      have hvb : (v : α) ≠ b := by
        intro h; apply hv.1; rw [h]; exact hab.symm
      have hua_ne : (u : α) ≠ a := hua.ne
      have hub_ne : (u : α) ≠ b := by
        intro h; apply hv.2; rw [← h]; exact huv'.symm
      exact no_inducedP4_in_minimal G hPath S hS v.property u.property a.property b.property
        hvu hva hvb hua_ne hub_ne hab.ne huv'.symm hua hab hv.1 hv.2 hubn
    · have huan : ¬ G.Adj (u : α) a := by
        intro h
        exact hTriFree (u : α) b a hub hab.symm h.symm
      have hvu : (v : α) ≠ u := huv'.symm.ne
      have hvb : (v : α) ≠ b := by
        intro h; apply hv.1; rw [h]; exact hab.symm
      have hva : (v : α) ≠ a := by
        intro h; apply hv.2; rw [h]; exact hab
      have hub_ne : (u : α) ≠ b := hub.ne
      have hua_ne : (u : α) ≠ a := by
        intro h; apply hv.1; rw [← h]; exact huv'.symm
      exact no_inducedP4_in_minimal G hPath S hS v.property u.property b.property a.property
        hvu hvb hva hub_ne hua_ne hab.symm.ne huv'.symm hub hab.symm hv.2 hv.1 huan
  have hwalk {u v : (S : Set α)} (w : H.Walk u v) (hu : D u) : D v := by
    induction w with
    | nil => exact hu
    | cons h w ih => exact ih (hstep h hu)
  intro x
  obtain ⟨w⟩ := hconn a x
  exact hwalk w (Or.inr hab)

private lemma no_private_k22 (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (x z y w px pz py pw : α)
    (hxy : G.Adj x y) (hxw : G.Adj x w) (hzy : G.Adj z y) (hzw : G.Adj z w)
    (hpx : G.Adj px x) (hpz : G.Adj pz z) (hpy : G.Adj py y) (hpw : G.Adj pw w)
    (hpxzS : ¬ G.Adj px z) (hpxyS : ¬ G.Adj px y) (hpxwS : ¬ G.Adj px w)
    (hpzxS : ¬ G.Adj pz x) (hpzyS : ¬ G.Adj pz y) (hpzwS : ¬ G.Adj pz w)
    (hpyxS : ¬ G.Adj py x) (hpyzS : ¬ G.Adj py z) (hpywS : ¬ G.Adj py w)
    (hpwxS : ¬ G.Adj pw x) (hpwzS : ¬ G.Adj pw z) (hpwyS : ¬ G.Adj pw y)
    (hpxz : G.Adj px pz) (hpyw : G.Adj py pw) : False := by
  have hxy0 : x ≠ y := hxy.ne
  have hxw0 : x ≠ w := hxw.ne
  have hzy0 : z ≠ y := hzy.ne
  have hzw0 : z ≠ w := hzw.ne
  have hpxx0 : px ≠ x := hpx.ne
  have hpxz0 : px ≠ z := by
    intro h; apply hpxyS; rw [h]; exact hzy
  have hpxy0 : px ≠ y := by
    intro h; apply hpxzS; rw [h]; exact hzy.symm
  have hpxw0 : px ≠ w := by
    intro h; apply hpxzS; rw [h]; exact hzw.symm
  have hpzx0 : pz ≠ x := by
    intro h; apply hpzyS; rw [h]; exact hxy
  have hpzz0 : pz ≠ z := hpz.ne
  have hpzy0 : pz ≠ y := by
    intro h; apply hpzxS; rw [h]; exact hxy.symm
  have hpzw0 : pz ≠ w := by
    intro h; apply hpzxS; rw [h]; exact hxw.symm
  have hpyx0 : py ≠ x := by
    intro h; apply hpywS; rw [h]; exact hxw
  have hpyz0 : py ≠ z := by
    intro h; apply hpywS; rw [h]; exact hzw
  have hpyy0 : py ≠ y := hpy.ne
  have hpyw0 : py ≠ w := by
    intro h; apply hpyxS; rw [h]; exact hxw.symm
  have hpwx0 : pw ≠ x := by
    intro h; apply hpwyS; rw [h]; exact hxy
  have hpwz0 : pw ≠ z := by
    intro h; apply hpwyS; rw [h]; exact hzy
  have hpwy0 : pw ≠ y := by
    intro h; apply hpwzS; rw [h]; exact hzy.symm
  have hpww0 : pw ≠ w := hpw.ne
  have hpxpy0 : px ≠ py := by
    intro h; apply hpyxS; rw [← h]; exact hpx
  have hpxpw0 : px ≠ pw := by
    intro h; apply hpwxS; rw [← h]; exact hpx
  have hpzpy0 : pz ≠ py := by
    intro h; apply hpyzS; rw [← h]; exact hpz
  have hpzpw0 : pz ≠ pw := by
    intro h; apply hpwzS; rw [← h]; exact hpz
  by_cases hpxpy : G.Adj px py
  · have hpzpyN : ¬ G.Adj pz py := by
      intro h
      exact hTriFree pz px py hpxz.symm hpxpy h.symm
    have hpxpwN : ¬ G.Adj px pw := by
      intro h
      exact hTriFree px py pw hpxpy hpyw h.symm
    by_cases hpzpw : G.Adj pz pw
    · exact no_inducedP5 G hPath x y py pw pz
        hxy0 hpyx0.symm hpwx0.symm hpzx0.symm hpyy0.symm hpwy0.symm hpzy0.symm
        hpyw.ne hpzpy0.symm hpzpw.symm.ne
        hxy hpy.symm hpyw hpzpw.symm
        (fun h => hpyxS h.symm) (fun h => hpwxS h.symm)
        (fun h => hpzxS h.symm) (fun h => hpwyS h.symm)
        (fun h => hpzyS h.symm) (fun h => hpzpyN h.symm)
    · exact no_inducedP5 G hPath px pz z w pw
        hpxz.ne hpxz0 hpxw0 hpxpw0 hpzz0 hpzw0 hpzpw0 hzw0
        hpwz0.symm hpww0.symm
        hpxz hpz hzw hpw.symm hpxzS hpxwS hpxpwN hpzwS hpzpw
        (fun h => hpwzS h.symm)
  · by_cases hpzpy : G.Adj pz py
    · have hpzpwN : ¬ G.Adj pz pw := by
        intro h
        exact hTriFree pz py pw hpzpy hpyw h.symm
      by_cases hpxpw : G.Adj px pw
      · exact no_inducedP5 G hPath z y py pw px
          hzy0 hpyz0.symm hpwz0.symm hpxz0.symm hpyy0.symm hpwy0.symm
          hpxy0.symm hpyw.ne hpxpy0.symm hpxpw.symm.ne
          hzy hpy.symm hpyw hpxpw.symm
          (fun h => hpyzS h.symm) (fun h => hpwzS h.symm)
          (fun h => hpxzS h.symm) (fun h => hpwyS h.symm)
          (fun h => hpxyS h.symm) (fun h => hpxpy h.symm)
      · exact no_inducedP5 G hPath pz px x w pw
          hpxz.symm.ne hpzx0 hpzw0 hpzpw0 hpxx0 hpxw0 hpxpw0 hxw0
          hpwx0.symm hpww0.symm
          hpxz.symm hpx hxw hpw.symm hpzxS hpzwS hpzpwN hpxwS hpxpw
          (fun h => hpwxS h.symm)
    · exact no_inducedP5 G hPath px pz z y py
        hpxz.ne hpxz0 hpxy0 hpxpy0 hpzz0 hpzy0 hpzpy0 hzy0
        hpyz0.symm hpyy0.symm
        hpxz hpz hzy hpy.symm hpxzS hpxyS hpxpy hpzyS hpzpy
        (fun h => hpyzS h.symm)

private lemma opposite_side_adjacent
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S)
    (r a b s : (S : Set α))
    (hra : G.Adj (r : α) a) (hab : G.Adj (a : α) b)
    (hsb : G.Adj (s : α) b) : G.Adj (r : α) s := by
  by_contra hrs
  have hrb : ¬ G.Adj (r : α) b := by
    intro h
    exact hTriFree (r : α) a b hra hab h.symm
  have has : ¬ G.Adj (a : α) s := by
    intro h
    exact hTriFree (s : α) b a hsb hab.symm h
  have hne1 : (r : α) ≠ a := hra.ne
  have hne2 : (r : α) ≠ b := by
    intro h; apply hrs; rw [h]; exact hsb.symm
  have hne3 : (r : α) ≠ s := by
    intro h; apply has; rw [← h]; exact hra.symm
  have hne4 : (a : α) ≠ b := hab.ne
  have hne5 : (a : α) ≠ s := by
    intro h; apply hrs; rw [← h]; exact hra
  have hne6 : (b : α) ≠ s := hsb.symm.ne
  exact no_inducedP4_in_minimal G hPath S hS r.property a.property b.property s.property
    hne1 hne2 hne3 hne4 hne5 hne6 hra hab hsb.symm hrb hrs has

private lemma common_neighbor_side_card_le_two
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S)
    (C : Finset (S : Set α)) (m : (S : Set α))
    (hC : ∀ x, x ∈ C ↔ G.Adj (x : α) m) : C.card ≤ 2 := by
  by_contra hn
  have hlt : 2 < C.card := by omega
  rw [Finset.two_lt_card_iff] at hlt
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := hlt
  obtain ⟨px, hpx, hpxp⟩ := exists_private_neighbor G S hS x.property
  obtain ⟨py, hpy, hpyp⟩ := exists_private_neighbor G S hS y.property
  obtain ⟨pz, hpz, hpzp⟩ := exists_private_neighbor G S hS z.property
  have hxm := (hC x).mp hx
  have hym := (hC y).mp hy
  have hzm := (hC z).mp hz
  have pxy := forced_private_edge G hTriFree hPath S hS x.property y.property m.property
    (fun h => hxy (Subtype.ext h)) hxm hym hpx hpxp hpy hpyp
  have pyz := forced_private_edge G hTriFree hPath S hS y.property z.property m.property
    (fun h => hyz (Subtype.ext h)) hym hzm hpy hpyp hpz hpzp
  have pxz := forced_private_edge G hTriFree hPath S hS x.property z.property m.property
    (fun h => hxz (Subtype.ext h)) hxm hzm hpx hpxp hpz hpzp
  exact hTriFree px py pz pxy pyz pxz.symm

private lemma minimal_card_le_three (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (S : Finset α) (hS : IsMinimalTotalDominatingSet G S) : S.card ≤ 3 := by
  classical
  let H := G.induce (S : Set α)
  have hconn : H.Connected := induced_minimal_connected G hG hTriFree hPath S hS
  have hTD : IsTotalDominatingSet G S := hS.1
  obtain ⟨a⟩ := hconn.nonempty
  obtain ⟨bv, hbS, hab⟩ := hTD (a : α)
  let b : (S : Set α) := ⟨bv, hbS⟩
  have hab' : G.Adj (a : α) b := hab
  have hcover (x : (S : Set α)) : G.Adj (x : α) a ∨ G.Adj (x : α) b :=
    edge_neighborhood_covers_minimal G hTriFree hPath S hS hconn a b hab' x
  let A : Finset (S : Set α) := Finset.univ.filter (fun x => G.Adj (x : α) a)
  let B : Finset (S : Set α) := Finset.univ.filter (fun x => G.Adj (x : α) b)
  have hAB : A ∪ B = Finset.univ := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_univ, iff_true]
    exact hcover x
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact hTriFree (x : α) a b hx hab' hy.symm
  have side_le_two (C : Finset (S : Set α)) (m : (S : Set α))
      (hC : ∀ x, x ∈ C ↔ G.Adj (x : α) m) : C.card ≤ 2 :=
    common_neighbor_side_card_le_two G hTriFree hPath S hS C m hC
  have hA : A.card ≤ 2 := side_le_two A a (by intro x; simp [A])
  have hB : B.card ≤ 2 := side_le_two B b (by intro x; simp [B])
  have hcard : S.card = A.card + B.card := by
    rw [← Finset.card_union_of_disjoint hdis, hAB]
    simp
  have hfour : S.card ≤ 4 := by omega
  by_contra hn
  have hScard : S.card = 4 := by omega
  have hAc : A.card = 2 := by omega
  have hBc : B.card = 2 := by omega
  obtain ⟨x, z, hxz, hArep⟩ := Finset.card_eq_two.mp hAc
  obtain ⟨y, w, hyw, hBrep⟩ := Finset.card_eq_two.mp hBc
  have hxA : x ∈ A := by simp [hArep]
  have hzA : z ∈ A := by simp [hArep]
  have hyB : y ∈ B := by simp [hBrep]
  have hwB : w ∈ B := by simp [hBrep]
  have hxa : G.Adj (x : α) a := by simpa [A] using hxA
  have hza : G.Adj (z : α) a := by simpa [A] using hzA
  have hyb : G.Adj (y : α) b := by simpa [B] using hyB
  have hwb : G.Adj (w : α) b := by simpa [B] using hwB
  have cross (r s : (S : Set α)) (hra : G.Adj (r : α) a)
      (hsb : G.Adj (s : α) b) : G.Adj (r : α) s :=
    opposite_side_adjacent G hTriFree hPath S hS r a b s hra hab' hsb
  have hxy' := cross x y hxa hyb
  have hxw := cross x w hxa hwb
  have hzy := cross z y hza hyb
  have hzw := cross z w hza hwb
  obtain ⟨px, hpx, hpxp⟩ := exists_private_neighbor G S hS x.property
  obtain ⟨pz, hpz, hpzp⟩ := exists_private_neighbor G S hS z.property
  obtain ⟨py, hpy, hpyp⟩ := exists_private_neighbor G S hS y.property
  obtain ⟨pw, hpw, hpwp⟩ := exists_private_neighbor G S hS w.property
  have hpxz := forced_private_edge G hTriFree hPath S hS x.property z.property a.property
    (fun h => hxz (Subtype.ext h)) hxa hza hpx hpxp hpz hpzp
  have hpyw := forced_private_edge G hTriFree hPath S hS y.property w.property b.property
    (fun h => hyw (Subtype.ext h)) hyb hwb hpy hpyp hpw hpwp
  have hxz0 : (x : α) ≠ z := fun h => hxz (Subtype.ext h)
  have hyw0 : (y : α) ≠ w := fun h => hyw (Subtype.ext h)
  have hxy0 : (x : α) ≠ y := hxy'.ne
  have hxw0 : (x : α) ≠ w := hxw.ne
  have hzy0 : (z : α) ≠ y := hzy.ne
  have hzw0 : (z : α) ≠ w := hzw.ne
  have hpxzS : ¬ G.Adj px z := hpxp (z : α) z.property hxz0.symm
  have hpxyS : ¬ G.Adj px y := hpxp (y : α) y.property hxy0.symm
  have hpxwS : ¬ G.Adj px w := hpxp (w : α) w.property hxw0.symm
  have hpzxS : ¬ G.Adj pz x := hpzp (x : α) x.property hxz0
  have hpzyS : ¬ G.Adj pz y := hpzp (y : α) y.property hzy0.symm
  have hpzwS : ¬ G.Adj pz w := hpzp (w : α) w.property hzw0.symm
  have hpyxS : ¬ G.Adj py x := hpyp (x : α) x.property hxy0
  have hpyzS : ¬ G.Adj py z := hpyp (z : α) z.property hzy0
  have hpywS : ¬ G.Adj py w := hpyp (w : α) w.property hyw0.symm
  have hpwxS : ¬ G.Adj pw x := hpwp (x : α) x.property hxw0
  have hpwzS : ¬ G.Adj pw z := hpwp (z : α) z.property hzw0
  have hpwyS : ¬ G.Adj pw y := hpwp (y : α) y.property hyw0
  exact no_private_k22 G hTriFree hPath (x : α) (z : α) (y : α) (w : α)
    px pz py pw hxy' hxw hzy hzw hpx hpz hpy hpw
    hpxzS hpxyS hpxwS hpzxS hpzyS hpzwS hpyxS hpyzS hpywS hpwxS hpwzS hpwyS
    hpxz hpyw

private lemma card_two_cover_forbids_three_path
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (T : Finset α) (hT : IsMinimalTotalDominatingSet G T)
    (x y : α) (hcover : ∀ v, G.Adj v x ∨ G.Adj v y)
    {a b c : α} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T)
    (hac : a ≠ c) (hab : G.Adj a b) (hbc : G.Adj b c) : False := by
  obtain ⟨pa, hpa, hpap⟩ := exists_private_neighbor G T hT ha
  obtain ⟨pc, hpc, hpcp⟩ := exists_private_neighbor G T hT hc
  have hpac : G.Adj pa pc := forced_private_edge G hTriFree hPath T hT
    ha hc hb hac hab hbc.symm hpa hpap hpc hpcp
  rcases hcover a with hax | hay
  · have hby : G.Adj b y := by
      rcases hcover b with hbx | hby
      · exact (hTriFree a b x hab hbx hax.symm).elim
      · exact hby
    have hcx : G.Adj c x := by
      rcases hcover c with hcx | hcy
      · exact hcx
      · exact (hTriFree b c y hbc hcy hby.symm).elim
    have hpay : G.Adj pa y := by
      rcases hcover pa with hpax | hpay
      · exact (hTriFree pa a x hpa hax hpax.symm).elim
      · exact hpay
    have hpcy : G.Adj pc y := by
      rcases hcover pc with hpcx | hpcy
      · exact (hTriFree pc c x hpc hcx hpcx.symm).elim
      · exact hpcy
    exact hTriFree pa pc y hpac hpcy hpay.symm
  · have hbx : G.Adj b x := by
      rcases hcover b with hbx | hby
      · exact hbx
      · exact (hTriFree a b y hab hby hay.symm).elim
    have hcy : G.Adj c y := by
      rcases hcover c with hcx | hcy
      · exact (hTriFree b c x hbc hcx hbx.symm).elim
      · exact hcy
    have hpax : G.Adj pa x := by
      rcases hcover pa with hpax | hpay
      · exact hpax
      · exact (hTriFree pa a y hpa hay hpay.symm).elim
    have hpcx : G.Adj pc x := by
      rcases hcover pc with hpcx | hpcy
      · exact hpcx
      · exact (hTriFree pc c y hpc hcy hpcy.symm).elim
    exact hTriFree pa pc x hpac hpcx hpax.symm

private lemma no_minimal_total_dominating_sets_of_card_two_and_three
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4)
    (S T : Finset α) (hS : IsMinimalTotalDominatingSet G S)
    (hT : IsMinimalTotalDominatingSet G T) (hScard : S.card = 2)
    (hTcard : T.card = 3) : False := by
  classical
  obtain ⟨x, y, hxy0, hxy, hcover⟩ := structure_of_card_two G S hS hScard
  have path_case {a b c : α} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T)
      (hac : a ≠ c) (hab : G.Adj a b) (hbc : G.Adj b c) : False :=
    card_two_cover_forbids_three_path G hTriFree hPath T hT x y hcover
      ha hb hc hac hab hbc
  obtain ⟨a, b, c, hab0, hac0, hbc0, hTrep⟩ := Finset.card_eq_three.mp hTcard
  have haT : a ∈ T := by simp [hTrep]
  have hbT : b ∈ T := by simp [hTrep]
  have hcT : c ∈ T := by simp [hTrep]
  obtain ⟨u, huT, hau⟩ := hT.1 a
  rw [hTrep] at huT
  simp only [Finset.mem_insert, Finset.mem_singleton] at huT
  rcases huT with rfl | rfl | rfl
  · exact hau.ne rfl
  · obtain ⟨v, hvT, hcv⟩ := hT.1 c
    rw [hTrep] at hvT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvT
    rcases hvT with rfl | rfl | rfl
    · exact path_case hbT haT hcT hbc0 hau.symm hcv.symm
    · exact path_case haT hbT hcT hac0 hau hcv.symm
    · exact hcv.ne rfl
  · obtain ⟨v, hvT, hbv⟩ := hT.1 b
    rw [hTrep] at hvT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvT
    rcases hvT with rfl | rfl | rfl
    · exact path_case hcT haT hbT hbc0.symm hau.symm hbv.symm
    · exact hbv.ne rfl
    · exact path_case haT hcT hbT hab0 hau hbv.symm
















@[category research open, AMS 5]
theorem conjecture314 [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G := by
  unfold IsWellTotallyDominated
  intro S T hS hT
  have hSlo : 2 ≤ S.card := two_le_card_of_minimal_total_dominating G S hS
  have hTlo : 2 ≤ T.card := two_le_card_of_minimal_total_dominating G T hT
  have hShi : S.card ≤ 3 := minimal_card_le_three G hG hTriFree hPath S hS
  have hThi : T.card ≤ 3 := minimal_card_le_three G hG hTriFree hPath T hT
  by_contra hne
  have hcards : (S.card = 2 ∧ T.card = 3) ∨ (T.card = 2 ∧ S.card = 3) := by
    omega
  rcases hcards with ⟨hS2, hT3⟩ | ⟨hT2, hS3⟩
  · exact no_minimal_total_dominating_sets_of_card_two_and_three G hTriFree hPath
      S T hS hT hS2 hT3
  · exact no_minimal_total_dominating_sets_of_card_two_and_three G hTriFree hPath
      T S hT hS hT2 hS3
end WrittenOnTheWallII.GraphConjecture314
