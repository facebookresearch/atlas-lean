/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted

/-! # Finite Menger theorem (edge form)

Proves the edge version of Menger's theorem for finite simple graphs: the maximum number of
pairwise edge-disjoint `s-t` paths equals the minimum size of an `s-t` edge cut.
-/

/-- Family `paths` of `s-t` paths is edge-disjoint when distinct paths share no edge. -/
def IsEdgeDisjointSTPaths {V : Type*} {G : SimpleGraph V}
    {s t : V} {n : ℕ} (paths : Fin n → G.Path s t) : Prop :=
  ∀ i j, i ≠ j → ∀ e : Sym2 V, e ∈ (paths i).val.edges → e ∉ (paths j).val.edges

/-- `C` is an `s-t` edge cut when `C ⊆ G.edgeSet` and deleting `C` disconnects `s` from `t`. -/
def IsSTEdgeCut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (C : Finset (Sym2 V)) : Prop :=
  (↑C : Set (Sym2 V)) ⊆ G.edgeSet ∧ ¬ (G.deleteEdges (↑C : Set (Sym2 V))).Reachable s t

/-- Weak duality: every `s-t` path meets every `s-t` edge cut
(Mathlib's `SimpleGraph.Walk.exists_mem_edges_of_not_reachable_deleteEdges`). -/
private theorem path_meets_cut {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s t : V}
    (p : G.Path s t) (C : Finset (Sym2 V)) (hC : IsSTEdgeCut G s t C) :
    ∃ e ∈ C, e ∈ p.val.edges :=
  p.val.exists_mem_edges_of_not_reachable_deleteEdges (s := (↑C : Set (Sym2 V))) hC.2

/-- Weak duality, counting form: an edge-disjoint family of `l` paths injects into any
`s-t` edge cut, so `l ≤ C.card`. -/
private theorem weak_duality_aux {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s t : V}
    {l : ℕ} (paths : Fin l → G.Path s t) (hdisj : IsEdgeDisjointSTPaths paths)
    (C : Finset (Sym2 V)) (hC : IsSTEdgeCut G s t C) :
    l ≤ C.card := by
  have key : ∀ i : Fin l, ∃ e : ↥C, (e : Sym2 V) ∈ (paths i).val.edges := by
    intro i
    obtain ⟨e, heC, hepath⟩ := path_meets_cut (paths i) C hC
    exact ⟨⟨e, heC⟩, hepath⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hne' : i ≠ j := hne
    have hmem : ((f j : ↥C) : Sym2 V) ∈ (paths i).val.edges := hij ▸ hf i
    exact (hdisj i j hne' _ hmem) (hf j)
  have hle := Fintype.card_le_of_injective f hinj
  rwa [Fintype.card_fin, Fintype.card_coe] at hle

/-- The full edge set is an `s-t` edge cut when `s ≠ t`. -/
private theorem univ_edge_cut {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s t : V} (hst : s ≠ t) :
    ∃ C : Finset (Sym2 V), IsSTEdgeCut G s t C := by
  classical
  refine ⟨Finset.univ.filter (fun e => e ∈ G.edgeSet), ?_, ?_⟩
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    exact he.2
  · have hset : ((Finset.univ.filter (fun e => e ∈ G.edgeSet)) : Set (Sym2 V))
        = G.edgeSet := by
      ext e
      simp
    have hbot : G.deleteEdges (↑(Finset.univ.filter (fun e => e ∈ G.edgeSet)) :
        Set (Sym2 V)) = ⊥ := by
      rw [hset]
      exact SimpleGraph.deleteEdges_eq_bot.mpr fun _ h => h
    rw [hbot, SimpleGraph.reachable_bot]
    exact hst

/-- There exists an `s-t` edge cut of minimum size. -/
private theorem exists_min_cut {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s t : V} (hst : s ≠ t) :
    ∃ k : ℕ, ∃ C : Finset (Sym2 V),
      IsSTEdgeCut G s t C ∧ C.card = k ∧
      (∀ C' : Finset (Sym2 V), IsSTEdgeCut G s t C' → k ≤ C'.card) := by
  classical
  obtain ⟨C₀, hC₀⟩ := univ_edge_cut (G := G) (s := s) (t := t) hst
  have hP : ∃ n : ℕ, ∃ C : Finset (Sym2 V), IsSTEdgeCut G s t C ∧ C.card = n :=
    ⟨C₀.card, C₀, hC₀, rfl⟩
  obtain ⟨C, hCcut, hCcard⟩ := Nat.find_spec hP
  exact ⟨Nat.find hP, C, hCcut, hCcard,
    fun C' hC' => Nat.find_min' hP ⟨C', hC', rfl⟩⟩

/-- An `s-t` path with `s ≠ t` uses at least one edge. -/
private theorem path_edges_nonempty {V : Type*} {G : SimpleGraph V} {s t : V}
    (hst : s ≠ t) (p : G.Path s t) : ∃ e, e ∈ p.val.edges := by
  have hnil : ¬ p.val.Nil := SimpleGraph.Walk.not_nil_of_ne hst
  have hne : p.val.edges ≠ [] := by
    rwa [ne_eq, SimpleGraph.Walk.edges_eq_nil]
  match h : p.val.edges with
  | [] => exact absurd h hne
  | e :: _ => exact ⟨e, by simp⟩

/-- Any edge-disjoint family has size at most the number of edges. -/
private theorem card_le_edgeSet_card {V : Type*} {G : SimpleGraph V} [Fintype G.edgeSet]
    {s t : V} (hst : s ≠ t)
    {l : ℕ} (paths : Fin l → G.Path s t) (hdisj : IsEdgeDisjointSTPaths paths) :
    l ≤ Fintype.card G.edgeSet := by
  have key : ∀ i : Fin l, ∃ e : G.edgeSet, (e : Sym2 V) ∈ (paths i).val.edges := by
    intro i
    obtain ⟨e, hepath⟩ := path_edges_nonempty hst (paths i)
    exact ⟨⟨e, (paths i).val.edges_subset_edgeSet hepath⟩, hepath⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hmem : ((f j : G.edgeSet) : Sym2 V) ∈ (paths i).val.edges := hij ▸ hf i
    exact (hdisj i j hne _ hmem) (hf j)
  have hle := Fintype.card_le_of_injective f hinj
  rwa [Fintype.card_fin] at hle

/-- There exists a maximum-size edge-disjoint family. -/
private theorem exists_max_family {V : Type*} [Finite V]
    {G : SimpleGraph V} {s t : V} (hst : s ≠ t) :
    ∃ kmax : ℕ, ∃ paths : Fin kmax → G.Path s t,
      IsEdgeDisjointSTPaths paths ∧
      (∀ {l : ℕ} (paths' : Fin l → G.Path s t),
        IsEdgeDisjointSTPaths paths' → l ≤ kmax) := by
  classical
  let _fintypeV := Fintype.ofFinite V
  let bound := Fintype.card G.edgeSet
  let P : ℕ → Prop := fun l => ∃ paths : Fin l → G.Path s t,
    IsEdgeDisjointSTPaths paths
  have hP0 : P 0 := ⟨fun i => Fin.elim0 i, fun i _ _ _ _ => Fin.elim0 i⟩
  have hbound : ∀ l, P l → l ≤ bound := by
    intro l hl
    obtain ⟨paths, hdisj⟩ := hl
    exact card_le_edgeSet_card hst paths hdisj
  let kmax := Nat.findGreatest P bound
  have hPmax : P kmax :=
    Nat.findGreatest_spec (m := 0) (Nat.zero_le _) hP0
  obtain ⟨paths, hdisj⟩ := hPmax
  refine ⟨kmax, paths, hdisj, ?_⟩
  intro l paths' hdisj'
  have hl : P l := ⟨paths', hdisj'⟩
  by_contra hlt
  have hlt' : kmax < l := by omega
  have hle : l ≤ bound := hbound l hl
  have hneg := Nat.findGreatest_is_greatest (P := P)
    (n := bound) (k := l) hlt' hle
  exact hneg hl

/-- Darts of a path with the same edge are equal (edges are nodup). -/
private theorem dart_eq_of_edge_eq {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath)
    {d₁ d₂ : G.Dart} (h₁ : d₁ ∈ p.darts) (h₂ : d₂ ∈ p.darts)
    (he : d₁.edge = d₂.edge) : d₁ = d₂ := by
  have hedges : p.edges.Nodup := hp.isTrail.edges_nodup
  have hlen : p.edges.length = p.darts.length := by simp [SimpleGraph.Walk.edges]
  obtain ⟨n₁, hn₁, hn₁eq⟩ := List.mem_iff_getElem.mp h₁
  obtain ⟨n₂, hn₂, hn₂eq⟩ := List.mem_iff_getElem.mp h₂
  have hn₁' : n₁ < p.edges.length := by rwa [hlen]
  have hn₂' : n₂ < p.edges.length := by rwa [hlen]
  have e₁ : p.edges[n₁]'hn₁' = d₁.edge := by simp [SimpleGraph.Walk.edges, hn₁eq]
  have e₂ : p.edges[n₂]'hn₂' = d₂.edge := by simp [SimpleGraph.Walk.edges, hn₂eq]
  have hidx : n₁ = n₂ := by
    have hnodup := hedges.getElem_inj_iff (i := n₁) (hi := hn₁') (j := n₂) (hj := hn₂')
    have heq : p.edges[n₁]'hn₁' = p.edges[n₂]'hn₂' := by rw [e₁, e₂, he]
    exact hnodup.mp heq
  subst hidx
  exact hn₁eq.symm.trans hn₂eq

/-- A path never contains opposite darts. -/
private theorem path_no_rev_dart {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath)
    {a b : V} (hab : G.Adj a b)
    {d₁ d₂ : G.Dart} (h₁ : d₁ ∈ p.darts) (h₂ : d₂ ∈ p.darts)
    (e₁ : d₁.toProd = (a, b)) (e₂ : d₂.toProd = (b, a)) : False := by
  have hne : a ≠ b := hab.ne
  have he₁ : d₁.edge = s(a, b) :=
    SimpleGraph.dart_edge_eq_mk'_iff.mpr (Or.inl e₁)
  have he₂ : d₂.edge = s(b, a) :=
    SimpleGraph.dart_edge_eq_mk'_iff.mpr (Or.inl e₂)
  have he : d₁.edge = d₂.edge := by rw [he₁, he₂, Sym2.eq_swap]
  have hdeq := dart_eq_of_edge_eq hp h₁ h₂ he
  have hprod : d₁.toProd = d₂.toProd := congrArg SimpleGraph.Dart.toProd hdeq
  rw [e₁, e₂] at hprod
  have hab_eq : a = b := congrArg Prod.fst hprod
  exact hne hab_eq

/-- Ordered pairs used by a family of paths. -/
private def UsedPairs {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) : Set (V × V) :=
  {p | ∃ i, ∃ d ∈ (paths i).val.darts, d.toProd = p}

/-- Residual relation: `G`-edges whose forward dart is unused. -/
private def ResidualRel {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) : V → V → Prop :=
  fun a b => G.Adj a b ∧ (a, b) ∉ UsedPairs paths

private theorem used_of_mem_darts {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    {paths : Fin k → G.Path s t} {i : Fin k} {d : G.Dart}
    (h : d ∈ (paths i).val.darts) : d.toProd ∈ UsedPairs paths :=
  ⟨i, d, h, rfl⟩

private theorem mem_edges_of_used {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    {paths : Fin k → G.Path s t} {a b : V} (h : (a, b) ∈ UsedPairs paths) :
    ∃ i, s(a, b) ∈ (paths i).val.edges := by
  obtain ⟨i, d, hd, hprod⟩ := h
  have he : d.edge = s(a, b) := by
    have hiff := SimpleGraph.dart_edge_eq_mk'_iff (d := d) (u := a) (v := b)
    have hprodeq : d.toProd = (a, b) := hprod
    exact hiff.mpr (Or.inl hprodeq)
  have hmem : d.edge ∈ (paths i).val.edges := by
    have hmap : (paths i).val.edges = (paths i).val.darts.map SimpleGraph.Dart.edge := rfl
    rw [hmap]
    exact List.mem_map_of_mem hd
  exact ⟨i, he ▸ hmem⟩

private theorem used_no_rev {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    {paths : Fin k → G.Path s t} (hdisj : IsEdgeDisjointSTPaths paths)
    {a b : V} (hab : G.Adj a b) (h : (a, b) ∈ UsedPairs paths) :
    (b, a) ∉ UsedPairs paths := by
  intro hrev
  obtain ⟨i, d₁, hd₁, hp₁⟩ := h
  obtain ⟨j, d₂, hd₂, hp₂⟩ := hrev
  by_cases hij : i = j
  · subst hij
    exact path_no_rev_dart (paths i).property hab hd₁ hd₂ hp₁ hp₂
  · have he₁ : s(a, b) ∈ (paths i).val.edges := by
      have hed : d₁.edge = s(a, b) :=
        SimpleGraph.dart_edge_eq_mk'_iff.mpr (Or.inl hp₁)
      have hmem : d₁.edge ∈ (paths i).val.edges := by
        have hmap : (paths i).val.edges =
            (paths i).val.darts.map SimpleGraph.Dart.edge := rfl
        rw [hmap]
        exact List.mem_map_of_mem hd₁
      rwa [hed] at hmem
    have he₂ : s(a, b) ∈ (paths j).val.edges := by
      have hed : d₂.edge = s(b, a) :=
        SimpleGraph.dart_edge_eq_mk'_iff.mpr (Or.inl hp₂)
      have hmem : d₂.edge ∈ (paths j).val.edges := by
        have hmap : (paths j).val.edges =
            (paths j).val.darts.map SimpleGraph.Dart.edge := rfl
        rw [hmap]
        exact List.mem_map_of_mem hd₂
      have he₂ba : s(b, a) ∈ (paths j).val.edges := by rwa [hed] at hmem
      rwa [Sym2.eq_swap] at he₂ba
    exact hdisj i j hij _ he₁ he₂

private theorem not_residual_of_used {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    {paths : Fin k → G.Path s t} {a b : V} (h : (a, b) ∈ UsedPairs paths) :
    ¬ ResidualRel paths a b := fun ⟨_, hnmem⟩ => hnmem h

private theorem residual_of_unused {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    {paths : Fin k → G.Path s t} {a b : V} (hab : G.Adj a b)
    (h : ∀ i, s(a, b) ∉ (paths i).val.edges) : ResidualRel paths a b := by
  refine ⟨hab, ?_⟩
  intro hused
  obtain ⟨i, he⟩ := mem_edges_of_used hused
  exact h i he

private theorem residual_rev_of_used {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    {paths : Fin k → G.Path s t} (hdisj : IsEdgeDisjointSTPaths paths)
    {i : Fin k} {d : G.Dart} (hd : d ∈ (paths i).val.darts)
    {a b : V} (hprod : d.toProd = (a, b)) : ResidualRel paths b a := by
  obtain ⟨⟨x, y⟩, hadj⟩ := d
  simp only [Prod.mk.injEq] at hprod
  obtain ⟨rfl, rfl⟩ := hprod
  have hused : (x, y) ∈ UsedPairs paths := ⟨i, _, hd, rfl⟩
  have hab : G.Adj x y := hadj
  exact ⟨hab.symm, used_no_rev hdisj hab hused⟩

/-- A walk starting outside `S` with no `T→S` darts stays outside `S`. -/
private theorem walk_support_out_of_no_TS {V : Type*} {G : SimpleGraph V}
    {S : Set V} : ∀ {a b : V} (w : G.Walk a b), a ∉ S →
    (∀ d ∈ w.darts, ¬ (d.fst ∉ S ∧ d.snd ∈ S)) →
    ∀ v ∈ w.support, v ∉ S
  | _, _, SimpleGraph.Walk.nil, ha, _, v, hv => by
    simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rw [hv]
    exact ha
  | _, _, @SimpleGraph.Walk.cons _ _ u v w h rest, ha, hno, x, hx => by
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · have hc : v ∉ S := by
        classical
        by_cases hvmem : v ∈ S
        · exfalso
          have hd0mem : (⟨(u, v), h⟩ : G.Dart) ∈
              (SimpleGraph.Walk.cons h rest).darts := by simp
          exact hno _ hd0mem ⟨ha, hvmem⟩
        · exact hvmem
      have hno_rest : ∀ d ∈ rest.darts, ¬ (d.fst ∉ S ∧ d.snd ∈ S) := by
        intro d hd hts
        have hdmem : d ∈ (SimpleGraph.Walk.cons h rest).darts := by simp [hd]
        exact hno d hdmem hts
      exact walk_support_out_of_no_TS rest hc hno_rest x hx

/-- A walk starting outside `S` with no `T→S` has no `S→T` either. -/
private theorem walk_no_ST_of_start_out {V : Type*} {G : SimpleGraph V}
    {S : Set V} {a b : V} (w : G.Walk a b) (ha : a ∉ S)
    (hnoTS : ∀ d ∈ w.darts, ¬ (d.fst ∉ S ∧ d.snd ∈ S)) :
    ∀ d ∈ w.darts, ¬ (d.fst ∈ S ∧ d.snd ∉ S) := by
  intro d hd hst
  have hfstmem : d.fst ∈ w.support :=
    SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts w hd
  have hfstout : d.fst ∉ S :=
    walk_support_out_of_no_TS w ha hnoTS _ hfstmem
  exact hfstout hst.1

/-- A walk from `S` to outside with no `T→S` has a unique `S→T` dart. -/
private theorem walk_exists_unique_ST {V : Type*} {G : SimpleGraph V}
    {S : Set V} : ∀ {a t : V} (w : G.Walk a t), a ∈ S → t ∉ S →
    (∀ d ∈ w.darts, ¬ (d.fst ∉ S ∧ d.snd ∈ S)) →
    ∃! d, d ∈ w.darts ∧ d.fst ∈ S ∧ d.snd ∉ S
  | _, _, SimpleGraph.Walk.nil, ha, ht, _ => by
    exact False.elim (ht ha)
  | _, _, @SimpleGraph.Walk.cons _ _ u v w h rest, ha, ht, hno => by
    classical
    have hno_rest : ∀ d ∈ rest.darts, ¬ (d.fst ∉ S ∧ d.snd ∈ S) := by
      intro d hd hts
      have hdmem : d ∈ (SimpleGraph.Walk.cons h rest).darts := by simp [hd]
      exact hno d hdmem hts
    by_cases hvmem : v ∈ S
    · obtain ⟨dstar, ⟨hmem, hST1, hST2⟩, huniq⟩ :=
        walk_exists_unique_ST rest hvmem ht hno_rest
      have hmemW : dstar ∈ (SimpleGraph.Walk.cons h rest).darts := by
        simp [hmem]
      refine ⟨dstar, ⟨hmemW, hST1, hST2⟩, ?_⟩
      intro d ⟨hdmem, hdST1, hdST2⟩
      have hdisj : d = (⟨(u, v), h⟩ : G.Dart) ∨ d ∈ rest.darts := by
        have hmem' : d ∈ [⟨(u, v), h⟩] ++ rest.darts := by simpa using hdmem
        simpa using hmem'
      rcases hdisj with rfl | hdmem'
      · have hsnd : (⟨(u, v), h⟩ : G.Dart).snd ∈ S := hvmem
        exact False.elim (hdST2 hsnd)
      · exact huniq d ⟨hdmem', hdST1, hdST2⟩
    · have hd0mem : (⟨(u, v), h⟩ : G.Dart) ∈
          (SimpleGraph.Walk.cons h rest).darts := by simp
      have hd0ST1 : (⟨(u, v), h⟩ : G.Dart).fst ∈ S := ha
      have hd0ST2 : (⟨(u, v), h⟩ : G.Dart).snd ∉ S := hvmem
      have hnoST_rest := walk_no_ST_of_start_out rest hvmem hno_rest
      refine ⟨⟨(u, v), h⟩, ⟨hd0mem, hd0ST1, hd0ST2⟩, ?_⟩
      intro d ⟨hdmem, hdST1, hdST2⟩
      have hdisj : d = (⟨(u, v), h⟩ : G.Dart) ∨ d ∈ rest.darts := by
        have hmem' : d ∈ [⟨(u, v), h⟩] ++ rest.darts := by simpa using hdmem
        simpa using hmem'
      rcases hdisj with rfl | hdmem'
      · rfl
      · exact False.elim (hnoST_rest d hdmem' ⟨hdST1, hdST2⟩)

/-- Any walk from `S` to outside uses an `S→T` dart. -/
private theorem walk_exists_ST_of_mem {V : Type*} {G : SimpleGraph V}
    {S : Set V} : ∀ {a t : V} (w : G.Walk a t), a ∈ S → t ∉ S →
    ∃ d, d ∈ w.darts ∧ d.fst ∈ S ∧ d.snd ∉ S
  | _, _, SimpleGraph.Walk.nil, ha, ht => by
    exact False.elim (ht ha)
  | _, _, @SimpleGraph.Walk.cons _ _ u v w h rest, ha, ht => by
    classical
    by_cases hvmem : v ∈ S
    · obtain ⟨d, hdmem, hdST1, hdST2⟩ :=
        walk_exists_ST_of_mem rest hvmem ht
      have hdmemW : d ∈ (SimpleGraph.Walk.cons h rest).darts := by simp [hdmem]
      exact ⟨d, hdmemW, hdST1, hdST2⟩
    · have hd0mem : (⟨(u, v), h⟩ : G.Dart) ∈
          (SimpleGraph.Walk.cons h rest).darts := by simp
      exact ⟨⟨(u, v), h⟩, hd0mem, ha, hvmem⟩

/-- Vertices reachable from `s` in the residual relation. -/
private def ResidReachableSet {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) : Set V :=
  {v | Relation.ReflTransGen (ResidualRel paths) s v}

private theorem mem_residReachableSet_self {V : Type*} {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t) :
    s ∈ ResidReachableSet paths :=
  Relation.ReflTransGen.refl

private theorem not_mem_residReachableSet_of_not_reachable {V : Type*}
    {G : SimpleGraph V} {s t : V} {k : ℕ} (paths : Fin k → G.Path s t)
    (hnot : ¬ Relation.ReflTransGen (ResidualRel paths) s t) :
    t ∉ ResidReachableSet paths :=
  hnot

private theorem no_residual_cross {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) {a b : V}
    (ha : a ∈ ResidReachableSet paths) (hb : b ∉ ResidReachableSet paths) :
    ¬ ResidualRel paths a b := by
  intro hres
  exact hb (ha.tail hres)

private theorem crossing_edge_used {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) {a b : V} (hab : G.Adj a b)
    (hcross : (a ∈ ResidReachableSet paths ∧ b ∉ ResidReachableSet paths) ∨
      (a ∉ ResidReachableSet paths ∧ b ∈ ResidReachableSet paths)) :
    ∃ i, s(a, b) ∈ (paths i).val.edges := by
  by_contra hnone
  have hunused : ∀ i, s(a, b) ∉ (paths i).val.edges := fun i hi => hnone ⟨i, hi⟩
  rcases hcross with ⟨haS, hbS⟩ | ⟨haS, hbS⟩
  · have hres := residual_of_unused hab hunused
    exact no_residual_cross paths haS hbS hres
  · have hunused' : ∀ i, s(b, a) ∉ (paths i).val.edges := by
      intro i hi
      have hi' : s(a, b) ∈ (paths i).val.edges := by
        rwa [Sym2.eq_swap] at hi
      exact hunused i hi'
    have hres := residual_of_unused hab.symm hunused'
    exact no_residual_cross paths hbS haS hres

private theorem no_TS_in_paths {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    {paths : Fin k → G.Path s t} (hdisj : IsEdgeDisjointSTPaths paths)
    (i : Fin k) : ∀ d ∈ (paths i).val.darts,
    ¬ (d.fst ∉ ResidReachableSet paths ∧ d.snd ∈ ResidReachableSet paths) := by
  intro d hd hts
  obtain ⟨hTS1, hTS2⟩ := hts
  have hprod : d.toProd = (d.fst, d.snd) := rfl
  have hres := residual_rev_of_used hdisj hd hprod
  exact no_residual_cross paths hTS2 hTS1 hres

private theorem unique_ST_dart_of_path {V : Type*} {G : SimpleGraph V} {s t : V}
    {k : ℕ} {paths : Fin k → G.Path s t} (hdisj : IsEdgeDisjointSTPaths paths)
    (hnot : ¬ Relation.ReflTransGen (ResidualRel paths) s t) (i : Fin k) :
    ∃! d, d ∈ (paths i).val.darts ∧ d.fst ∈ ResidReachableSet paths ∧
      d.snd ∉ ResidReachableSet paths :=
  walk_exists_unique_ST (paths i).val (mem_residReachableSet_self paths)
    (not_mem_residReachableSet_of_not_reachable paths hnot)
    (no_TS_in_paths hdisj i)

/-- An edge crosses the residual cut when it joins `S` to its complement. -/
private def IsCrossing {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) (e : Sym2 V) : Prop :=
  ∃ a b, e = s(a, b) ∧
    ((a ∈ ResidReachableSet paths ∧ b ∉ ResidReachableSet paths) ∨
      (a ∉ ResidReachableSet paths ∧ b ∈ ResidReachableSet paths))

/-- Each path uses a unique crossing edge. -/
private theorem unique_crossing_edge_of_path {V : Type*} {G : SimpleGraph V}
    {s t : V} {k : ℕ} {paths : Fin k → G.Path s t}
    (hdisj : IsEdgeDisjointSTPaths paths)
    (hnot : ¬ Relation.ReflTransGen (ResidualRel paths) s t) (i : Fin k) :
    ∃ estar, estar ∈ (paths i).val.edges ∧ IsCrossing paths estar ∧
      ∀ e ∈ (paths i).val.edges, IsCrossing paths e → e = estar := by
  obtain ⟨dstar, ⟨hmemStar, hST1Star, hST2Star⟩, huniqStar⟩ :=
    unique_ST_dart_of_path hdisj hnot i
  have hnoTS := no_TS_in_paths hdisj i
  let estar : Sym2 V := dstar.edge
  have hmemStarE : estar ∈ (paths i).val.edges := by
    have hmap : (paths i).val.edges =
        (paths i).val.darts.map SimpleGraph.Dart.edge := rfl
    rw [hmap]
    exact List.mem_map_of_mem hmemStar
  have hcrossStar : IsCrossing paths estar := by
    refine ⟨dstar.fst, dstar.snd, rfl, Or.inl ⟨hST1Star, hST2Star⟩⟩
  refine ⟨estar, hmemStarE, hcrossStar, ?_⟩
  intro e heMem heCross
  obtain ⟨a, b, heq, hcross⟩ := heCross
  have hmap : (paths i).val.edges =
      (paths i).val.darts.map SimpleGraph.Dart.edge := rfl
  have heMemMap : e ∈ (paths i).val.darts.map SimpleGraph.Dart.edge := by
    rwa [← hmap]
  obtain ⟨d, hdmem, hed⟩ := List.mem_map.mp heMemMap
  have hedge : d.edge = s(a, b) := by rw [hed, heq]
  have hprodCases := SimpleGraph.dart_edge_eq_mk'_iff.mp hedge
  rcases hcross with ⟨haS, hbS⟩ | ⟨haS, hbS⟩
  · rcases hprodCases with hprod | hprod
    · have hfst : d.fst = a := congrArg Prod.fst hprod
      have hsnd : d.snd = b := congrArg Prod.snd hprod
      have hST1 : d.fst ∈ ResidReachableSet paths := by rwa [hfst]
      have hST2 : d.snd ∉ ResidReachableSet paths := by rwa [hsnd]
      have hdeq := huniqStar d ⟨hdmem, hST1, hST2⟩
      have hedeq : d.edge = estar := congrArg SimpleGraph.Dart.edge hdeq
      rwa [hed] at hedeq
    · have hfst : d.fst = b := congrArg Prod.fst hprod
      have hsnd : d.snd = a := congrArg Prod.snd hprod
      have hTS1 : d.fst ∉ ResidReachableSet paths := by rwa [hfst]
      have hTS2 : d.snd ∈ ResidReachableSet paths := by rwa [hsnd]
      exact False.elim (hnoTS d hdmem ⟨hTS1, hTS2⟩)
  · rcases hprodCases with hprod | hprod
    · have hfst : d.fst = a := congrArg Prod.fst hprod
      have hsnd : d.snd = b := congrArg Prod.snd hprod
      have hTS1 : d.fst ∉ ResidReachableSet paths := by rwa [hfst]
      have hTS2 : d.snd ∈ ResidReachableSet paths := by rwa [hsnd]
      exact False.elim (hnoTS d hdmem ⟨hTS1, hTS2⟩)
    · have hfst : d.fst = b := congrArg Prod.fst hprod
      have hsnd : d.snd = a := congrArg Prod.snd hprod
      have hST1 : d.fst ∈ ResidReachableSet paths := by rwa [hfst]
      have hST2 : d.snd ∉ ResidReachableSet paths := by rwa [hsnd]
      have hdeq := huniqStar d ⟨hdmem, hST1, hST2⟩
      have hedeq : d.edge = estar := congrArg SimpleGraph.Dart.edge hdeq
      rwa [hed] at hedeq

private theorem exists_cut_of_not_reachable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) (hdisj : IsEdgeDisjointSTPaths paths)
    (hnot : ¬ Relation.ReflTransGen (ResidualRel paths) s t) :
    ∃ C : Finset (Sym2 V), IsSTEdgeCut G s t C ∧ C.card = k := by
  classical
  have hsS : s ∈ ResidReachableSet paths := mem_residReachableSet_self paths
  have htS : t ∉ ResidReachableSet paths :=
    not_mem_residReachableSet_of_not_reachable paths hnot
  let C : Finset (Sym2 V) :=
    Finset.univ.filter (fun e => e ∈ G.edgeSet ∧ IsCrossing paths e)
  have hCmem : ∀ e : Sym2 V, e ∈ C ↔ e ∈ G.edgeSet ∧ IsCrossing paths e := by
    intro e
    simp [C]
  have hcut : IsSTEdgeCut G s t C := by
    constructor
    · intro e he
      rw [Finset.mem_coe] at he
      rw [hCmem] at he
      exact he.1
    · intro hreach
      obtain ⟨w⟩ := hreach
      have hle : G.deleteEdges (↑C : Set (Sym2 V)) ≤ G :=
        SimpleGraph.deleteEdges_le _
      let wG : G.Walk s t := w.mapLe hle
      have hedgeEq : wG.edges = w.edges :=
        SimpleGraph.Walk.edges_mapLe_eq_edges _ _
      obtain ⟨d, hdmem, hdST1, hdST2⟩ := walk_exists_ST_of_mem wG hsS htS
      have heMemG : d.edge ∈ wG.edges := by
        have hmap : wG.edges = wG.darts.map SimpleGraph.Dart.edge := rfl
        rw [hmap]
        exact List.mem_map_of_mem hdmem
      have heSet : d.edge ∈ G.edgeSet := wG.edges_subset_edgeSet heMemG
      have heCross : IsCrossing paths d.edge := ⟨d.fst, d.snd, rfl, Or.inl ⟨hdST1, hdST2⟩⟩
      have heC : d.edge ∈ C := by
        rw [hCmem]
        exact ⟨heSet, heCross⟩
      have heW : d.edge ∈ w.edges := by rwa [hedgeEq] at heMemG
      have heSetDel : d.edge ∈ (G.deleteEdges (↑C : Set (Sym2 V))).edgeSet :=
        w.edges_subset_edgeSet heW
      rw [SimpleGraph.edgeSet_deleteEdges] at heSetDel
      have heNotC : d.edge ∉ C := by
        intro hcon
        have hcoe : d.edge ∈ (↑C : Set (Sym2 V)) :=
          Finset.mem_coe.mpr hcon
        exact heSetDel.2 hcoe
      exact heNotC heC
  have hcard : C.card = k := by
    have hle1 : k ≤ C.card := weak_duality_aux paths hdisj C hcut
    have hle2 : C.card ≤ k := by
      have hused : ∀ e ∈ C, ∃ i, e ∈ (paths i).val.edges := by
        intro e heC
        rw [hCmem] at heC
        obtain ⟨heSet, a, b, heq, hcross⟩ := heC
        have hab : G.Adj a b := by
          have hs : s(a, b) ∈ G.edgeSet := by rwa [heq] at heSet
          exact hs
        obtain ⟨i, hi⟩ := crossing_edge_used paths hab hcross
        exact ⟨i, by rwa [heq]⟩
      choose f hf using fun e : ↥C => hused e.val e.property
      have hinj : Function.Injective f := by
        intro e1 e2 hij
        obtain ⟨estar, _, _, huniq⟩ :=
          unique_crossing_edge_of_path hdisj hnot (f e1)
        have he1mem : (e1 : Sym2 V) ∈ (paths (f e1)).val.edges := hf e1
        have he2mem : (e2 : Sym2 V) ∈ (paths (f e1)).val.edges := by
          have h2 : (e2 : Sym2 V) ∈ (paths (f e2)).val.edges := hf e2
          rwa [← hij] at h2
        have he1C : (e1 : Sym2 V) ∈ C := e1.property
        have he2C : (e2 : Sym2 V) ∈ C := e2.property
        rw [hCmem] at he1C he2C
        have he1eq := huniq _ he1mem he1C.2
        have he2eq := huniq _ he2mem he2C.2
        have hvaleq : (e1 : Sym2 V) = (e2 : Sym2 V) := by
          rw [he1eq, he2eq]
        exact Subtype.ext hvaleq
      have hle := Fintype.card_le_of_injective f hinj
      rwa [Fintype.card_coe, Fintype.card_fin] at hle
    exact Nat.le_antisymm hle2 hle1
  exact ⟨C, hcut, hcard⟩

/-- Outgoing dart count of `v` in `D`. -/
private def outCount {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (D : Finset G.Dart) (v : V) : ℕ :=
  (D.filter (fun d => d.fst = v)).card

/-- Incoming dart count of `v` in `D`. -/
private def inCount {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (D : Finset G.Dart) (v : V) : ℕ :=
  (D.filter (fun d => d.snd = v)).card

/-- Darts of a path satisfy flow conservation (out - in is 1 at start, -1 at end). -/
private theorem path_balances {V : Type*} [DecidableEq V] {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), p.IsPath → ∀ x : V,
    outCount p.darts.toFinset x + (if x = v then 1 else 0) =
      inCount p.darts.toFinset x + (if x = u then 1 else 0)
  | _, _, SimpleGraph.Walk.nil, _, x => by
    simp [outCount, inCount]
  | _, _, @SimpleGraph.Walk.cons _ _ u v w h rest, hp, x => by
    have hpRest : rest.IsPath := hp.of_cons
    have ih := path_balances rest hpRest x
    have hdartsNodup : (SimpleGraph.Walk.cons h rest).darts.Nodup :=
      SimpleGraph.Walk.darts_nodup_of_support_nodup hp.support_nodup
    have hd0NotMem : (⟨(u, v), h⟩ : G.Dart) ∉ rest.darts := by
      have hcons : (SimpleGraph.Walk.cons h rest).darts =
          (⟨(u, v), h⟩ : G.Dart) :: rest.darts := rfl
      rw [hcons] at hdartsNodup
      exact (List.nodup_cons.mp hdartsNodup).1
    have hd0NotMemFin : (⟨(u, v), h⟩ : G.Dart) ∉ rest.darts.toFinset := by
      rw [List.mem_toFinset]
      exact hd0NotMem
    have htoFinsetEq : (SimpleGraph.Walk.cons h rest).darts.toFinset =
        insert (⟨(u, v), h⟩ : G.Dart) rest.darts.toFinset := by
      have hcons : (SimpleGraph.Walk.cons h rest).darts =
          (⟨(u, v), h⟩ : G.Dart) :: rest.darts := rfl
      rw [hcons, List.toFinset_cons]
    have houtEq : outCount (SimpleGraph.Walk.cons h rest).darts.toFinset x =
        outCount rest.darts.toFinset x + (if x = u then 1 else 0) := by
      rw [htoFinsetEq]
      simp only [outCount]
      rw [Finset.filter_insert]
      by_cases hx : ((⟨(u, v), h⟩ : G.Dart).fst = x)
      · have hxu : x = u := by
          have : (⟨(u, v), h⟩ : G.Dart).fst = u := rfl
          rw [this] at hx
          exact hx.symm
        rw [ite_eq_left hx]
        rw [ite_eq_left hxu]
        have hnotmem : (⟨(u, v), h⟩ : G.Dart) ∉
            rest.darts.toFinset.filter (fun d => d.fst = x) := by
          intro hcon
          have hmem : (⟨(u, v), h⟩ : G.Dart) ∈ rest.darts.toFinset :=
            Finset.mem_of_mem_filter _ hcon
          exact hd0NotMemFin hmem
        rw [Finset.card_insert_of_notMem hnotmem]
      · have hxu : ¬ x = u := by
          intro hcon
          have : (⟨(u, v), h⟩ : G.Dart).fst = u := rfl
          apply hx
          rw [this, hcon]
        rw [ite_eq_right hx]
        rw [ite_eq_right hxu]
        simp
    have hinEq : inCount (SimpleGraph.Walk.cons h rest).darts.toFinset x =
        inCount rest.darts.toFinset x + (if x = v then 1 else 0) := by
      rw [htoFinsetEq]
      simp only [inCount]
      rw [Finset.filter_insert]
      by_cases hx : ((⟨(u, v), h⟩ : G.Dart).snd = x)
      · have hxv : x = v := by
          have : (⟨(u, v), h⟩ : G.Dart).snd = v := rfl
          rw [this] at hx
          exact hx.symm
        rw [ite_eq_left hx]
        rw [ite_eq_left hxv]
        have hnotmem : (⟨(u, v), h⟩ : G.Dart) ∉
            rest.darts.toFinset.filter (fun d => d.snd = x) := by
          intro hcon
          have hmem : (⟨(u, v), h⟩ : G.Dart) ∈ rest.darts.toFinset :=
            Finset.mem_of_mem_filter _ hcon
          exact hd0NotMemFin hmem
        rw [Finset.card_insert_of_notMem hnotmem]
      · have hxv : ¬ x = v := by
          intro hcon
          have : (⟨(u, v), h⟩ : G.Dart).snd = v := rfl
          apply hx
          rw [this, hcon]
        rw [ite_eq_right hx]
        rw [ite_eq_right hxv]
        simp
    rw [houtEq, hinEq]
    omega

/-- A residual-reachable vertex yields a residual walk (all darts unused forward). -/
private theorem walk_of_resid_reachable {V : Type*} {G : SimpleGraph V} {s t : V}
    {k : ℕ} {paths : Fin k → G.Path s t} {u : V}
    (h : Relation.ReflTransGen (ResidualRel paths) s u) :
    ∃ w : G.Walk s u, ∀ d ∈ w.darts, d.toProd ∉ UsedPairs paths := by
  induction h with
  | refl =>
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | @tail b _ _ hres ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨hab, hunused⟩ := hres
    refine ⟨w.append hab.toWalk, ?_⟩
    intro d hd
    rw [SimpleGraph.Walk.darts_append, SimpleGraph.Adj.darts_toWalk] at hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hdOld | rfl
    · exact hw d hdOld
    · simpa using hunused

/-- A residual-reachable `t` yields a residual `s-t` path. -/
private theorem path_of_resid_reachable {V : Type*} {G : SimpleGraph V} {s t : V}
    {k : ℕ} {paths : Fin k → G.Path s t}
    (h : Relation.ReflTransGen (ResidualRel paths) s t) :
    ∃ q : G.Path s t, ∀ d ∈ q.val.darts, d.toProd ∉ UsedPairs paths := by
  classical
  obtain ⟨w, hw⟩ := walk_of_resid_reachable h
  refine ⟨w.toPath, ?_⟩
  intro d hd
  have hdW : d ∈ w.darts :=
    SimpleGraph.Walk.darts_toPath_subset_darts w hd
  exact hw d hdW

/-- Darts of distinct edge-disjoint paths are disjoint. -/
private theorem paths_darts_disjoint {V : Type*} {G : SimpleGraph V} {s t : V}
    {k : ℕ} {paths : Fin k → G.Path s t} (hdisj : IsEdgeDisjointSTPaths paths)
    {i j : Fin k} (hij : i ≠ j) : ∀ d ∈ (paths i).val.darts, d ∉ (paths j).val.darts := by
  intro d hdI hdJ
  have heI : d.edge ∈ (paths i).val.edges := by
    have hmap : (paths i).val.edges =
        (paths i).val.darts.map SimpleGraph.Dart.edge := rfl
    rw [hmap]
    exact List.mem_map_of_mem hdI
  have heJ : d.edge ∈ (paths j).val.edges := by
    have hmap : (paths j).val.edges =
        (paths j).val.darts.map SimpleGraph.Dart.edge := rfl
    rw [hmap]
    exact List.mem_map_of_mem hdJ
  exact hdisj i j hij _ heI heJ

/-- Residual path darts are disjoint from used darts. -/
private theorem resid_darts_disjoint {V : Type*} {G : SimpleGraph V} {s t : V}
    {k : ℕ} {paths : Fin k → G.Path s t} {q : G.Path s t}
    (hq : ∀ d ∈ q.val.darts, d.toProd ∉ UsedPairs paths)
    (i : Fin k) : ∀ d ∈ q.val.darts, d ∉ (paths i).val.darts := by
  intro d hdQ hdP
  have hused : d.toProd ∈ UsedPairs paths := ⟨i, d, hdP, rfl⟩
  exact hq d hdQ hused

/-- Combined dart counts of `k` paths plus a residual path satisfy `k+1` balances. -/
private theorem D0_balances {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t)
    (hdisj : IsEdgeDisjointSTPaths paths) (q : G.Path s t)
    (hq : ∀ d ∈ q.val.darts, d.toProd ∉ UsedPairs paths) (x : V) :
    outCount ((Finset.univ.biUnion (fun i => (paths i).val.darts.toFinset)) ∪
      q.val.darts.toFinset) x + (if x = t then k + 1 else 0) =
      inCount ((Finset.univ.biUnion (fun i => (paths i).val.darts.toFinset)) ∪
      q.val.darts.toFinset) x + (if x = s then k + 1 else 0) := by
  have hPiDisj : ∀ i j : Fin k, i ≠ j →
      Disjoint (paths i).val.darts.toFinset (paths j).val.darts.toFinset := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro d hdI hdJ
    rw [List.mem_toFinset] at hdI hdJ
    exact paths_darts_disjoint hdisj hij d hdI hdJ
  have hQDisj : ∀ i : Fin k,
      Disjoint q.val.darts.toFinset (paths i).val.darts.toFinset := by
    intro i
    rw [Finset.disjoint_left]
    intro d hdQ hdP
    rw [List.mem_toFinset] at hdQ hdP
    exact resid_darts_disjoint hq i d hdQ hdP
  have hPairwise : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin k)) : Set (Fin k))
      (fun i => (paths i).val.darts.toFinset) := by
    intro i _ j _ hij
    exact hPiDisj i j hij
  have hQDisjUnion : Disjoint
      (Finset.univ.biUnion (fun i => (paths i).val.darts.toFinset))
      q.val.darts.toFinset := by
    rw [Finset.disjoint_biUnion_left]
    intro i _
    exact (hQDisj i).symm
  have hPairwiseFiltOut : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin k)) : Set (Fin k))
      (fun i => ((paths i).val.darts.toFinset).filter (fun d => d.fst = x)) := by
    intro i _ j _ hij
    exact Finset.disjoint_filter_filter (hPiDisj i j hij)
  have houtBiUnion : outCount
      (Finset.univ.biUnion (fun i => (paths i).val.darts.toFinset)) x =
      ∑ i : Fin k, outCount (paths i).val.darts.toFinset x := by
    simp only [outCount, Finset.filter_biUnion]
    rw [Finset.card_biUnion hPairwiseFiltOut]
  have hPairwiseFiltIn : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin k)) : Set (Fin k))
      (fun i => ((paths i).val.darts.toFinset).filter (fun d => d.snd = x)) := by
    intro i _ j _ hij
    exact Finset.disjoint_filter_filter (hPiDisj i j hij)
  have hinBiUnion : inCount
      (Finset.univ.biUnion (fun i => (paths i).val.darts.toFinset)) x =
      ∑ i : Fin k, inCount (paths i).val.darts.toFinset x := by
    simp only [inCount, Finset.filter_biUnion]
    rw [Finset.card_biUnion hPairwiseFiltIn]
  have houtUnion : ∀ (A B : Finset G.Dart), Disjoint A B →
      outCount (A ∪ B) x = outCount A x + outCount B x := by
    intro A B hDisj
    simp only [outCount, Finset.filter_union]
    rw [Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hDisj)]
  have hinUnion : ∀ (A B : Finset G.Dart), Disjoint A B →
      inCount (A ∪ B) x = inCount A x + inCount B x := by
    intro A B hDisj
    simp only [inCount, Finset.filter_union]
    rw [Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hDisj)]
  have houtD0 : outCount
      ((Finset.univ.biUnion (fun i => (paths i).val.darts.toFinset)) ∪
        q.val.darts.toFinset) x =
      (∑ i : Fin k, outCount (paths i).val.darts.toFinset x) +
        outCount q.val.darts.toFinset x := by
    rw [houtUnion _ _ hQDisjUnion, houtBiUnion]
  have hinD0 : inCount
      ((Finset.univ.biUnion (fun i => (paths i).val.darts.toFinset)) ∪
        q.val.darts.toFinset) x =
      (∑ i : Fin k, inCount (paths i).val.darts.toFinset x) +
        inCount q.val.darts.toFinset x := by
    rw [hinUnion _ _ hQDisjUnion, hinBiUnion]
  have hPiBal : ∀ i : Fin k, outCount (paths i).val.darts.toFinset x +
      (if x = t then 1 else 0) =
      inCount (paths i).val.darts.toFinset x + (if x = s then 1 else 0) :=
    fun i => path_balances (paths i).val (paths i).property x
  have hQBal : outCount q.val.darts.toFinset x + (if x = t then 1 else 0) =
      inCount q.val.darts.toFinset x + (if x = s then 1 else 0) :=
    path_balances q.val q.property x
  have hsumPi : (∑ i : Fin k, outCount (paths i).val.darts.toFinset x) +
      (∑ _i : Fin k, (if x = t then 1 else 0)) =
      (∑ i : Fin k, inCount (paths i).val.darts.toFinset x) +
      (∑ _i : Fin k, (if x = s then 1 else 0)) := by
    have hcongr : (∑ i : Fin k, (outCount (paths i).val.darts.toFinset x +
        (if x = t then 1 else 0))) =
        ∑ i : Fin k, (inCount (paths i).val.darts.toFinset x +
        (if x = s then 1 else 0)) :=
      Finset.sum_congr rfl (fun i _ => hPiBal i)
    rwa [Finset.sum_add_distrib, Finset.sum_add_distrib] at hcongr
  have hsumT : (∑ _i : Fin k, (if x = t then 1 else 0)) =
      (if x = t then k else 0) := by
    by_cases ht : x = t
    · simp [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    · simp [ht]
  have hsumS : (∑ _i : Fin k, (if x = s then 1 else 0)) =
      (if x = s then k else 0) := by
    by_cases hs : x = s
    · simp [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    · simp [hs]
  rw [houtD0, hinD0]
  rw [hsumT, hsumS] at hsumPi
  have hk1T : (if x = t then k + 1 else 0) =
      (if x = t then k else 0) + (if x = t then 1 else 0) := by
    by_cases ht : x = t <;> simp [ht]
  have hk1S : (if x = s then k + 1 else 0) =
      (if x = s then k else 0) + (if x = s then 1 else 0) := by
    by_cases hs : x = s <;> simp [hs]
  rw [hk1T, hk1S]
  omega

private theorem fst_symm {V : Type*} {G : SimpleGraph V} (d : G.Dart) :
    d.symm.fst = d.snd := by
  obtain ⟨⟨a, b⟩, h⟩ := d
  rfl

private theorem snd_symm {V : Type*} {G : SimpleGraph V} (d : G.Dart) :
    d.symm.snd = d.fst := by
  obtain ⟨⟨a, b⟩, h⟩ := d
  rfl

/-- Cancelled darts (those with opposite present) are balanced everywhere. -/
private theorem cancel_balanced {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (D0 : Finset G.Dart) (x : V) :
    outCount (D0.filter (fun d => d.symm ∈ D0)) x =
      inCount (D0.filter (fun d => d.symm ∈ D0)) x := by
  have hsymm : ∀ d : G.Dart, d ∈ D0.filter (fun d => d.symm ∈ D0) →
      d.symm ∈ D0.filter (fun d => d.symm ∈ D0) := by
    intro d hd
    rw [Finset.mem_filter] at hd ⊢
    obtain ⟨hd0, hsymm0⟩ := hd
    refine ⟨hsymm0, ?_⟩
    rw [SimpleGraph.Dart.symm_symm]
    exact hd0
  simp only [outCount, inCount]
  apply Finset.card_bij (fun d _ => d.symm)
  · intro d hd
    rw [Finset.mem_filter] at hd ⊢
    obtain ⟨hdC, hfst⟩ := hd
    have hsymmC := hsymm d hdC
    refine ⟨hsymmC, ?_⟩
    rw [snd_symm]
    exact hfst
  · intro a _ b _ hab
    have hsymmEq : a.symm.symm = b.symm.symm := congrArg _ hab
    rwa [SimpleGraph.Dart.symm_symm, SimpleGraph.Dart.symm_symm] at hsymmEq
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbC, hsnd⟩ := hb
    have hsymmC := hsymm b hbC
    refine ⟨b.symm, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨hsymmC, ?_⟩
      rw [fst_symm]
      exact hsnd
    · exact SimpleGraph.Dart.symm_symm b

/-- All darts of `paths` plus `q`. -/
private def D0Finset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t) (q : G.Path s t) :
    Finset G.Dart :=
  (Finset.univ.biUnion (fun i => (paths i).val.darts.toFinset)) ∪
    q.val.darts.toFinset

/-- Darts of `D0` with opposite present (to cancel). -/
private def CancelFinset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t) (q : G.Path s t) :
    Finset G.Dart :=
  (D0Finset paths q).filter (fun d => d.symm ∈ D0Finset paths q)

/-- Remaining darts after cancelling opposite pairs. -/
private def DFinset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t) (q : G.Path s t) :
    Finset G.Dart :=
  (D0Finset paths q) \ (CancelFinset paths q)

/-- Flow balance: `D` carries `n` units of flow from `s` to `t`. -/
private def Balances {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (s t : V) (D : Finset G.Dart) (n : ℕ) : Prop :=
  ∀ x : V, outCount D x + (if x = t then n else 0) =
    inCount D x + (if x = s then n else 0)

/-- Out-counts add over disjoint dart sets. -/
private theorem outCount_union {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset G.Dart} (h : Disjoint A B) (x : V) :
    outCount (A ∪ B) x = outCount A x + outCount B x := by
  simp only [outCount, Finset.filter_union]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

/-- In-counts add over disjoint dart sets. -/
private theorem inCount_union {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset G.Dart} (h : Disjoint A B) (x : V) :
    inCount (A ∪ B) x = inCount A x + inCount B x := by
  simp only [inCount, Finset.filter_union]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

/-- Every edge of a walk comes from one of its darts. -/
private theorem edge_mem_dart {V : Type*} {G : SimpleGraph V} {u v : V}
    {w : G.Walk u v} {e : Sym2 V} (h : e ∈ w.edges) :
    ∃ d ∈ w.darts, d.edge = e := by
  have hmap : w.edges = w.darts.map SimpleGraph.Dart.edge := rfl
  rw [hmap] at h
  obtain ⟨d, hd, hed⟩ := List.mem_map.mp h
  exact ⟨d, hd, hed⟩

/-- Summing out-counts over `S` counts darts starting in `S`. -/
private theorem sum_outCount_eq_card_filter {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (D : Finset G.Dart) (S : Finset V) :
    ∑ x ∈ S, outCount D x = (D.filter (fun d => d.fst ∈ S)).card := by
  have hcard : ∀ x : V, outCount D x =
      ∑ d ∈ D, (if d.fst = x then 1 else 0) := by
    intro x
    change (D.filter (fun d => d.fst = x)).card = _
    exact Finset.card_filter _ _
  have hR : (D.filter (fun d => d.fst ∈ S)).card =
      ∑ d ∈ D, (if d.fst ∈ S then 1 else 0) :=
    Finset.card_filter _ _
  calc ∑ x ∈ S, outCount D x
      = ∑ x ∈ S, ∑ d ∈ D, (if d.fst = x then 1 else 0) := by
        simp only [hcard]
    _ = ∑ d ∈ D, ∑ x ∈ S, (if d.fst = x then 1 else 0) := Finset.sum_comm
    _ = ∑ d ∈ D, (if d.fst ∈ S then 1 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro d _
        exact Finset.sum_ite_eq S d.fst (fun _ => 1)
    _ = (D.filter (fun d => d.fst ∈ S)).card := hR.symm

/-- Summing in-counts over `S` counts darts ending in `S`. -/
private theorem sum_inCount_eq_card_filter {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (D : Finset G.Dart) (S : Finset V) :
    ∑ x ∈ S, inCount D x = (D.filter (fun d => d.snd ∈ S)).card := by
  have hcard : ∀ x : V, inCount D x =
      ∑ d ∈ D, (if d.snd = x then 1 else 0) := by
    intro x
    change (D.filter (fun d => d.snd = x)).card = _
    exact Finset.card_filter _ _
  have hR : (D.filter (fun d => d.snd ∈ S)).card =
      ∑ d ∈ D, (if d.snd ∈ S then 1 else 0) :=
    Finset.card_filter _ _
  calc ∑ x ∈ S, inCount D x
      = ∑ x ∈ S, ∑ d ∈ D, (if d.snd = x then 1 else 0) := by
        simp only [hcard]
    _ = ∑ d ∈ D, ∑ x ∈ S, (if d.snd = x then 1 else 0) := Finset.sum_comm
    _ = ∑ d ∈ D, (if d.snd ∈ S then 1 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro d _
        exact Finset.sum_ite_eq S d.snd (fun _ => 1)
    _ = (D.filter (fun d => d.snd ∈ S)).card := hR.symm

/-- Darts starting in `S` split into internal and outgoing ones. -/
private theorem card_filter_fst_partition {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (D : Finset G.Dart) (S : Finset V) :
    (D.filter (fun d => d.fst ∈ S)).card =
      (D.filter (fun d => d.fst ∈ S ∧ d.snd ∈ S)).card +
      (D.filter (fun d => d.fst ∈ S ∧ d.snd ∉ S)).card := by
  have hunion : D.filter (fun d => d.fst ∈ S) =
      D.filter (fun d => d.fst ∈ S ∧ d.snd ∈ S) ∪
      D.filter (fun d => d.fst ∈ S ∧ d.snd ∉ S) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hd, hf⟩
      by_cases hsnd : d.snd ∈ S
      · exact Or.inl ⟨hd, hf, hsnd⟩
      · exact Or.inr ⟨hd, hf, hsnd⟩
    · rintro (⟨hd, hf, -⟩ | ⟨hd, hf, -⟩) <;> exact ⟨hd, hf⟩
  have hdisj : Disjoint (D.filter (fun d => d.fst ∈ S ∧ d.snd ∈ S))
      (D.filter (fun d => d.fst ∈ S ∧ d.snd ∉ S)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [Finset.mem_filter] at hd1 hd2
    exact hd2.2.2 hd1.2.2
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-- Darts ending in `S` split into internal and incoming ones. -/
private theorem card_filter_snd_partition {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (D : Finset G.Dart) (S : Finset V) :
    (D.filter (fun d => d.snd ∈ S)).card =
      (D.filter (fun d => d.fst ∈ S ∧ d.snd ∈ S)).card +
      (D.filter (fun d => d.fst ∉ S ∧ d.snd ∈ S)).card := by
  have hunion : D.filter (fun d => d.snd ∈ S) =
      D.filter (fun d => d.fst ∈ S ∧ d.snd ∈ S) ∪
      D.filter (fun d => d.fst ∉ S ∧ d.snd ∈ S) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hd, hs⟩
      by_cases hfst : d.fst ∈ S
      · exact Or.inl ⟨hd, hfst, hs⟩
      · exact Or.inr ⟨hd, hfst, hs⟩
    · rintro (⟨hd, -, hs⟩ | ⟨hd, -, hs⟩) <;> exact ⟨hd, hs⟩
  have hdisj : Disjoint (D.filter (fun d => d.fst ∈ S ∧ d.snd ∈ S))
      (D.filter (fun d => d.fst ∉ S ∧ d.snd ∈ S)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [Finset.mem_filter] at hd1 hd2
    exact hd2.2.1 hd1.2.1
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-- A vertex reachable by `D`-dart steps yields a walk using only `D`-darts. -/
private theorem walk_of_dart_reachable {V : Type*} {G : SimpleGraph V} {s : V}
    (D : Finset G.Dart) {u : V}
    (h : Relation.ReflTransGen
      (fun a b => ∃ d ∈ D, d.fst = a ∧ d.snd = b) s u) :
    ∃ w : G.Walk s u, ∀ d ∈ w.darts, d ∈ D := by
  induction h with
  | refl =>
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | @tail b c _ hres ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨d, hdD, hfst, hsnd⟩ := hres
    have hadj : G.Adj b c := by
      rw [← hfst, ← hsnd]
      exact d.adj
    refine ⟨w.append hadj.toWalk, ?_⟩
    intro e he
    rw [SimpleGraph.Walk.darts_append, SimpleGraph.Adj.darts_toWalk] at he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hw e he
    · have hprod : d.toProd = (b, c) := by
        have heta : d.toProd = (d.fst, d.snd) := rfl
        rw [heta, hfst, hsnd]
      have hdeq : (⟨(b, c), hadj⟩ : G.Dart) = d :=
        SimpleGraph.Dart.ext _ _ hprod.symm
      rw [hdeq]
      exact hdD

/-- Positive balances always yield an `s-t` walk through `D`-darts. -/
private theorem exists_walk_of_balances {V : Type*} [DecidableEq V] [Finite V]
    {G : SimpleGraph V} {s t : V} (D : Finset G.Dart) {m : ℕ}
    (hbal : Balances s t D (m + 1)) :
    ∃ w : G.Walk s t, ∀ d ∈ w.darts, d ∈ D := by
  classical
  let _fintypeV := Fintype.ofFinite V
  set S : Finset V :=
    Finset.univ.filter (fun v => Relation.ReflTransGen
      (fun a b => ∃ d ∈ D, d.fst = a ∧ d.snd = b) s v) with hSdef
  have hsS : s ∈ S := by
    rw [hSdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  have hclosed : ∀ {a b : V}, a ∈ S →
      (∃ d ∈ D, d.fst = a ∧ d.snd = b) → b ∈ S := by
    intro a b ha hab
    rw [hSdef] at ha ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.tail hab
  by_cases htS : t ∈ S
  · rw [hSdef] at htS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htS
    exact walk_of_dart_reachable D htS
  · have hcongr : ∑ x ∈ S, (outCount D x + (if x = t then m + 1 else 0)) =
        ∑ x ∈ S, (inCount D x + (if x = s then m + 1 else 0)) :=
      Finset.sum_congr rfl (fun x _ => hbal x)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hcongr
    have hT : ∑ x ∈ S, (if x = t then m + 1 else 0) = 0 := by
      rw [Finset.sum_ite_eq']
      simp [htS]
    have hS : ∑ x ∈ S, (if x = s then m + 1 else 0) = m + 1 := by
      rw [Finset.sum_ite_eq']
      simp [hsS]
    rw [hT, hS] at hcongr
    have houtF := sum_outCount_eq_card_filter D S
    have hinF := sum_inCount_eq_card_filter D S
    rw [houtF, hinF] at hcongr
    have hpartO := card_filter_fst_partition D S
    have hpartI := card_filter_snd_partition D S
    have hempty : D.filter (fun d => d.fst ∈ S ∧ d.snd ∉ S) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdD, hfstS, hsndS⟩ := hd
      exact hsndS (hclosed hfstS ⟨d, hdD, rfl, rfl⟩)
    rw [hempty, Finset.card_empty] at hpartO
    have hfalse : False := by omega
    exact False.elim hfalse

/-- Positive balances always yield an `s-t` path through `D`-darts. -/
private theorem exists_path_of_balances {V : Type*} [DecidableEq V] [Finite V]
    {G : SimpleGraph V} {s t : V} (D : Finset G.Dart) {m : ℕ}
    (hbal : Balances s t D (m + 1)) :
    ∃ P : G.Path s t, ∀ d ∈ P.val.darts, d ∈ D := by
  obtain ⟨w, hw⟩ := exists_walk_of_balances D hbal
  refine ⟨w.toPath, ?_⟩
  intro d hd
  have hdW : d ∈ w.darts :=
    SimpleGraph.Walk.darts_toPath_subset_darts w hd
  exact hw d hdW

/-- The uncancelled darts carry `k+1` units from `s` to `t`. -/
private theorem D_balances {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t)
    (hdisj : IsEdgeDisjointSTPaths paths) (q : G.Path s t)
    (hq : ∀ d ∈ q.val.darts, d.toProd ∉ UsedPairs paths) :
    Balances s t (DFinset paths q) (k + 1) := by
  intro x
  have hD0 : outCount (D0Finset paths q) x + (if x = t then k + 1 else 0) =
      inCount (D0Finset paths q) x + (if x = s then k + 1 else 0) :=
    D0_balances paths hdisj q hq x
  have hC : outCount (CancelFinset paths q) x =
      inCount (CancelFinset paths q) x :=
    cancel_balanced (D0Finset paths q) x
  have hDdef : DFinset paths q =
      D0Finset paths q \ CancelFinset paths q := rfl
  have hsub : CancelFinset paths q ⊆ D0Finset paths q :=
    Finset.filter_subset _ _
  have hunion : DFinset paths q ∪ CancelFinset paths q =
      D0Finset paths q := by
    rw [hDdef]
    exact Finset.sdiff_union_of_subset hsub
  have hdisjDC : Disjoint (DFinset paths q) (CancelFinset paths q) := by
    rw [hDdef]
    exact Finset.disjoint_sdiff.symm
  have hout := outCount_union hdisjDC x
  have hin := inCount_union hdisjDC x
  rw [hunion] at hout hin
  omega

/-- The uncancelled darts contain no opposite pair. -/
private theorem D_no_symm {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t) (q : G.Path s t)
    {d : G.Dart} (hd : d ∈ DFinset paths q) :
    d.symm ∉ DFinset paths q := by
  simp only [DFinset, CancelFinset, Finset.mem_sdiff, Finset.mem_filter] at hd ⊢
  rintro ⟨hsym0, -⟩
  exact hd.2 ⟨hd.1, hsym0⟩

/-- The uncancelled darts have pairwise distinct edges. -/
private theorem D_edge_unique {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t) (q : G.Path s t)
    {d₁ d₂ : G.Dart} (h₁ : d₁ ∈ DFinset paths q)
    (h₂ : d₂ ∈ DFinset paths q) (he : d₁.edge = d₂.edge) : d₁ = d₂ := by
  rcases (SimpleGraph.dart_edge_eq_iff d₁ d₂).mp he with rfl | hsymm
  · rfl
  · have hcon : d₂.symm ∈ DFinset paths q := by
      rw [← hsymm]
      exact h₁
    exact absurd hcon (D_no_symm paths q h₂)

/-- Removing one path's darts drops the carried flow by one. -/
private theorem balances_sdiff_path {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {s t : V} {n : ℕ} {D : Finset G.Dart}
    (hbal : Balances s t D (n + 1)) {P : G.Path s t}
    (hsub : P.val.darts.toFinset ⊆ D) :
    Balances s t (D \ P.val.darts.toFinset) n := by
  intro x
  have hunion : D \ P.val.darts.toFinset ∪ P.val.darts.toFinset = D :=
    Finset.sdiff_union_of_subset hsub
  have hdisj : Disjoint (D \ P.val.darts.toFinset) P.val.darts.toFinset :=
    Finset.disjoint_sdiff.symm
  have hout := outCount_union hdisj x
  have hin := inCount_union hdisj x
  rw [hunion] at hout hin
  have hP := path_balances P.val P.property x
  have hD := hbal x
  have hTn : (if x = t then n + 1 else 0) =
      (if x = t then n else 0) + (if x = t then 1 else 0) := by
    by_cases ht : x = t <;> simp [ht]
  have hSn : (if x = s then n + 1 else 0) =
      (if x = s then n else 0) + (if x = s then 1 else 0) := by
    by_cases hs : x = s <;> simp [hs]
  rw [hTn, hSn] at hD
  omega

/-- Flow decomposition: balanced darts with unique edges yield disjoint paths. -/
private theorem extract_paths {V : Type*} [DecidableEq V] [Finite V]
    {G : SimpleGraph V} {s t : V} :
    ∀ (n : ℕ) (D : Finset G.Dart), Balances s t D n →
    (∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁.edge = d₂.edge → d₁ = d₂) →
    ∃ paths : Fin n → G.Path s t,
      IsEdgeDisjointSTPaths paths ∧ ∀ i, ∀ d ∈ (paths i).val.darts, d ∈ D := by
  intro n
  induction n with
  | zero =>
    intro D _ _
    refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  | succ n ih =>
    intro D hbal huniq
    obtain ⟨P, hPsub⟩ := exists_path_of_balances D hbal
    have hsub : P.val.darts.toFinset ⊆ D := by
      intro d hd
      rw [List.mem_toFinset] at hd
      exact hPsub d hd
    have hbal' := balances_sdiff_path hbal hsub
    have huniq' : ∀ d₁ ∈ D \ P.val.darts.toFinset,
        ∀ d₂ ∈ D \ P.val.darts.toFinset, d₁.edge = d₂.edge → d₁ = d₂ := by
      intro d₁ hd₁ d₂ hd₂ he
      rw [Finset.mem_sdiff] at hd₁ hd₂
      exact huniq d₁ hd₁.1 d₂ hd₂.1 he
    obtain ⟨paths', hdisj', hsub'⟩ := ih (D \ P.val.darts.toFinset) hbal' huniq'
    refine ⟨Fin.cons P paths', ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · intro j
        refine Fin.cases ?_ ?_ j
        · intro hij e he_i he_j
          exact absurd rfl hij
        · intro j' hij e he_i he_j
          rw [Fin.cons_zero] at he_i
          rw [Fin.cons_succ] at he_j
          obtain ⟨d₁, hd₁mem, hed₁⟩ := edge_mem_dart he_i
          obtain ⟨d₂, hd₂mem, hed₂⟩ := edge_mem_dart he_j
          have hd₁D : d₁ ∈ D := hPsub d₁ hd₁mem
          have h2mem := hsub' j' d₂ hd₂mem
          rw [Finset.mem_sdiff] at h2mem
          have hdeq : d₁ = d₂ :=
            huniq d₁ hd₁D d₂ h2mem.1 (by rw [hed₁, hed₂])
          have hd₁in : d₁ ∈ P.val.darts.toFinset := by
            rw [List.mem_toFinset]
            exact hd₁mem
          rw [hdeq] at hd₁in
          exact h2mem.2 hd₁in
      · intro i' j
        refine Fin.cases ?_ ?_ j
        · intro hij e he_i he_j
          rw [Fin.cons_succ] at he_i
          rw [Fin.cons_zero] at he_j
          obtain ⟨d₁, hd₁mem, hed₁⟩ := edge_mem_dart he_i
          obtain ⟨d₂, hd₂mem, hed₂⟩ := edge_mem_dart he_j
          have hd₂D : d₂ ∈ D := hPsub d₂ hd₂mem
          have h1mem := hsub' i' d₁ hd₁mem
          rw [Finset.mem_sdiff] at h1mem
          have hdeq : d₁ = d₂ :=
            huniq d₁ h1mem.1 d₂ hd₂D (by rw [hed₁, hed₂])
          have hd₂in : d₂ ∈ P.val.darts.toFinset := by
            rw [List.mem_toFinset]
            exact hd₂mem
          rw [← hdeq] at hd₂in
          exact h1mem.2 hd₂in
        · intro j' hij e he_i he_j
          rw [Fin.cons_succ] at he_i he_j
          have hij' : i' ≠ j' := fun h => hij (by rw [h])
          exact hdisj' i' j' hij' e he_i he_j
    · intro i
      refine Fin.cases ?_ ?_ i
      · intro d hd
        rw [Fin.cons_zero] at hd
        exact hPsub d hd
      · intro i' d hd
        rw [Fin.cons_succ] at hd
        have hmem := hsub' i' d hd
        rw [Finset.mem_sdiff] at hmem
        exact hmem.1

/-- A residual path augments `k` disjoint paths to `k+1`. -/
private theorem augment {V : Type*} [Finite V]
    {G : SimpleGraph V} {s t : V} {k : ℕ} (paths : Fin k → G.Path s t)
    (hdisj : IsEdgeDisjointSTPaths paths) (q : G.Path s t)
    (hq : ∀ d ∈ q.val.darts, d.toProd ∉ UsedPairs paths) :
    ∃ paths' : Fin (k + 1) → G.Path s t, IsEdgeDisjointSTPaths paths' := by
  classical
  have hbal := D_balances paths hdisj q hq
  have huniq : ∀ d₁ ∈ DFinset paths q, ∀ d₂ ∈ DFinset paths q,
      d₁.edge = d₂.edge → d₁ = d₂ :=
    fun d₁ h₁ d₂ h₂ he => D_edge_unique paths q h₁ h₂ he
  obtain ⟨paths', hdisj', -⟩ := extract_paths (k + 1) (DFinset paths q) hbal huniq
  exact ⟨paths', hdisj'⟩

/--
The maximum number of edge-disjoint s-t paths equals the minimum size of an s-t cut.
Source: K. Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), 96-115, DOI
10.4064/FM-10-1-96-115.

Proves `Wanted` entry `menger_edge_max_min`.
-/
theorem menger_edge_max_min
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t) :
    ∃ k : ℕ, ∃ (paths : Fin k → G.Path s t) (C : Finset (Sym2 V)),
      IsEdgeDisjointSTPaths paths ∧
      IsSTEdgeCut G s t C ∧
      C.card = k ∧
      (∀ {l : ℕ} (paths' : Fin l → G.Path s t), IsEdgeDisjointSTPaths paths' → l ≤ k) ∧
      (∀ C' : Finset (Sym2 V), IsSTEdgeCut G s t C' → k ≤ C'.card) := by
  obtain ⟨k, C, hCcut, hCcard, hCmin⟩ := exists_min_cut (G := G) (s := s) (t := t) hst
  -- Strong duality: a minimum cut of size `k` is matched by `k` edge-disjoint paths.
  obtain ⟨paths, hdisj⟩ :
      ∃ paths : Fin k → G.Path s t, IsEdgeDisjointSTPaths paths := by
    obtain ⟨kmax, paths_max, hdisj_max, hmax⟩ := exists_max_family (G := G) hst
    by_cases hreach : Relation.ReflTransGen (ResidualRel paths_max) s t
    · obtain ⟨q, hq⟩ := path_of_resid_reachable hreach
      obtain ⟨paths', hdisj'⟩ := augment paths_max hdisj_max q hq
      have hle := hmax paths' hdisj'
      have hnot : ¬ kmax + 1 ≤ kmax := by omega
      exact False.elim (hnot hle)
    · obtain ⟨C', hC', hcard'⟩ :=
        exists_cut_of_not_reachable paths_max hdisj_max hreach
      have hkle : k ≤ kmax := by
        have h := hCmin C' hC'
        omega
      have hkmax : kmax ≤ k := by
        have hle := weak_duality_aux paths_max hdisj_max C hCcut
        omega
      have heq : kmax = k := Nat.le_antisymm hkmax hkle
      subst heq
      exact ⟨paths_max, hdisj_max⟩
  refine ⟨k, paths, C, hdisj, hCcut, hCcard, ?_, hCmin⟩
  intro l paths' hdisj'
  have hle := weak_duality_aux paths' hdisj' C hCcut
  omega

end MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted
end
