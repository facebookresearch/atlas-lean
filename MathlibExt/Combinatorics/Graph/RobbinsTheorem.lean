/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.CompletePartialOrder
import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public section

section
namespace MetaMathlibExt

/-! # Robbins' theorem

A finite undirected simple graph is 2-edge-connected (connected and bridgeless) if and
only if it admits a strongly connected orientation.

Primary source: H. E. Robbins, "A Theorem on Graphs, with an Application to a Problem
of Traffic Control," American Mathematical Monthly 46 (1939), 281–283.
-/

/-- Every vertex in a walk's support is a `getVert` value. -/
private theorem Walk.exists_getVert_of_mem_support {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {c : V} (h : c ∈ p.support) :
    ∃ j, j ≤ p.length ∧ p.getVert j = c := by
  induction p with
  | nil =>
    rw [SimpleGraph.Walk.support_nil] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false]at h
    subst h
    exact ⟨0, Nat.zero_le _, SimpleGraph.Walk.getVert_zero _⟩
  | cons h1 tail ih =>
    rw [SimpleGraph.Walk.support_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, Nat.zero_le _, SimpleGraph.Walk.getVert_zero _⟩
    · obtain ⟨j, hjle, e⟩ := ih h
      exact ⟨j + 1, Nat.succ_le_succ hjle, (SimpleGraph.Walk.getVert_cons_succ _ _).trans e⟩

/-- The first projection of a dart in a walk is a `getVert` value at an index
strictly below the length. -/
private theorem Walk.exists_getVert_lt_of_mem_darts {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) {d : G.Dart} (h : d ∈ w.darts) :
    ∃ k, k < w.length ∧ w.getVert k = d.toProd.1 := by
  induction w with
  | nil =>
    rw [SimpleGraph.Walk.darts_nil] at h
    simp at h
  | cons h1 tail ih =>
    rw [SimpleGraph.Walk.darts_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, Nat.succ_pos _, SimpleGraph.Walk.getVert_zero _⟩
    · obtain ⟨k, hk, e⟩ := ih h
      exact ⟨k + 1, Nat.succ_lt_succ hk, (SimpleGraph.Walk.getVert_cons_succ _ _).trans e⟩

/-- A walk whose darts all satisfy `D` gives a `ReflTransGen` path. -/
private theorem Walk.rt_of_mem_darts {V : Type*} {G : SimpleGraph V} {D : V → V → Prop}
    {a b : V} (w : G.Walk a b) (h : ∀ d ∈ w.darts, D d.toProd.1 d.toProd.2) :
    Relation.ReflTransGen D a b := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons h1 tail ih =>
    have hhead : D _ _ :=
      h { fst := _, snd := _, adj := h1 } (by
        rw [SimpleGraph.Walk.darts_cons]
        exact List.mem_cons_self)
    have htail : Relation.ReflTransGen D _ _ :=
      ih (fun d hd => h d (by
        rw [SimpleGraph.Walk.darts_cons]
        exact List.mem_cons_of_mem _ hd))
    exact Relation.ReflTransGen.head hhead htail

/-- Oriented steps that stay inside graph edges lift to graph reachability. -/
private theorem lift_D_to_reachable {V : Type*} (G : SimpleGraph V)
    (D : V → V → Prop) (hD : ∀ u v, D u v → G.Adj u v) {a b : V}
    (h : Relation.ReflTransGen D a b) : G.Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih => exact ih.tail (hD _ _ hxy)

/-- The edge-deleted relation is symmetric. -/
private theorem delEdge_symm {V : Type*} (G : SimpleGraph V) (u v x y : V)
    (h : G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) :
    G.Adj y x ∧ ¬ ((y = u ∧ x = v) ∨ (y = v ∧ x = u)) := by
  obtain ⟨hadj, hne⟩ := h
  refine ⟨hadj.symm, fun hcon => hne ?_⟩
  rcases hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- Detour: if `D u v` holds but not `D v u`, then `u` reaches `v` even after
deleting the undirected edge `u-v`. -/
private theorem detour {V : Type*} (G : SimpleGraph V)
    (D : V → V → Prop) (hD : ∀ a b, D a b → G.Adj a b)
    (u v : V) (hDuv : D u v) (hDvu : ¬ D v u)
    (hconn : ∀ a b, Relation.ReflTransGen D a b) :
    Relation.ReflTransGen (fun x y => G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) u v := by
  classical
  by_contra hcon
  have key : ∀ (w : V) (_ : Relation.ReflTransGen D v w),
      ¬ Relation.ReflTransGen (fun x y => G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) u
          w := by
    intro w hw
    induction hw with
    | refl => exact hcon
    | tail hrt hxy ih =>
      rename_i x y
      intro hreach
      by_cases hforbid : ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
      · rcases hforbid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcon hreach
        · exact hDvu hxy
      · exact ih (hreach.trans (Relation.ReflTransGen.single
          (delEdge_symm G u v x y ⟨hD _ _ hxy, hforbid⟩)))
  exact key u (hconn v u) Relation.ReflTransGen.refl

/-- Every oriented path lifts to the edge-deleted graph, replacing `u-to-v`
steps by the detour. -/
private theorem lift_past_edge {V : Type*} (G : SimpleGraph V)
    (D : V → V → Prop) (hD : ∀ a b, D a b → G.Adj a b)
    (u v : V) (hDvu : ¬ D v u)
    (hdet : Relation.ReflTransGen (fun x y => G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) u
        v)
    {a b : V} (h : Relation.ReflTransGen D a b) :
    Relation.ReflTransGen (fun x y => G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) a b := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hxy hrt ih =>
    rename_i x y
    by_cases hforbid : ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
    · rcases hforbid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hdet.trans ih
      · exact absurd hxy hDvu
    · exact (Relation.ReflTransGen.single ⟨hD _ _ hxy, hforbid⟩).trans ih

/-- A partial orientation is "good" if it only uses graph edges, is
antisymmetric, and every oriented edge has both endpoints in the strong
component of `r`. -/
private def GoodOr {V : Type*} (G : SimpleGraph V) (r : V) (D : V → V → Prop) : Prop :=
  (∀ x y, D x y → G.Adj x y) ∧
  (∀ x y, D x y → D y x → False) ∧
  (∀ x y, D x y → (Relation.ReflTransGen D r x ∧ Relation.ReflTransGen D x r) ∧
    (Relation.ReflTransGen D r y ∧ Relation.ReflTransGen D y r))

/-- The predicate maximized in the ear-decomposition argument. -/
private def RobbinsPred {V : Type*} [Finite V] (G : SimpleGraph V) (r : V) : ℕ → Prop :=
  fun k => ∃ D : V → V → Prop, GoodOr G r D ∧
    k ≤ Set.ncard {v | Relation.ReflTransGen D r v ∧ Relation.ReflTransGen D v r}

/-- Ear-extension step: a good partial orientation whose strong component of `r`
is not everything can be strictly grown. -/
private theorem extendStrong {V : Type*} [Finite V] (G : SimpleGraph V)
    (hconn : ∀ u v, G.Reachable u v)
    (hbridge : ∀ u v, G.Adj u v → ∀ a b, Relation.ReflTransGen
      (fun x y => G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) a b)
    (r : V) (D : V → V → Prop)
    (hgood : GoodOr G r D)
    (t₀ : V) (ht₀ : ¬ (Relation.ReflTransGen D r t₀ ∧ Relation.ReflTransGen D t₀ r)) :
    ∃ D' : V → V → Prop, GoodOr G r D' ∧
      {v | Relation.ReflTransGen D r v ∧ Relation.ReflTransGen D v r} ⊂
        {v | Relation.ReflTransGen D' r v ∧ Relation.ReflTransGen D' v r} := by
  classical
  obtain ⟨hsub, hanti, hS⟩ := hgood
  -- (1) An edge from the strong component to its complement.
  have hrt : Relation.ReflTransGen G.Adj r t₀ :=
    (SimpleGraph.reachable_iff_reflTransGen r t₀).mp (hconn r t₀)
  have edge_cross : ∃ s t, (Relation.ReflTransGen D r s ∧ Relation.ReflTransGen D s r) ∧
      ¬ (Relation.ReflTransGen D r t ∧ Relation.ReflTransGen D t r) ∧ G.Adj s t := by
    revert ht₀
    induction hrt with
    | refl =>
      intro hmem
      exact absurd ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩ hmem
    | tail hrt hadj ih =>
      rename_i x y
      intro hy
      by_cases hx : (Relation.ReflTransGen D r x ∧ Relation.ReflTransGen D x r)
      · exact ⟨x, y, hx, hy, hadj⟩
      · exact ih hx
  obtain ⟨s, t, hsS, htS, hst⟩ := edge_cross
  -- (2) A simple path back to the strong component in the edge-deleted graph.
  have hdel : Relation.ReflTransGen
      (fun x y => G.Adj x y ∧ ¬ ((x = s ∧ y = t) ∨ (x = t ∧ y = s))) t r :=
    hbridge s t hst t r
  have hdelR : (G.deleteEdges {s(s, t)}).Reachable t r := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    refine Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ hdel
    obtain ⟨hadj, hne⟩ := hxy
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hadj, ?_⟩
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    rw [Sym2.eq_iff] at hmem
    exact hne hmem
  obtain ⟨p, hpath⟩ := hdelR.exists_isPath
  -- (3) Take the shortest prefix ending in the strong component.
  have hrS : Relation.ReflTransGen D r r ∧ Relation.ReflTransGen D r r :=
    ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  have hex : ∃ i, i ≤ p.length ∧ (Relation.ReflTransGen D r (p.getVert i) ∧
      Relation.ReflTransGen D (p.getVert i) r) :=
    ⟨p.length, le_rfl, by rw [p.getVert_length]; exact hrS⟩
  have : DecidablePred (fun i => i ≤ p.length ∧ (Relation.ReflTransGen D r (p.getVert i) ∧
      Relation.ReflTransGen D (p.getVert i) r)) := fun i => Classical.propDecidable _
  set i₀ := Nat.find hex with hi₀def
  have hi₀le : i₀ ≤ p.length := (Nat.find_spec hex).1
  have hi₀S : Relation.ReflTransGen D r (p.getVert i₀) ∧
      Relation.ReflTransGen D (p.getVert i₀) r := (Nat.find_spec hex).2
  have hqpath : (p.take i₀).IsPath := hpath.take i₀
  have hqlen : (p.take i₀).length = i₀ := by
    rw [SimpleGraph.Walk.take_length, min_eq_left hi₀le]
  have honly : ∀ c ∈ (p.take i₀).support,
      (Relation.ReflTransGen D r c ∧ Relation.ReflTransGen D c r) → c = p.getVert i₀ := by
    intro c hc hcmem
    obtain ⟨j, hjle, rfl⟩ := Walk.exists_getVert_of_mem_support (p.take i₀) hc
    have hj0 : j ≤ i₀ := by rw [← hqlen]; exact hjle
    have e1 : (p.take i₀).getVert j = p.getVert j := by
      rw [SimpleGraph.Walk.take_getVert, min_eq_right hj0]
    rw [e1] at hcmem ⊢
    have hQ : j ≤ p.length ∧ (Relation.ReflTransGen D r (p.getVert j) ∧
        Relation.ReflTransGen D (p.getVert j) r) := ⟨le_trans hj0 hi₀le, hcmem⟩
    have hmin : i₀ ≤ j := Nat.find_min' hex hQ
    have hji : j = i₀ := le_antisymm hj0 hmin
    rw [hji]
  -- (4) The new orientation: old arcs, `s → t`, and the path darts forward.
  set D' : V → V → Prop := fun x y => D x y ∨ (x = s ∧ y = t) ∨
    ∃ d : (G.deleteEdges {s(s, t)}).Dart, d ∈ (p.take i₀).darts ∧
      d.toProd.1 = x ∧ d.toProd.2 = y with hD'def
  have hD'ch : ∀ x y, D' x y ↔ (D x y ∨ (x = s ∧ y = t) ∨
      ∃ d : (G.deleteEdges {s(s, t)}).Dart, d ∈ (p.take i₀).darts ∧
        d.toProd.1 = x ∧ d.toProd.2 = y) := fun x y => Iff.rfl
  have hdartfst : ∀ d : (G.deleteEdges {s(s, t)}).Dart, d ∈ (p.take i₀).darts →
      ¬ (Relation.ReflTransGen D r d.toProd.1 ∧
        Relation.ReflTransGen D d.toProd.1 r) := by
    intro d hd hmem
    obtain ⟨k, hk, ek⟩ := Walk.exists_getVert_lt_of_mem_darts (p.take i₀) hd
    rw [hqlen] at hk
    have ek' : (p.take i₀).getVert k = p.getVert k := by
      rw [SimpleGraph.Walk.take_getVert, min_eq_right hk.le]
    rw [← ek] at hmem
    rw [ek'] at hmem
    have hQ : k ≤ p.length ∧ (Relation.ReflTransGen D r (p.getVert k) ∧
        Relation.ReflTransGen D (p.getVert k) r) := ⟨le_trans hk.le hi₀le, hmem⟩
    have hmin : i₀ ≤ k := Nat.find_min' hex hQ
    omega
  have hdartdel : ∀ d : (G.deleteEdges {s(s, t)}).Dart, d ∈ (p.take i₀).darts →
      ¬ ((d.toProd.1 = s ∧ d.toProd.2 = t) ∨
        (d.toProd.1 = t ∧ d.toProd.2 = s)) := by
    intro d hd hcon
    have hadj := (SimpleGraph.deleteEdges_adj.mp d.adj).2
    rw [Set.mem_singleton_iff] at hadj
    rcases hcon with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2] at hadj
      exact hadj rfl
    · have hswap : s(d.toProd.1, d.toProd.2) = s(s, t) := by
        rw [e1, e2, Sym2.eq_iff]
        exact Or.inr ⟨rfl, rfl⟩
      exact hadj hswap
  have dsub : ∀ a b, D a b → D' a b := fun a b h => (hD'ch a b).mpr (Or.inl h)
  have monoD : ∀ {x y}, Relation.ReflTransGen D x y → Relation.ReflTransGen D' x y :=
    fun h => Relation.ReflTransGen.mono dsub _ _ h
  have hmemT : Relation.ReflTransGen D' r t := by
    have hrs : Relation.ReflTransGen D' r s := monoD hsS.1
    have hst' : D' s t := (hD'ch s t).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact hrs.trans (Relation.ReflTransGen.single hst')
  have hmemTr : Relation.ReflTransGen D' t r := by
    have hqb : Relation.ReflTransGen D' t (p.getVert i₀) := by
      change Relation.ReflTransGen (fun x y => D x y ∨ (x = s ∧ y = t) ∨
        ∃ d : (G.deleteEdges {s(s, t)}).Dart, d ∈ (p.take i₀).darts ∧
          d.toProd.1 = x ∧ d.toProd.2 = y) t (p.getVert i₀)
      refine Walk.rt_of_mem_darts (p.take i₀) (fun d hd => ?_)
      exact Or.inr (Or.inr ⟨d, hd, rfl, rfl⟩)
    exact hqb.trans (monoD hi₀S.2)
  have hpre : ∀ (c : V) (j : ℕ), j ≤ (p.take i₀).length → (p.take i₀).getVert j = c →
      Relation.ReflTransGen D' t c := by
    intro c j hjle e
    subst e
    change Relation.ReflTransGen (fun x y => D x y ∨ (x = s ∧ y = t) ∨
      ∃ d : (G.deleteEdges {s(s, t)}).Dart, d ∈ (p.take i₀).darts ∧
        d.toProd.1 = x ∧ d.toProd.2 = y) t ((p.take i₀).getVert j)
    refine Walk.rt_of_mem_darts ((p.take i₀).take j) (fun d hd => ?_)
    rw [SimpleGraph.Walk.darts_take] at hd
    exact Or.inr (Or.inr ⟨d, List.take_subset _ _ hd, rfl, rfl⟩)
  have hsuf : ∀ (c : V) (j : ℕ), j ≤ (p.take i₀).length → (p.take i₀).getVert j = c →
      Relation.ReflTransGen D' c (p.getVert i₀) := by
    intro c j hjle e
    subst e
    change Relation.ReflTransGen (fun x y => D x y ∨ (x = s ∧ y = t) ∨
      ∃ d : (G.deleteEdges {s(s, t)}).Dart, d ∈ (p.take i₀).darts ∧
        d.toProd.1 = x ∧ d.toProd.2 = y) ((p.take i₀).getVert j) (p.getVert i₀)
    refine Walk.rt_of_mem_darts ((p.take i₀).drop j) (fun d hd => ?_)
    rw [SimpleGraph.Walk.darts_drop] at hd
    exact Or.inr (Or.inr ⟨d, List.drop_subset _ _ hd, rfl, rfl⟩)
  have hdartmem : ∀ d : (G.deleteEdges {s(s, t)}).Dart, d ∈ (p.take i₀).darts →
      ((Relation.ReflTransGen D' r d.toProd.1 ∧ Relation.ReflTransGen D' d.toProd.1 r) ∧
        (Relation.ReflTransGen D' r d.toProd.2 ∧ Relation.ReflTransGen D' d.toProd.2 r)) := by
    intro d hd
    obtain ⟨k, hk, ek⟩ := Walk.exists_getVert_lt_of_mem_darts (p.take i₀) hd
    obtain ⟨j, hjle, ej⟩ := Walk.exists_getVert_of_mem_support (p.take i₀)
      (SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ hd)
    have h1r : Relation.ReflTransGen D' r d.toProd.1 := hmemT.trans (hpre _ k hk.le ek)
    have hr1 : Relation.ReflTransGen D' d.toProd.1 r :=
      (hsuf _ k hk.le ek).trans (monoD hi₀S.2)
    have h2r : Relation.ReflTransGen D' r d.toProd.2 := hmemT.trans (hpre _ j hjle ej)
    have hr2 : Relation.ReflTransGen D' d.toProd.2 r :=
      (hsuf _ j hjle ej).trans (monoD hi₀S.2)
    exact ⟨⟨h1r, hr1⟩, ⟨h2r, hr2⟩⟩
  -- (5) Assemble.
  refine ⟨D', ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y h
    rw [hD'ch x y] at h
    rcases h with hD | ⟨rfl, rfl⟩ | ⟨d, hd, e1, e2⟩
    · exact hsub x y hD
    · exact hst
    · rw [← e1, ← e2]
      exact (SimpleGraph.deleteEdges_adj.mp d.adj).1
  · intro x y hxy hyx
    rw [hD'ch x y] at hxy
    rw [hD'ch y x] at hyx
    rcases hxy with hDxy | ⟨e1, e2⟩ | ⟨d₁, hd₁, e1, e2⟩
    · obtain hDyx | ⟨f1, f2⟩ | ⟨d₂, hd₂, g1, g2⟩ := hyx
      · exact hanti x y hDxy hDyx
      · have hxS := (hS x y hDxy).1
        rw [f2] at hxS
        exact htS hxS
      · have hyS := (hS x y hDxy).2
        rw [← g1] at hyS
        exact hdartfst d₂ hd₂ hyS
    · rw [e1, e2] at hyx
      obtain hD | ⟨f1, f2⟩ | ⟨d₂, hd₂, g1, g2⟩ := hyx
      · exact htS (hS t s hD).1
      · exact G.ne_of_adj hst f2
      · exact hdartdel d₂ hd₂ (Or.inr ⟨g1, g2⟩)
    · subst e1
      subst e2
      obtain hD | ⟨f1, f2⟩ | ⟨d₂, hd₂, g1, g2⟩ := hyx
      · exact hdartfst d₁ hd₁ (hS _ _ hD).2
      · exact hdartdel d₁ hd₁ (Or.inr ⟨f2, f1⟩)
      · have heq : SimpleGraph.Dart.edge d₁ = SimpleGraph.Dart.edge d₂ := by
          change s(d₁.toProd.1, d₁.toProd.2) = s(d₂.toProd.1, d₂.toProd.2)
          rw [g1, g2, Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩
        have hnodup : ((p.take i₀).darts).Nodup :=
          SimpleGraph.Walk.darts_nodup_of_support_nodup hqpath.support_nodup
        have hmapnodup :
            (List.map SimpleGraph.Dart.edge (p.take i₀).darts).Nodup := by
          rw [← SimpleGraph.Walk.edges_eq_map_darts]
          exact hqpath.isTrail.edges_nodup
        have hinj := (List.nodup_map_iff_inj_on hnodup).mp hmapnodup d₁ hd₁ d₂ hd₂ heq
        have hcontra : d₂.toProd.1 = d₂.toProd.2 := hinj ▸ g1
        have hloop : (G.deleteEdges {s(s, t)}).Adj d₂.toProd.2 d₂.toProd.2 :=
          hcontra ▸ d₂.adj
        exact (G.deleteEdges {s(s, t)}).ne_of_adj hloop rfl
  · intro x y h
    rw [hD'ch x y] at h
    rcases h with hD | ⟨rfl, rfl⟩ | ⟨d, hd, e1, e2⟩
    · obtain ⟨hxS, hyS⟩ := hS x y hD
      exact ⟨⟨monoD hxS.1, monoD hxS.2⟩, ⟨monoD hyS.1, monoD hyS.2⟩⟩
    · exact ⟨⟨monoD hsS.1, monoD hsS.2⟩, ⟨hmemT, hmemTr⟩⟩
    · rw [← e1, ← e2]
      exact hdartmem d hd
  · refine lt_of_le_of_ne' ?_ ?_
    · intro v hv
      exact ⟨monoD hv.1, monoD hv.2⟩
    · intro heq
      apply htS
      have hmem : t ∈ ({v | Relation.ReflTransGen D' r v ∧
          Relation.ReflTransGen D' v r} : Set V) := ⟨hmemT, hmemTr⟩
      rw [heq] at hmem
      exact hmem
/-- Once the strong component is everything, complete to a total orientation by
a fixed linear order without losing strong connectivity. -/
private theorem completeStrong {V : Type*} [Finite V] (G : SimpleGraph V)
    (r : V) (D : V → V → Prop) (hgood : GoodOr G r D)
    (hfull : ∀ v, Relation.ReflTransGen D r v ∧ Relation.ReflTransGen D v r) :
    ∃ D' : V → V → Prop, (∀ u v, D' u v → G.Adj u v) ∧
      (∀ u v, G.Adj u v → Xor (D' u v) (D' v u)) ∧
      (∀ u v, Relation.ReflTransGen D' u v) := by
  classical
  obtain ⟨hsub, hanti, -⟩ := hgood
  set Dtot : V → V → Prop := fun x y => D x y ∨ (G.Adj x y ∧ ¬ D x y ∧ ¬ D y x ∧
    (Finite.equivFin V) x < (Finite.equivFin V) y) with hDdef
  have hDch : ∀ x y, Dtot x y ↔ (D x y ∨ (G.Adj x y ∧ ¬ D x y ∧ ¬ D y x ∧
      (Finite.equivFin V) x < (Finite.equivFin V) y)) := fun x y => Iff.rfl
  have dsub : ∀ a b, D a b → Dtot a b := fun a b h => (hDch a b).mpr (Or.inl h)
  have monoD : ∀ {x y}, Relation.ReflTransGen D x y → Relation.ReflTransGen Dtot x y :=
    fun h => Relation.ReflTransGen.mono dsub _ _ h
  refine ⟨Dtot, ?_, ?_, ?_⟩
  · intro x y h
    rw [hDch x y] at h
    rcases h with hD | ⟨hadj, -, -, -⟩
    · exact hsub x y hD
    · exact hadj
  · intro x y hxy
    rw [xor_def, hDch x y, hDch y x]
    by_cases hDx : D x y
    · refine Or.inl ⟨Or.inl hDx, fun hcon => ?_⟩
      rcases hcon with hDy | ⟨-, -, hDx', -⟩
      · exact hanti x y hDx hDy
      · exact hDx' hDx
    · by_cases hDy : D y x
      · refine Or.inr ⟨Or.inl hDy, fun hcon => ?_⟩
        rcases hcon with hDx' | ⟨-, -, hDy', -⟩
        · exact hDx hDx'
        · exact hDy' hDy
      · have hne : x ≠ y := G.ne_of_adj hxy
        have hlt := lt_trichotomy ((Finite.equivFin V) x) ((Finite.equivFin V) y)
        rcases hlt with hlt | heq | hlt
        · refine Or.inl ⟨Or.inr ⟨hxy, hDx, hDy, hlt⟩, fun hcon => ?_⟩
          rcases hcon with hDy' | ⟨-, -, -, hlt'⟩
          · exact hDy hDy'
          · exact absurd hlt' (not_lt.mpr (le_of_lt hlt))
        · exfalso
          apply hne
          exact (Finite.equivFin V).injective heq
        · refine Or.inr ⟨Or.inr ⟨hxy.symm, hDy, hDx, hlt⟩, fun hcon => ?_⟩
          rcases hcon with hDx' | ⟨-, -, -, hlt'⟩
          · exact hDx hDx'
          · exact absurd hlt' (not_lt.mpr (le_of_lt hlt))
  · intro a b
    exact (monoD (hfull a).2).trans (monoD (hfull b).1)
/-- **Robbins' theorem.** Let $G$ be a simple graph on a finite nonempty vertex set $V$. Then $G$
is connected and, after deleting any single edge of $G$, every vertex is still reachable from
every vertex (that is, $G$ is 2-edge-connected) if and only if $G$ has a strongly connected
orientation: a relation $D$ on $V$ such that $D(u, v)$ holds only when $u$ and $v$ are
adjacent, for every edge $uv$ exactly one of $D(u, v)$ and $D(v, u)$ holds, and every vertex
$v$ can be reached from every vertex $u$ by a finite, possibly empty, sequence of $D$-steps.

Source: H. E. Robbins, "A Theorem on Graphs, with an Application to a Problem
of Traffic Control," American Mathematical Monthly 46 (1939), 281–283;
https://en.wikipedia.org/wiki/Robbins%27_theorem
-/
theorem robbins_theorem_connected {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V) :
    (G.Connected ∧
      ∀ u v, G.Adj u v →
        ∀ a b, Relation.ReflTransGen
          (fun x y => G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) a b) ↔
    ∃ D : V → V → Prop, (∀ u v, D u v → G.Adj u v) ∧
      (∀ u v, G.Adj u v → Xor (D u v) (D v u)) ∧
      (∀ u v, Relation.ReflTransGen D u v) := by
  classical
  constructor
  · rintro ⟨hconn, hbridge⟩
    have hneV : Nonempty V := inferInstance
    have r : V := Classical.choice hneV
    have : DecidablePred (RobbinsPred G r) := fun n => Classical.propDecidable _
    have hP0 : RobbinsPred G r 0 := by
      refine ⟨fun _ _ => False, ⟨?_, ?_, ?_⟩, Nat.zero_le _⟩
      · intro x y h
        exact False.elim h
      · intro x y h
        exact False.elim h
      · intro x y h
        exact False.elim h
    have hstar : RobbinsPred G r (Nat.findGreatest (RobbinsPred G r) (Nat.card V)) :=
      Nat.findGreatest_spec (Nat.zero_le _) hP0
    obtain ⟨Dstar, hgoodstar, hkstar⟩ := hstar
    have hcard : ∀ D : V → V → Prop, Set.ncard
        {v | Relation.ReflTransGen D r v ∧ Relation.ReflTransGen D v r} ≤ Nat.card V := by
      intro D
      have h1 : Set.ncard {v | Relation.ReflTransGen D r v ∧
          Relation.ReflTransGen D v r} ≤ Set.univ.ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
      rwa [Set.ncard_univ] at h1
    by_cases hfull : ∀ v, Relation.ReflTransGen Dstar r v ∧
        Relation.ReflTransGen Dstar v r
    · exact completeStrong G r Dstar hgoodstar hfull
    · have hne : {v | Relation.ReflTransGen Dstar r v ∧
          Relation.ReflTransGen Dstar v r} ≠ Set.univ := by
        intro heq
        apply hfull
        intro v
        have hmem : v ∈ ({v | Relation.ReflTransGen Dstar r v ∧
            Relation.ReflTransGen Dstar v r} : Set V) := by
          rw [heq]
          exact Set.mem_univ v
        exact hmem
      obtain ⟨t₀, ht₀⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
      obtain ⟨D', hgood', hstrict⟩ :=
        extendStrong G hconn.preconnected hbridge r Dstar hgoodstar t₀ ht₀
      have hlt : Set.ncard {v | Relation.ReflTransGen Dstar r v ∧
          Relation.ReflTransGen Dstar v r} <
          Set.ncard {v | Relation.ReflTransGen D' r v ∧
            Relation.ReflTransGen D' v r} :=
        Set.ncard_lt_ncard hstrict (Set.finite_univ.subset (Set.subset_univ _))
      have hPnext : RobbinsPred G r
          (Nat.findGreatest (RobbinsPred G r) (Nat.card V) + 1) :=
        ⟨D', hgood', Nat.succ_le_of_lt (lt_of_le_of_lt hkstar hlt)⟩
      have hle : Nat.findGreatest (RobbinsPred G r) (Nat.card V) + 1 ≤ Nat.card V :=
        le_trans (Nat.succ_le_of_lt (lt_of_le_of_lt hkstar hlt)) (hcard D')
      exact absurd hPnext
        (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle)
  · rintro ⟨D, hDsub, hDxor, hDconn⟩
    refine ⟨?_, ?_⟩
    · exact (SimpleGraph.connected_iff G).mpr
        ⟨fun u v => lift_D_to_reachable G D hDsub (hDconn u v), inferInstance⟩
    · intro u v huv a b
      rcases hDxor u v huv with ⟨hDuv, hDvu⟩ | ⟨hDvu, hDuv⟩
      · exact lift_past_edge G D hDsub u v hDvu
          (detour G D hDsub u v hDuv hDvu hDconn) (hDconn a b)
      · have h := lift_past_edge G D hDsub v u hDuv
          (detour G D hDsub v u hDvu hDuv hDconn) (hDconn a b)
        refine Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ h
        obtain ⟨hadj, hne⟩ := hxy
        refine ⟨hadj, fun hcon => hne ?_⟩
        rcases hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
/-- **Robbins' theorem, allowing the empty graph.** Let $G$ be a simple graph on a finite,
possibly empty, vertex set $V$. Then every vertex of $G$ is reachable from every vertex and,
after deleting any single edge of $G$, every vertex is still reachable from every vertex, if
and only if $G$ has a strongly connected orientation: a relation $D$ on $V$ such that $D(u, v)$
holds only when $u$ and $v$ are adjacent, for every edge $uv$ exactly one of $D(u, v)$ and
$D(v, u)$ holds, and every vertex $v$ can be reached from every vertex $u$ by a finite,
possibly empty, sequence of $D$-steps.

For nonempty $V$ the left-hand condition says that $G$ is 2-edge-connected; for empty $V$ both
sides hold.

Proves `Wanted` entry `robbins_theorem`.

Source: https://en.wikipedia.org/wiki/Robbins%27_theorem
-/
theorem robbins_theorem {V : Type*} [Finite V] (G : SimpleGraph V) :
    ((∀ u v, G.Reachable u v) ∧
      ∀ u v, G.Adj u v →
        ∀ a b, Relation.ReflTransGen
          (fun x y => G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) a b) ↔
    ∃ D : V → V → Prop, (∀ u v, D u v → G.Adj u v) ∧
      (∀ u v, G.Adj u v → Xor (D u v) (D v u)) ∧
      (∀ u v, Relation.ReflTransGen D u v) := by
  classical
  constructor
  · rintro ⟨hconn, hbridge⟩
    by_cases hE : IsEmpty V
    · have := hE
      refine ⟨fun _ _ => False, ?_, ?_, ?_⟩
      · intro u v h
        exact False.elim h
      · intro u v huv
        exact (IsEmpty.false u).elim
      · intro u v
        exact (IsEmpty.false u).elim
    · have hneV : Nonempty V := not_isEmpty_iff.mp hE
      have hc : (∀ u v, G.Reachable u v) ↔ G.Connected :=
        ⟨fun h => (SimpleGraph.connected_iff G).mpr ⟨h, hneV⟩, fun h => h.preconnected⟩
      exact (@robbins_theorem_connected V inferInstance hneV G).mp ⟨hc.mp hconn, hbridge⟩
  · rintro ⟨D, hDsub, hDxor, hDconn⟩
    by_cases hE : IsEmpty V
    · have := hE
      exact ⟨fun u v => (IsEmpty.false u).elim,
        fun u v _ => (IsEmpty.false u).elim⟩
    · have hneV : Nonempty V := not_isEmpty_iff.mp hE
      obtain ⟨hC, hb⟩ :=
        (@robbins_theorem_connected V inferInstance hneV G).mpr ⟨D, hDsub, hDxor, hDconn⟩
      exact ⟨hC.preconnected, hb⟩

end MetaMathlibExt
end
