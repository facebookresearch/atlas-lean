/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat

@[expose] public section

section
namespace MetaMathlibExt

/-- A chain from `s` to `t` taking only values in `{s, t}` forces `Adj s t` or `s = t`. -/
private theorem chain_two_valued {V : Type*} (G : SimpleGraph V) (s t : V) :
    ∀ (l : List V), l.head? = some s → l.getLast? = some t →
      List.IsChain G.Adj l → (∀ v ∈ l, v = s ∨ v = t) → G.Adj s t ∨ s = t := by
  intro l
  match l with
  | [] => intro hhead _ _ _; simp at hhead
  | [a] =>
    intro hhead hlast _ _
    have has : a = s := by simpa using hhead
    have hat : a = t := by simpa using hlast
    exact Or.inr (has.symm.trans hat)
  | a :: b :: l =>
    intro hhead hlast hchain hall
    simp only [List.head?_cons] at hhead
    rw [List.getLast?_cons_cons] at hlast
    rw [List.isChain_cons_cons] at hchain
    obtain ⟨hadj, hchain'⟩ := hchain
    have hb : b = s ∨ b = t := hall b (List.mem_cons_of_mem _ List.mem_cons_self)
    cases hb with
    | inr hbt =>
      have has : a = s := Option.some_inj.mp hhead
      subst has
      subst hbt
      exact Or.inl hadj
    | inl hbs =>
      have hhead' : (b :: l).head? = some s := by simp [hbs]
      exact chain_two_valued G s t (b :: l) hhead' hlast hchain'
        (fun v hv => hall v (List.mem_cons_of_mem _ hv))

/-- Every s-t walk with s ≠ t nonadjacent has an internal vertex. -/
private theorem exists_internal_vertex {V : Type*} (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (hnadj : ¬ G.Adj s t) (p : G.Walk s t) :
    ∃ v ∈ p.support, v ≠ s ∧ v ≠ t := by
  by_contra hcon
  have hall : ∀ v ∈ p.support, v = s ∨ v = t := by
    intro v hv
    by_cases heq : v = s
    · exact Or.inl heq
    · right
      by_contra ht
      exact hcon ⟨v, hv, heq, ht⟩
  have hhead : p.support.head? = some s := by
    rw [List.head?_eq_some_head p.support_ne_nil, p.head_support]
  have hlast : p.support.getLast? = some t := by
    rw [List.getLast?_eq_some_getLast p.support_ne_nil, p.getLast_support]
  obtain hA | hE := chain_two_valued G s t p.support hhead hlast
    p.isChain_adj_support hall
  · exact hnadj hA
  · exact hne hE

/-- Some separator exists: all vertices but `s`, `t` hit every s-t walk. -/
private theorem sep_univ {V : Type*} [Finite V] (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (hnadj : ¬ G.Adj s t) :
    ∃ C : Finset V, s ∉ C ∧ t ∉ C ∧ (∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C) := by
  classical
  have := Fintype.ofFinite V
  refine ⟨(Finset.univ.erase s).erase t, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro p
    obtain ⟨v, hv, hvs, hvt⟩ := exists_internal_vertex G s t hne hnadj p
    refine ⟨v, hv, ?_⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hvt, hvs⟩

/-- A minimum separator exists (least cardinality among separators). -/
private theorem min_separator {V : Type*} [Finite V] (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (hnadj : ¬ G.Adj s t) :
    ∃ n : ℕ, ∃ C : Finset V, C.card = n ∧ s ∉ C ∧ t ∉ C ∧
      (∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C) ∧
      ∀ C' : Finset V, s ∉ C' → t ∉ C' →
        (∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C') → n ≤ C'.card := by
  obtain ⟨C₀, hs₀, ht₀, hhit₀⟩ := sep_univ G s t hne hnadj
  let S : Set ℕ := {n | ∃ C : Finset V, C.card = n ∧ s ∉ C ∧ t ∉ C ∧
    (∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C)}
  have hmem0 : C₀.card ∈ S := ⟨C₀, rfl, hs₀, ht₀, hhit₀⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem ⟨C₀.card, hmem0⟩
  obtain ⟨C, hCcard, hsC, htC, hhitC⟩ := hmem
  exact ⟨sInf S, C, hCcard, hsC, htC, hhitC,
    fun C' hs' ht' hhit' => Nat.sInf_le ⟨C', rfl, hs', ht', hhit'⟩⟩

/-- Easy direction: any internally-disjoint family is no larger than any separator. -/
private theorem family_le_sep {V : Type*} (G : SimpleGraph V) (s t : V)
    (_hne : s ≠ t) (_hnadj : ¬ G.Adj s t)
    (m : ℕ) (Q : Fin m → G.Walk s t)
    (_hQnodup : ∀ i, (Q i).support.Nodup)
    (hQdisj : ∀ i j, i ≠ j → ∀ v, v ∈ (Q i).support → v ∈ (Q j).support → v = s ∨ v = t)
    (C' : Finset V) (hs' : s ∉ C') (ht' : t ∉ C')
    (hhit' : ∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C') : m ≤ C'.card := by
  classical
  choose f hfmem hfC using (fun i => hhit' (Q i))
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hneij
    have hmem : f i ∈ (Q j).support := by rw [hij]; exact hfmem j
    obtain hs_or | ht_or := hQdisj i j hneij (f i) (hfmem i) hmem
    · exact hs' (hs_or ▸ hfC i)
    · exact ht' (ht_or ▸ hfC i)
  have hcard : (Finset.image f Finset.univ).card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : Finset.image f Finset.univ ⊆ C' := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfC i
  calc m = (Finset.image f Finset.univ).card := hcard.symm
    _ ≤ C'.card := Finset.card_le_card hsub

/-- Any internally-disjoint family is bounded by the number of vertices. -/
private theorem family_bound {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (hnadj : ¬ G.Adj s t)
    (m : ℕ) (Q : Fin m → G.Walk s t)
    (_hQnodup : ∀ i, (Q i).support.Nodup)
    (hQdisj : ∀ i j, i ≠ j → ∀ v, v ∈ (Q i).support → v ∈ (Q j).support → v = s ∨ v = t) :
    m ≤ Fintype.card V := by
  classical
  choose f hf using (fun i => exists_internal_vertex G s t hne hnadj (Q i))
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hneij
    obtain ⟨hmemi, hnesi, hneti⟩ := hf i
    have hmem : f i ∈ (Q j).support := by rw [hij]; exact (hf j).1
    obtain hs_or | ht_or := hQdisj i j hneij (f i) hmemi hmem
    · exact hnesi hs_or
    · exact hneti ht_or
  have hcard : (Finset.image f Finset.univ).card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  calc m = (Finset.image f Finset.univ).card := hcard.symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card V := Finset.card_univ

/-- A maximum internally-disjoint family exists. -/
private theorem max_family {V : Type*} [Finite V] (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (hnadj : ¬ G.Adj s t) :
    ∃ n : ℕ, ∃ P : Fin n → G.Walk s t, (∀ i, (P i).support.Nodup) ∧
      (∀ i j, i ≠ j → ∀ v, v ∈ (P i).support → v ∈ (P j).support → v = s ∨ v = t) ∧
      ∀ (m : ℕ) (Q : Fin m → G.Walk s t), (∀ i, (Q i).support.Nodup) →
        (∀ i j, i ≠ j → ∀ v, v ∈ (Q i).support → v ∈ (Q j).support → v = s ∨ v = t) →
        m ≤ n := by
  classical
  have := Fintype.ofFinite V
  let S : Set ℕ := {m | ∃ Q : Fin m → G.Walk s t, (∀ i, (Q i).support.Nodup) ∧
    (∀ i j, i ≠ j → ∀ v, v ∈ (Q i).support → v ∈ (Q j).support → v = s ∨ v = t)}
  have h0 : (0 : ℕ) ∈ S :=
    ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  have hbdd : S ⊆ ↑(Finset.range (Fintype.card V + 1)) := by
    intro m hm
    obtain ⟨Q, hQn, hQd⟩ := hm
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (family_bound G s t hne hnadj m Q hQn hQd)
  have hfin : S.Finite := Set.Finite.subset (Finset.finite_toSet _) hbdd
  have hneS : hfin.toFinset.Nonempty := ⟨0, hfin.mem_toFinset.mpr h0⟩
  refine ⟨hfin.toFinset.max' hneS, ?_⟩
  have hmem : hfin.toFinset.max' hneS ∈ S :=
    hfin.mem_toFinset.mp (Finset.max'_mem _ hneS)
  obtain ⟨P, hPn, hPd⟩ := hmem
  exact ⟨P, hPn, hPd, fun m Q hQn hQd =>
    Finset.le_max' _ _ (hfin.mem_toFinset.mpr ⟨Q, hQn, hQd⟩)⟩

/-- Capacity in the vertex-split network on `V × Bool` (`false` = entry,
`true` = exit): unit capacity on internal vertex arcs, `big` on `s`/`t`
vertex arcs and on arcs following graph edges, zero elsewhere. -/
private def splitCap {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ) :
    (V × Bool) → (V × Bool) → ℕ
  | (u, false), (v, true) =>
      if u = v then (if u = s ∨ u = t then big else 1) else 0
  | (u, true), (v, false) =>
      if G.Adj u v then big else 0
  | _, _ => 0

/-- A feasible `ℕ`-flow in the split network: bounded by capacities,
conserved away from source/sink, with no inflow to the source and no
outflow from the sink. -/
private def IsSplitFlow {V : Type*} [Fintype V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (S T : V × Bool)
    (f : (V × Bool) → (V × Bool) → ℕ) : Prop :=
  (∀ a b, f a b ≤ cap a b) ∧
  (∀ w, w ≠ S → w ≠ T → ∑ u : V × Bool, f u w = ∑ v : V × Bool, f w v) ∧
  (∀ v, f v S = 0) ∧
  (∀ v, f T v = 0)

/-- Flow value: outflow from the source. -/
private def splitValue {V : Type*} [Fintype V] (S : V × Bool)
    (f : (V × Bool) → (V × Bool) → ℕ) : ℕ :=
  ∑ v : V × Bool, f S v

/-- Cut capacity: total capacity of arcs leaving the set. -/
private def splitCutCap {V : Type*} [Fintype V] [DecidableEq V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (C : Finset (V × Bool)) : ℕ :=
  ∑ u ∈ C, ∑ v ∈ Finset.univ \ C, cap u v

/-- Vertex arcs have unit capacity away from `s`, `t`. -/
private theorem splitCap_self {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ) (v : V) :
    splitCap G s t big (v, false) (v, true) =
      (if v = s ∨ v = t then big else 1) := by
  simp only [splitCap, ↓reduceIte]

/-- Vertex arcs between distinct vertices vanish. -/
private theorem splitCap_self_ne {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ) {u v : V}
    (h : u ≠ v) :
    splitCap G s t big (u, false) (v, true) = 0 := by
  simp only [splitCap, h, ↓reduceIte]

/-- Edge arcs follow graph adjacency with capacity `big`. -/
private theorem splitCap_edge {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ) {u v : V}
    (h : G.Adj u v) :
    splitCap G s t big (u, true) (v, false) = big := by
  simp only [splitCap, h, ↓reduceIte]

/-- Non-edge arcs vanish. -/
private theorem splitCap_edge_not {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ) {u v : V}
    (h : ¬ G.Adj u v) :
    splitCap G s t big (u, true) (v, false) = 0 := by
  simp only [splitCap, h, ↓reduceIte]

/-- Entry-to-entry arcs vanish. -/
private theorem splitCap_ff {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ) (u v : V) :
    splitCap G s t big (u, false) (v, false) = 0 := by
  rfl

/-- Exit-to-exit arcs vanish. -/
private theorem splitCap_tt {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ) (u v : V) :
    splitCap G s t big (u, true) (v, true) = 0 := by
  rfl

/-- Flow across a cut (`ℕ` version): value plus backward flow equals forward flow. -/
private theorem split_cut_flow {V : Type*} [Fintype V] [DecidableEq V]
    (S T : V × Bool) (f : (V × Bool) → (V × Bool) → ℕ)
    (hcons : ∀ w, w ≠ S → w ≠ T →
      ∑ u : V × Bool, f u w = ∑ v : V × Bool, f w v)
    (hS : ∀ v, f v S = 0)
    (C : Finset (V × Bool)) (hSC : S ∈ C) (hTC : T ∉ C) :
    splitValue S f + (∑ u ∈ C, ∑ v ∈ Finset.univ \ C, f v u) =
      (∑ u ∈ C, ∑ v ∈ Finset.univ \ C, f u v) := by
  have hsplit_out : ∀ w : V × Bool, (∑ v : V × Bool, f w v) =
      (∑ v ∈ C, f w v) + ∑ v ∈ Finset.univ \ C, f w v := by
    intro w
    have h := Finset.sum_sdiff (Finset.subset_univ C) (f := fun v => f w v)
    rw [add_comm]
    exact h.symm
  have hsplit_in : ∀ w : V × Bool, (∑ u : V × Bool, f u w) =
      (∑ u ∈ C, f u w) + ∑ u ∈ Finset.univ \ C, f u w := by
    intro w
    have h := Finset.sum_sdiff (Finset.subset_univ C) (f := fun u => f u w)
    rw [add_comm]
    exact h.symm
  have hrest : ∑ w ∈ C.erase S, (∑ v : V × Bool, f w v) =
      ∑ w ∈ C.erase S, (∑ u : V × Bool, f u w) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mem_erase] at hw
    exact (hcons w hw.1 (fun heq => hTC (heq ▸ hw.2))).symm
  have hinflowS : (∑ u : V × Bool, f u S) = 0 :=
    Finset.sum_eq_zero (fun u _ => hS u)
  have hsum : ∑ w ∈ C, (∑ v : V × Bool, f w v) =
      splitValue S f + ∑ w ∈ C, (∑ u : V × Bool, f u w) := by
    have e1 := Finset.add_sum_erase C (fun w => ∑ v : V × Bool, f w v) hSC
    have e2 := Finset.add_sum_erase C (fun w => ∑ u : V × Bool, f u w) hSC
    unfold splitValue
    omega
  have hexpand_out : ∑ w ∈ C, (∑ v : V × Bool, f w v) =
      (∑ w ∈ C, ∑ v ∈ C, f w v) + (∑ u ∈ C, ∑ v ∈ Finset.univ \ C, f u v) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => hsplit_out w)
  have hexpand_in : ∑ w ∈ C, (∑ u : V × Bool, f u w) =
      (∑ w ∈ C, ∑ u ∈ C, f u w) + (∑ u ∈ C, ∑ v ∈ Finset.univ \ C, f v u) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => hsplit_in w)
  have hSS : (∑ w ∈ C, ∑ v ∈ C, f w v) = (∑ w ∈ C, ∑ u ∈ C, f u w) :=
    Finset.sum_comm
  omega

/-- Weak duality: flow value is at most any cut capacity. -/
private theorem split_weak_duality {V : Type*} [Fintype V] [DecidableEq V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (S T : V × Bool)
    (f : (V × Bool) → (V × Bool) → ℕ)
    (hf : IsSplitFlow cap S T f) (C : Finset (V × Bool))
    (hSC : S ∈ C) (hTC : T ∉ C) :
    splitValue S f ≤ splitCutCap cap C := by
  obtain ⟨hle, hcons, hS, _⟩ := hf
  have heq := split_cut_flow S T f hcons hS C hSC hTC
  have hle2 : (∑ u ∈ C, ∑ v ∈ Finset.univ \ C, f u v) ≤ splitCutCap cap C := by
    unfold splitCutCap
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact hle u v
  omega

/-- Every `ReflTransGen` path yields a chain list with the same endpoints. -/
private theorem reflTransGen_to_chain {W : Type*} (r : W → W → Prop) {a b : W}
    (h : Relation.ReflTransGen r a b) :
    ∃ l : List W, l.head? = some a ∧ l.getLast? = some b ∧ List.IsChain r l := by
  induction h using Relation.ReflTransGen.head_induction_on
  next => exact ⟨[b], rfl, by simp, List.isChain_singleton b⟩
  next a' c' hstep _ ih =>
    obtain ⟨l, hhead, hlast, hchain⟩ := ih
    match l, hhead, hlast, hchain with
    | [], hhead, _, _ =>
        simp only [List.head?_nil] at hhead
        exact absurd hhead (by simp)
    | y :: l, hhead, hlast, hchain =>
        refine ⟨a' :: y :: l, rfl, ?_, ?_⟩
        · rw [List.getLast?_cons_cons]
          exact hlast
        · rw [List.isChain_cons_cons]
          simp only [List.head?_cons] at hhead
          rw [← Option.some_inj.mp hhead] at hstep
          exact ⟨hstep, hchain⟩

/-- Every chain contains a nodup chain with the same endpoints and a subset
of vertices (strong induction on length). -/
private theorem chain_to_nodup_aux {W : Type*}
    (r : W → W → Prop) :
    ∀ (n : ℕ) (l : List W), l.length ≤ n →
    ∀ {a b : W}, l.head? = some a → l.getLast? = some b → List.IsChain r l →
    ∃ l' : List W, (∀ y ∈ l', y ∈ l) ∧ l'.head? = some a ∧
      l'.getLast? = some b ∧ List.IsChain r l' ∧ l'.Nodup := by
  classical
  intro n
  induction n with
  | zero =>
      intro l hlen a b hhead _ _
      have hempty : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hempty
      simp only [List.head?_nil] at hhead
      exact absurd hhead (by simp)
  | succ n ih =>
      intro l hlen a b hhead hlast hchain
      match l, hhead, hlast, hchain with
      | [], hhead, _, _ =>
          simp only [List.head?_nil] at hhead
          exact absurd hhead (by simp)
      | [x], hhead, hlast, hchain =>
          exact ⟨[x], fun _ h => h, hhead, hlast, hchain, List.nodup_singleton x⟩
      | x :: y :: t, hhead, hlast, hchain =>
          have hx : x = a := by
            simp only [List.head?_cons] at hhead
            exact Option.some_inj.mp hhead
          have hlast_t : (y :: t).getLast? = some b := by
            rw [List.getLast?_cons_cons] at hlast
            exact hlast
          have hchain_t : List.IsChain r (y :: t) := hchain.tail
          have hlen_lt : (y :: t).length ≤ n := by
            have e : (x :: y :: t).length = (y :: t).length + 1 := rfl
            omega
          by_cases hmem : x ∈ y :: t
          · obtain ⟨s, t', hsplit⟩ := List.mem_iff_append.mp hmem
            have hlen_splice : (x :: t').length ≤ n := by
              have e1 := congrArg List.length hsplit
              rw [List.length_append] at e1
              have e2 : (x :: y :: t).length = (y :: t).length + 1 := rfl
              have e3 : (x :: t').length = t'.length + 1 := rfl
              have e4 : (x :: t').length = t'.length + 1 := rfl
              omega
            have hhead_splice : (x :: t').head? = some a := by
              rw [hx]
              rfl
            have hlast_splice : (x :: t').getLast? = some b := by
              have e1 : (x :: y :: t).getLast? = (y :: t).getLast? := by
                rw [List.getLast?_cons_cons]
              have e2 : (y :: t).getLast? = (x :: t').getLast? := by
                rw [hsplit]
                exact List.getLast?_append_of_ne_nil s (by simp)
              rw [← e2, ← e1]
              exact hlast
            have hchain_xt' : List.IsChain r (x :: t') := by
              have hchain_s : List.IsChain r (s ++ x :: t') := by
                rw [← hsplit]
                exact hchain_t
              match t', hchain_s with
              | [], _ => exact List.isChain_singleton x
              | z :: t'', hchain_s =>
                  have hr : r x z := by
                    have h := (List.isChain_append_cons_cons.mp hchain_s).2.1
                    exact h
                  exact List.isChain_cons_cons.mpr
                    ⟨hr, (hchain_s.right_of_append.tail)⟩
            obtain ⟨l', hsub, hh', hl', hc', hn'⟩ :=
              ih (x :: t') hlen_splice hhead_splice hlast_splice hchain_xt'
            refine ⟨l', fun z hz => ?_, hh', hl', hc', hn'⟩
            have hzmem : z ∈ x :: t' := hsub z hz
            simp only [List.mem_cons] at hzmem
            rcases hzmem with rfl | hzmem
            · exact List.mem_cons_self
            · have : z ∈ y :: t := by
                rw [hsplit]
                exact List.mem_append_right s (List.mem_cons_of_mem x hzmem)
              exact List.mem_cons_of_mem x this
          · by_cases hnodup : (y :: t).Nodup
            · exact ⟨x :: y :: t, fun _ h => h, hhead, hlast, hchain,
                List.nodup_cons.mpr ⟨hmem, hnodup⟩⟩
            · have hhead_t : (y :: t).head? = some y := rfl
              obtain ⟨t'', hsub, hh'', hl'', hc'', hn''⟩ :=
                ih (y :: t) hlen_lt hhead_t hlast_t hchain_t
              have hxn't : x ∉ t'' := fun hcon => hmem (hsub x hcon)
              have hrxy : r x y := (List.isChain_cons_cons.mp hchain).1
              have hhead_new : (x :: t'').head? = some a := by
                rw [hx]
                rfl
              have hlast_new : (x :: t'').getLast? = some b := by
                match t'', hh'', hl'', hc'' with
                | [], hh'', _, _ =>
                    simp only [List.head?_nil] at hh''
                    exact absurd hh'' (by simp)
                | z :: t''', _, hl'', _ =>
                    rw [List.getLast?_cons_cons]
                    exact hl''
              have hchain_new : List.IsChain r (x :: t'') := by
                apply List.IsChain.cons hc''
                intro z hz
                rw [hh''] at hz
                have hzy : y = z := by simpa using hz
                rw [← hzy]
                exact hrxy
              refine ⟨x :: t'', fun z hz => ?_, hhead_new, hlast_new, hchain_new,
                List.nodup_cons.mpr ⟨hxn't, hn''⟩⟩
              simp only [List.mem_cons] at hz
              rcases hz with rfl | hz
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem x (hsub z hz)

/-- Reachability yields a nodup chain list with the same endpoints. -/
private theorem reflTransGen_to_nodup {W : Type*} (r : W → W → Prop) {a b : W}
    (h : Relation.ReflTransGen r a b) :
    ∃ l : List W, l.head? = some a ∧ l.getLast? = some b ∧ List.IsChain r l ∧
      l.Nodup := by
  obtain ⟨l, hhead, hlast, hchain⟩ := reflTransGen_to_chain r h
  obtain ⟨l', _, hh', hl', hc', hn'⟩ :=
    chain_to_nodup_aux r l.length l le_rfl hhead hlast hchain
  exact ⟨l', hh', hl', hc', hn'⟩

/-- Consecutive pair in a list, via indices. -/
private def isListStep {W : Type*} (l : List W) (a b : W) : Prop :=
  ∃ i : ℕ, ∃ hi : i < l.length, ∃ hi1 : i + 1 < l.length,
    l[i]'hi = a ∧ l[i + 1]'hi1 = b

/-- Steps start inside the list. -/
private theorem isListStep_mem_left {W : Type*} {l : List W} {a b : W}
    (h : isListStep l a b) : a ∈ l := by
  obtain ⟨i, hi, _, ha, _⟩ := h
  rw [← ha]
  simp

/-- Steps end inside the list. -/
private theorem isListStep_mem_right {W : Type*} {l : List W} {a b : W}
    (h : isListStep l a b) : b ∈ l := by
  obtain ⟨i, _, hi1, _, hb⟩ := h
  rw [← hb]
  simp

/-- Steps of a chain satisfy the relation. -/
private theorem isListStep_chain {W : Type*} {r : W → W → Prop} {l : List W}
    {a b : W} (hc : List.IsChain r l) (h : isListStep l a b) : r a b := by
  obtain ⟨i, hi, hi1, ha, hb⟩ := h
  have hrr : r l[i] l[i + 1] := hc.getElem i hi1
  rw [ha, hb] at hrr
  exact hrr

/-- Outgoing steps from a vertex of a nodup list are unique. -/
private theorem isListStep_unique_left {W : Type*} {l : List W} {a b₁ b₂ : W}
    (hn : l.Nodup) (h₁ : isListStep l a b₁) (h₂ : isListStep l a b₂) :
    b₁ = b₂ := by
  obtain ⟨i₁, hi₁, hi1₁, ha₁, hb₁⟩ := h₁
  obtain ⟨i₂, hi₂, hi1₂, ha₂, hb₂⟩ := h₂
  have heq : (l[i₁]'hi₁ : W) = l[i₂]'hi₂ := by rw [ha₁, ha₂]
  have hij : i₁ = i₂ := (hn.getElem_inj_iff).mp heq
  subst hij
  rw [← hb₁, ← hb₂]

/-- Incoming steps to a vertex of a nodup list are unique. -/
private theorem isListStep_unique_right {W : Type*} {l : List W} {a₁ a₂ b : W}
    (hn : l.Nodup) (h₁ : isListStep l a₁ b) (h₂ : isListStep l a₂ b) :
    a₁ = a₂ := by
  obtain ⟨i₁, hi₁, hi1₁, ha₁, hb₁⟩ := h₁
  obtain ⟨i₂, hi₂, hi1₂, ha₂, hb₂⟩ := h₂
  have heq : (l[i₁ + 1]'hi1₁ : W) = l[i₂ + 1]'hi1₂ := by rw [hb₁, hb₂]
  have hij : i₁ + 1 = i₂ + 1 := (hn.getElem_inj_iff).mp heq
  have hij' : i₁ = i₂ := Nat.succ_inj.mp hij
  subst hij'
  rw [← ha₁, ← ha₂]

/-- A nodup list never steps both ways between two vertices. -/
private theorem isListStep_not_rev {W : Type*} {l : List W} {a b : W}
    (hn : l.Nodup) (h₁ : isListStep l a b) (h₂ : isListStep l b a) : False := by
  obtain ⟨i, hi, hi1, ha, hb⟩ := h₁
  obtain ⟨j, hj, hj1, ha', hb'⟩ := h₂
  have e1 : (l[i]'hi : W) = l[j + 1]'hj1 := by rw [ha, hb']
  have e2 : (l[i + 1]'hi1 : W) = l[j]'hj := by rw [hb, ha']
  have f1 : i = j + 1 := (hn.getElem_inj_iff).mp e1
  have f2 : i + 1 = j := (hn.getElem_inj_iff).mp e2
  omega

/-- Steps of a nodup list never loop. -/
private theorem isListStep_irrefl {W : Type*} {l : List W} {a : W}
    (hn : l.Nodup) (h : isListStep l a a) : False :=
  isListStep_not_rev hn h h

/-- The head is the zeroth element. -/
private theorem head?_getElem_zero {W : Type*} {l : List W} {a : W}
    (hhead : l.head? = some a) (hlen : 0 < l.length) : l[0]'hlen = a := by
  match l, hhead with
  | [], hhead =>
      simp only [List.head?_nil] at hhead
      exact absurd hhead (by simp)
  | x :: xs, hhead =>
      simp only [List.head?_cons] at hhead
      have hx : x = a := Option.some_inj.mp hhead
      subst hx
      rfl

/-- The last element is at index `length - 1`. -/
private theorem getLast?_getElem_last {W : Type*} {l : List W} {b : W}
    (hlast : l.getLast? = some b) :
    ∃ h : l.length - 1 < l.length, l[l.length - 1]'h = b := by
  induction l with
  | nil =>
      simp only [List.getLast?_nil] at hlast
      exact absurd hlast (by simp)
  | cons x t ih =>
      match t, hlast with
      | [], hlast =>
          have hx : x = b := by simpa using hlast
          subst hx
          exact ⟨by simp, by simp⟩
      | y :: t', hlast =>
          rw [List.getLast?_cons_cons] at hlast
          obtain ⟨h, hh⟩ := ih hlast
          have hIdx : (x :: y :: t').length - 1 = ((y :: t').length - 1) + 1 := by
            simp
          rw [hIdx]
          refine ⟨?_, ?_⟩
          · have hM : 0 < (y :: t').length := by simp
            omega
          · exact hh

/-- Nothing steps into the head of a nodup list. -/
private theorem isListStep_not_to_head {W : Type*} {l : List W} {S v : W}
    (hhead : l.head? = some S) (hn : l.Nodup) : ¬ isListStep l v S := by
  have hlen : 0 < l.length := by
    match l, hhead with
    | [], hhead =>
        simp only [List.head?_nil] at hhead
        exact absurd hhead (by simp)
    | _ :: _, _ => exact Nat.zero_lt_succ _
  intro hstep
  obtain ⟨i, _, hi1, _, hb⟩ := hstep
  have hS0 : l[0]'hlen = S := head?_getElem_zero hhead hlen
  have heq : (l[i + 1]'hi1 : W) = l[0]'hlen := by rw [hb, hS0]
  have : i + 1 = 0 := (hn.getElem_inj_iff).mp heq
  omega

/-- Nothing steps out of the last element of a nodup list. -/
private theorem isListStep_not_from_last {W : Type*} {l : List W} {T v : W}
    (hlast : l.getLast? = some T) (hn : l.Nodup) : ¬ isListStep l T v := by
  obtain ⟨hlast_idx, hTlast⟩ := getLast?_getElem_last hlast
  intro hstep
  obtain ⟨i, hi, hi1, ha, _⟩ := hstep
  have heq : (l[i]'hi : W) = l[l.length - 1]'hlast_idx := by rw [ha, hTlast]
  have : i = l.length - 1 := (hn.getElem_inj_iff).mp heq
  omega

/-- Membership yields an index. -/
private theorem mem_getElem_idx {W : Type*} {l : List W} {x : W} (h : x ∈ l) :
    ∃ i : ℕ, ∃ hi : i < l.length, l[i]'hi = x := by
  induction l with
  | nil => simp at h
  | cons y t ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨i, hi, hEq⟩ := ih h
        refine ⟨i + 1, by simp; omega, ?_⟩
        have : ((y :: t)[i + 1]'(by simp; omega) : W) = t[i]'hi := rfl
        rw [this]
        exact hEq

/-- Two functions agreeing except at two points have related sums. -/
private theorem sum_two_diff {W : Type*} [Fintype W]
    (g h : W → ℕ) {p q : W} (hpq : p ≠ q)
    (hothers : ∀ v, v ≠ p → v ≠ q → g v = h v) :
    (∑ v, g v) + h p + h q = (∑ v, h v) + g p + g q := by
  classical
  have hp_mem : p ∈ (Finset.univ : Finset W) := Finset.mem_univ p
  have hq_mem : q ∈ (Finset.univ : Finset W) := Finset.mem_univ q
  have hq_erase : q ∈ (Finset.univ : Finset W).erase p :=
    Finset.mem_erase.mpr ⟨Ne.symm hpq, hq_mem⟩
  have e1 := Finset.add_sum_erase Finset.univ g hp_mem
  have e2 := Finset.add_sum_erase _ g hq_erase
  have e3 := Finset.add_sum_erase Finset.univ h hp_mem
  have e4 := Finset.add_sum_erase _ h hq_erase
  have erest : ∑ v ∈ (Finset.univ.erase p).erase q, g v =
      ∑ v ∈ (Finset.univ.erase p).erase q, h v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_erase, Finset.mem_erase] at hv
    exact hothers v hv.2.1 hv.1
  omega

/-- Residual relation: forward along unsaturated arcs, backward along used arcs. -/
private def splitResid {V : Type*} (cap : (V × Bool) → (V × Bool) → ℕ)
    (f : (V × Bool) → (V × Bool) → ℕ) : (V × Bool) → (V × Bool) → Prop :=
  fun a b => f a b < cap a b ∨ 0 < f b a

private noncomputable instance decIsListStep {W : Type*} (l : List W) (a b : W) :
    Decidable (isListStep l a b) :=
  Classical.propDecidable _

/-- Augmented flow along a residual path: increment forward steps, decrement
backward steps (preferring forward when both apply). -/
private noncomputable def splitAugment {V : Type*}
    (cap : (V × Bool) → (V × Bool) → ℕ)
    (l : List (V × Bool)) (f : (V × Bool) → (V × Bool) → ℕ) :
    (V × Bool) → (V × Bool) → ℕ :=
  fun a b =>
    f a b
      + (if isListStep l a b ∧ f a b < cap a b then 1 else 0)
      - (if isListStep l b a ∧ ¬ f b a < cap b a then 1 else 0)

/-- Augmenting along a nodup residual path strictly increases flow value. -/
private theorem split_augment {V : Type*} [Fintype V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (S T : V × Bool) (hST : S ≠ T)
    (f : (V × Bool) → (V × Bool) → ℕ) (hf : IsSplitFlow cap S T f)
    (l : List (V × Bool)) (hhead : l.head? = some S) (hlast : l.getLast? = some T)
    (hchain : List.IsChain (splitResid cap f) l) (hn : l.Nodup) :
    ∃ f' : (V × Bool) → (V × Bool) → ℕ,
      IsSplitFlow cap S T f' ∧ splitValue S f + 1 = splitValue S f' := by
  classical
  obtain ⟨hle, hcons, hSin, hTout⟩ := hf
  have hR : ∀ a b, isListStep l a b → f a b < cap a b ∨ 0 < f b a := by
    intro a b hstep
    have h := isListStep_chain hchain hstep
    exact h
  have hlen2 : 2 ≤ l.length := by
    match l, hhead, hlast with
    | [], hhead, _ =>
        simp only [List.head?_nil] at hhead
        exact absurd hhead (by simp)
    | [x], hhead, hlast =>
        have hxS : x = S := by simpa using hhead
        have hxT : x = T := by simpa using hlast
        exact absurd (hxS.symm.trans hxT) hST
    | x :: y :: t, _, _ =>
        have : (x :: y :: t).length = t.length + 2 := rfl
        omega
  have hlen_pos : 0 < l.length := by omega
  have hS0 : l[0]'hlen_pos = S := head?_getElem_zero hhead hlen_pos
  obtain ⟨hlast_idx, hTlast⟩ := getLast?_getElem_last hlast
  have h1lt : 1 < l.length := by omega
  have h01 : 0 + 1 < l.length := by omega
  have hstep0 : isListStep l S (l[1]'h1lt) := ⟨0, hlen_pos, h01, hS0, rfl⟩
  have hfwd0 : f S (l[1]'h1lt) < cap S (l[1]'h1lt) := by
    rcases hR S _ hstep0 with h | h
    · exact h
    · have hz : f (l[1]'h1lt) S = 0 := hSin _
      omega
  set f' : (V × Bool) → (V × Bool) → ℕ := splitAugment cap l f with hf'def
  have hf'_fwd : ∀ a b, (isListStep l a b ∧ f a b < cap a b) →
      ¬ (isListStep l b a ∧ ¬ f b a < cap b a) → f' a b = f a b + 1 := by
    intro a b hfwd hbwd
    simp only [hf'def, splitAugment, ite_eq_left hfwd, ite_eq_right hbwd, Nat.sub_zero]
  have hf'_bwd : ∀ a b, ¬ (isListStep l a b ∧ f a b < cap a b) →
      (isListStep l b a ∧ ¬ f b a < cap b a) → f' a b = f a b - 1 := by
    intro a b hfwd hbwd
    simp only [hf'def, splitAugment, ite_eq_right hfwd, ite_eq_left hbwd, Nat.add_zero]
  have hf'_same : ∀ a b, ¬ (isListStep l a b ∧ f a b < cap a b) →
      ¬ (isListStep l b a ∧ ¬ f b a < cap b a) → f' a b = f a b := by
    intro a b hfwd hbwd
    simp only [hf'def, splitAugment, ite_eq_right hfwd, ite_eq_right hbwd, Nat.add_zero,
      Nat.sub_zero]
  have hexcl : ∀ a b, (isListStep l a b ∧ f a b < cap a b) →
      ¬ (isListStep l b a ∧ ¬ f b a < cap b a) := by
    intro a b hfwd hbwd
    exact isListStep_not_rev hn hfwd.1 hbwd.1
  have hexcl' : ∀ a b, (isListStep l b a ∧ ¬ f b a < cap b a) →
      ¬ (isListStep l a b ∧ f a b < cap a b) := by
    intro a b hbwd hfwd
    exact isListStep_not_rev hn hfwd.1 hbwd.1
  have hbwd_pos : ∀ a b, (isListStep l b a ∧ ¬ f b a < cap b a) → 0 < f a b := by
    intro a b hbwd
    rcases hR b a hbwd.1 with h | h
    · exact absurd h hbwd.2
    · exact h
  have hcap' : ∀ a b, f' a b ≤ cap a b := by
    intro a b
    by_cases hfwd : isListStep l a b ∧ f a b < cap a b
    · rw [hf'_fwd a b hfwd (hexcl a b hfwd)]
      have h1 := hfwd.2
      omega
    · by_cases hbwd : isListStep l b a ∧ ¬ f b a < cap b a
      · rw [hf'_bwd a b hfwd hbwd]
        have h1 := hle a b
        omega
      · rw [hf'_same a b hfwd hbwd]
        exact hle a b
  have hcons' : ∀ x, x ≠ S → x ≠ T →
      (∑ u, f' u x) = ∑ v, f' x v := by
    intro x hxS hxT
    by_cases hxmem : x ∈ l
    · obtain ⟨j, hj, hjEq⟩ := mem_getElem_idx hxmem
      have hj0 : j ≠ 0 := by
        intro hcon
        subst hcon
        exact hxS (hjEq.symm.trans hS0)
      have hjlast : j ≠ l.length - 1 := by
        intro hcon
        subst hcon
        exact hxT (hjEq.symm.trans hTlast)
      have hj1 : j + 1 < l.length := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hk : k < l.length := by omega
      have hkin : isListStep l (l[k]'hk) x := ⟨k, hk, hj, rfl, hjEq⟩
      have hkout : isListStep l x (l[k + 1 + 1]'hj1) := ⟨k + 1, hj, hj1, hjEq, rfl⟩
      have hps : l[k]'hk ≠ l[k + 1 + 1]'hj1 := by
        intro hcon
        have : k = k + 1 + 1 := (hn.getElem_inj_iff).mp hcon
        omega
      have hno_out : ∀ v, v ≠ l[k + 1 + 1]'hj1 → ¬ isListStep l x v := by
        intro v hv hstep
        have : v = l[k + 1 + 1]'hj1 :=
          isListStep_unique_left hn hstep hkout
        exact hv this
      have hno_in : ∀ v, v ≠ l[k]'hk → ¬ isListStep l v x := by
        intro v hv hstep
        have : v = l[k]'hk := isListStep_unique_right hn hstep hkin
        exact hv this
      have hrow_other : ∀ v, v ≠ l[k + 1 + 1]'hj1 → v ≠ l[k]'hk →
          f' x v = f x v := by
        intro v hv1 hv2
        apply hf'_same
        · intro hcon
          exact hno_out v hv1 hcon.1
        · intro hcon
          exact hno_in v hv2 hcon.1
      have hcol_other : ∀ u, u ≠ l[k]'hk → u ≠ l[k + 1 + 1]'hj1 →
          f' u x = f u x := by
        intro u hu1 hu2
        apply hf'_same
        · intro hcon
          exact hno_in u hu1 hcon.1
        · intro hcon
          exact hno_out u hu2 hcon.1
      have hrow_eq := sum_two_diff (fun v => f' x v) (fun v => f x v)
        (Ne.symm hps) hrow_other
      have hcol_eq := sum_two_diff (fun u => f' u x) (fun u => f u x)
        hps hcol_other
      have hcon0 := hcons x hxS hxT
      by_cases hout : f x (l[k + 1 + 1]'hj1) < cap x (l[k + 1 + 1]'hj1)
      · by_cases hin : f (l[k]'hk) x < cap (l[k]'hk) x
        · have e1 : f' x (l[k + 1 + 1]'hj1) = f x (l[k + 1 + 1]'hj1) + 1 :=
            hf'_fwd _ _ ⟨hkout, hout⟩ (hexcl _ _ ⟨hkout, hout⟩)
          have e2 : f' x (l[k]'hk) = f x (l[k]'hk) := by
            apply hf'_same
            · intro hcon
              exact hno_out _ hps hcon.1
            · intro hcon
              exact hcon.2 hin
          have e3 : f' (l[k]'hk) x = f (l[k]'hk) x + 1 :=
            hf'_fwd _ _ ⟨hkin, hin⟩ (hexcl _ _ ⟨hkin, hin⟩)
          have e4 : f' (l[k + 1 + 1]'hj1) x = f (l[k + 1 + 1]'hj1) x := by
            apply hf'_same
            · intro hcon
              exact hno_in _ (Ne.symm hps) hcon.1
            · intro hcon
              exact hcon.2 hout
          omega
        · have e1 : f' x (l[k + 1 + 1]'hj1) = f x (l[k + 1 + 1]'hj1) + 1 :=
            hf'_fwd _ _ ⟨hkout, hout⟩ (hexcl _ _ ⟨hkout, hout⟩)
          have e2 : f' x (l[k]'hk) + 1 = f x (l[k]'hk) := by
            have hpos := hbwd_pos _ _ (⟨hkin, hin⟩ :
              isListStep l (l[k]'hk) x ∧ ¬ f (l[k]'hk) x < cap (l[k]'hk) x)
            have heq := hf'_bwd _ _ (fun hcon => hno_out _ hps hcon.1)
              (⟨hkin, hin⟩ :
                isListStep l (l[k]'hk) x ∧ ¬ f (l[k]'hk) x < cap (l[k]'hk) x)
            omega
          have e3 : f' (l[k]'hk) x = f (l[k]'hk) x := by
            apply hf'_same
            · intro hcon
              exact hin hcon.2
            · intro hcon
              exact hno_out _ hps hcon.1
          have e4 : f' (l[k + 1 + 1]'hj1) x = f (l[k + 1 + 1]'hj1) x := by
            apply hf'_same
            · intro hcon
              exact hno_in _ (Ne.symm hps) hcon.1
            · intro hcon
              exact hcon.2 hout
          omega
      · by_cases hin : f (l[k]'hk) x < cap (l[k]'hk) x
        · have e1 : f' x (l[k + 1 + 1]'hj1) = f x (l[k + 1 + 1]'hj1) := by
            apply hf'_same
            · intro hcon
              exact hout hcon.2
            · intro hcon
              exact hno_in _ (Ne.symm hps) hcon.1
          have e2 : f' x (l[k]'hk) = f x (l[k]'hk) := by
            apply hf'_same
            · intro hcon
              exact hno_out _ hps hcon.1
            · intro hcon
              exact hcon.2 hin
          have e3 : f' (l[k]'hk) x = f (l[k]'hk) x + 1 :=
            hf'_fwd _ _ ⟨hkin, hin⟩ (hexcl _ _ ⟨hkin, hin⟩)
          have e4 : f' (l[k + 1 + 1]'hj1) x + 1 = f (l[k + 1 + 1]'hj1) x := by
            have hpos := hbwd_pos _ _ (⟨hkout, hout⟩ :
              isListStep l x (l[k + 1 + 1]'hj1) ∧
                ¬ f x (l[k + 1 + 1]'hj1) < cap x (l[k + 1 + 1]'hj1))
            have heq := hf'_bwd _ _ (fun hcon => hno_in _ (Ne.symm hps) hcon.1)
              (⟨hkout, hout⟩ :
                isListStep l x (l[k + 1 + 1]'hj1) ∧
                  ¬ f x (l[k + 1 + 1]'hj1) < cap x (l[k + 1 + 1]'hj1))
            omega
          omega
        · have e1 : f' x (l[k + 1 + 1]'hj1) = f x (l[k + 1 + 1]'hj1) := by
            apply hf'_same
            · intro hcon
              exact hout hcon.2
            · intro hcon
              exact hno_in _ (Ne.symm hps) hcon.1
          have e2 : f' x (l[k]'hk) + 1 = f x (l[k]'hk) := by
            have hpos := hbwd_pos _ _ (⟨hkin, hin⟩ :
              isListStep l (l[k]'hk) x ∧ ¬ f (l[k]'hk) x < cap (l[k]'hk) x)
            have heq := hf'_bwd _ _ (fun hcon => hno_out _ hps hcon.1)
              (⟨hkin, hin⟩ :
                isListStep l (l[k]'hk) x ∧ ¬ f (l[k]'hk) x < cap (l[k]'hk) x)
            omega
          have e3 : f' (l[k]'hk) x = f (l[k]'hk) x := by
            apply hf'_same
            · intro hcon
              exact hin hcon.2
            · intro hcon
              exact hno_out _ hps hcon.1
          have e4 : f' (l[k + 1 + 1]'hj1) x + 1 = f (l[k + 1 + 1]'hj1) x := by
            have hpos := hbwd_pos _ _ (⟨hkout, hout⟩ :
              isListStep l x (l[k + 1 + 1]'hj1) ∧
                ¬ f x (l[k + 1 + 1]'hj1) < cap x (l[k + 1 + 1]'hj1))
            have heq := hf'_bwd _ _ (fun hcon => hno_in _ (Ne.symm hps) hcon.1)
              (⟨hkout, hout⟩ :
                isListStep l x (l[k + 1 + 1]'hj1) ∧
                  ¬ f x (l[k + 1 + 1]'hj1) < cap x (l[k + 1 + 1]'hj1))
            omega
          omega
    · have hrow : ∀ v, f' x v = f x v := by
        intro v
        apply hf'_same
        · intro hcon
          exact hxmem (isListStep_mem_left hcon.1)
        · intro hcon
          exact hxmem (isListStep_mem_right hcon.1)
      have hcol : ∀ u, f' u x = f u x := by
        intro u
        apply hf'_same
        · intro hcon
          exact hxmem (isListStep_mem_right hcon.1)
        · intro hcon
          exact hxmem (isListStep_mem_left hcon.1)
      rw [Finset.sum_congr rfl (fun u _ => hcol u),
        Finset.sum_congr rfl (fun v _ => hrow v)]
      exact hcons x hxS hxT
  have hSin' : ∀ v, f' v S = 0 := by
    intro v
    have hnofwd : ¬ (isListStep l v S ∧ f v S < cap v S) := by
      intro hcon
      exact isListStep_not_to_head hhead hn hcon.1
    by_cases hbwd : isListStep l S v ∧ ¬ f S v < cap S v
    · rw [hf'_bwd v S hnofwd hbwd]
      have hz : f v S = 0 := hSin v
      omega
    · rw [hf'_same v S hnofwd hbwd]
      exact hSin v
  have hTout' : ∀ v, f' T v = 0 := by
    intro v
    have hnofwd : ¬ (isListStep l T v ∧ f T v < cap T v) := by
      intro hcon
      exact isListStep_not_from_last hlast hn hcon.1
    by_cases hbwd : isListStep l v T ∧ ¬ f v T < cap v T
    · rw [hf'_bwd T v hnofwd hbwd]
      have hz : f T v = 0 := hTout v
      omega
    · rw [hf'_same T v hnofwd hbwd]
      exact hTout v
  have hval : splitValue S f + 1 = splitValue S f' := by
    have hrowS : ∀ v, v ≠ l[1]'h1lt → f' S v = f S v := by
      intro v hv
      apply hf'_same
      · intro hcon
        have : v = l[1]'h1lt := isListStep_unique_left hn hcon.1 hstep0
        exact hv this
      · intro hcon
        exact isListStep_not_to_head hhead hn hcon.1
    have hsucc : f' S (l[1]'h1lt) = f S (l[1]'h1lt) + 1 :=
      hf'_fwd _ _ ⟨hstep0, hfwd0⟩ (hexcl _ _ ⟨hstep0, hfwd0⟩)
    have hmem : l[1]'h1lt ∈ (Finset.univ : Finset (V × Bool)) := Finset.mem_univ _
    have e1 := Finset.add_sum_erase Finset.univ (fun v => f' S v) hmem
    have e2 := Finset.add_sum_erase Finset.univ (fun v => f S v) hmem
    have erest : ∑ v ∈ Finset.univ.erase (l[1]'h1lt), f' S v =
        ∑ v ∈ Finset.univ.erase (l[1]'h1lt), f S v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mem_erase] at hv
      exact hrowS v hv.1
    unfold splitValue
    omega
  exact ⟨f', ⟨hcap', hcons', hSin', hTout'⟩, hval⟩

/-- A value-maximal feasible flow exists, with no residual `S`-`T` path. -/
private theorem split_max_flow {V : Type*} [Fintype V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (S T : V × Bool) (hST : S ≠ T) :
    ∃ f : (V × Bool) → (V × Bool) → ℕ, IsSplitFlow cap S T f ∧
      (∀ f' : (V × Bool) → (V × Bool) → ℕ,
        IsSplitFlow cap S T f' → splitValue S f' ≤ splitValue S f) ∧
      ¬ Relation.ReflTransGen (splitResid cap f) S T := by
  classical
  have hTnotS : T ∉ ({S} : Finset (V × Bool)) := by
    simp only [Finset.mem_singleton]
    exact Ne.symm hST
  set bound := splitCutCap cap {S} with hbound
  have hbdd : ∀ f', IsSplitFlow cap S T f' → splitValue S f' ≤ bound := by
    intro f' hf'
    exact split_weak_duality cap S T f' hf' {S}
      (Finset.mem_singleton_self S) hTnotS
  let Ach : Set ℕ := {k | ∃ f, IsSplitFlow cap S T f ∧ splitValue S f = k}
  have h0 : (0 : ℕ) ∈ Ach := by
    refine ⟨fun _ _ => 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro a b
      exact Nat.zero_le _
    · intro w _ _
      simp
    · intro v
      rfl
    · intro v
      rfl
    · simp [splitValue]
  have hbddAch : Ach ⊆ ↑(Finset.range (bound + 1)) := by
    intro k hk
    obtain ⟨f', hf', hval⟩ := hk
    rw [Finset.mem_coe, Finset.mem_range]
    have hle := hbdd f' hf'
    omega
  have hfin : Ach.Finite := Set.Finite.subset (Finset.finite_toSet _) hbddAch
  have hne : hfin.toFinset.Nonempty := ⟨0, hfin.mem_toFinset.mpr h0⟩
  have hmem : hfin.toFinset.max' hne ∈ Ach :=
    hfin.mem_toFinset.mp (Finset.max'_mem _ hne)
  obtain ⟨f, hf, hval⟩ := hmem
  refine ⟨f, hf, ?_, ?_⟩
  · intro f' hf'
    have hmem' : splitValue S f' ∈ Ach := ⟨f', hf', rfl⟩
    have hle := Finset.le_max' _ _ (hfin.mem_toFinset.mpr hmem')
    rw [hval]
    exact hle
  · intro hreach
    obtain ⟨l, hhead, hlast, hchain, hn⟩ := reflTransGen_to_nodup _ hreach
    obtain ⟨f', hf', hval'⟩ :=
      split_augment cap S T hST f hf l hhead hlast hchain hn
    have hle := Finset.le_max' _ _
      (hfin.mem_toFinset.mpr (⟨f', hf', rfl⟩ : splitValue S f' ∈ Ach))
    omega

/-- The residual-reachable set is a minimum cut. -/
private theorem split_mincut {V : Type*} [Fintype V] [DecidableEq V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (S T : V × Bool)
    (f : (V × Bool) → (V × Bool) → ℕ) (hf : IsSplitFlow cap S T f)
    (hmax : ¬ Relation.ReflTransGen (splitResid cap f) S T) :
    ∃ C : Finset (V × Bool), S ∈ C ∧ T ∉ C ∧
      splitValue S f = splitCutCap cap C := by
  classical
  obtain ⟨hle, hcons, hSin, _⟩ := hf
  set R : Finset (V × Bool) :=
    Finset.univ.filter (fun w => Relation.ReflTransGen (splitResid cap f) S w)
    with hRdef
  have hSR : S ∈ R := by
    simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  have hTR : T ∉ R := by
    simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmax
  have hsat : ∀ u ∈ R, ∀ v ∈ Finset.univ \ R, f u v = cap u v ∧ f v u = 0 := by
    intro u hu v hv
    have huR : Relation.ReflTransGen (splitResid cap f) S u := by
      simpa only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and] using hu
    have hmem : v ∈ R → False := by
      intro hcon
      exact (Finset.mem_sdiff.mp hv).2 hcon
    constructor
    · by_contra hcon
      have h1 := hle u v
      have hlt : f u v < cap u v := by omega
      have hRuv : splitResid cap f u v := Or.inl hlt
      have hRv : Relation.ReflTransGen (splitResid cap f) S v := huR.tail hRuv
      have : v ∈ R := by
        simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hRv
      exact hmem this
    · by_contra hcon
      have hpos : 0 < f v u := by omega
      have hRuv : splitResid cap f u v := Or.inr hpos
      have hRv : Relation.ReflTransGen (splitResid cap f) S v := huR.tail hRuv
      have : v ∈ R := by
        simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hRv
      exact hmem this
  have heq : splitValue S f = splitCutCap cap R := by
    have hcf := split_cut_flow S T f hcons hSin R hSR hTR
    have hfwd : (∑ u ∈ R, ∑ v ∈ Finset.univ \ R, f u v) = splitCutCap cap R := by
      unfold splitCutCap
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      exact (hsat u hu v hv).1
    have hbwd : (∑ u ∈ R, ∑ v ∈ Finset.univ \ R, f v u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      exact (hsat u hu v hv).2
    omega
  exact ⟨R, hSR, hTR, heq⟩

/-- An adjacency chain lifts to a positive-capacity chain in the split network,
using only vertices of the original chain. -/
private theorem chain_to_split {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ)
    (hbig : 0 < big) (l : List V) (hc : List.IsChain G.Adj l)
    {a b : V} (hhead : l.head? = some a) (hlast : l.getLast? = some b) :
    ∃ L : List (V × Bool), L.head? = some (a, false) ∧ L.getLast? = some (b, true) ∧
      List.IsChain (fun x y => 0 < splitCap G s t big x y) L ∧
      (∀ w ∈ L, w.1 ∈ l) := by
  suffices h : ∀ (n : ℕ) (l : List V), l.length ≤ n → ∀ {a b : V},
      l.head? = some a → l.getLast? = some b → List.IsChain G.Adj l →
      ∃ L : List (V × Bool), L.head? = some (a, false) ∧
        L.getLast? = some (b, true) ∧
        List.IsChain (fun x y => 0 < splitCap G s t big x y) L ∧
        (∀ w ∈ L, w.1 ∈ l) by
    exact h l.length l le_rfl hhead hlast hc
  intro n
  induction n with
  | zero =>
      intro l hlen a b hhead hlast hc
      have hempty : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hempty
      simp only [List.head?_nil] at hhead
      exact absurd hhead (by simp)
  | succ n ih =>
      intro l hlen a b hhead hlast hc
      match l, hlen, hhead, hlast, hc with
      | [], _, hhead, _, _ =>
          simp only [List.head?_nil] at hhead
          exact absurd hhead (by simp)
      | [x], _, hhead, hlast, _ =>
          have hxa : x = a := by simpa using hhead
          have hxb : x = b := by simpa using hlast
          subst hxa
          subst hxb
          refine ⟨[(x, false), (x, true)], rfl, by simp, ?_, ?_⟩
          · rw [List.isChain_pair]
            rw [splitCap_self]
            by_cases h : x = s ∨ x = t
            · rw [ite_eq_left h]
              exact hbig
            · rw [ite_eq_right h]
              exact Nat.zero_lt_one
          · intro w hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl | rfl <;> simp
      | x :: y :: t', hlen, hhead, hlast, hc =>
          have hxa : x = a := by simpa using hhead
          subst hxa
          have hadj : G.Adj x y := (List.isChain_cons_cons.mp hc).1
          have hc_t : List.IsChain G.Adj (y :: t') := hc.tail
          have hhead_t : (y :: t').head? = some y := rfl
          have hlast_t : (y :: t').getLast? = some b := by
            rw [List.getLast?_cons_cons] at hlast
            exact hlast
          have hlen_t : (y :: t').length ≤ n := by
            have e : (x :: y :: t').length = (y :: t').length + 1 := rfl
            omega
          obtain ⟨L', hh', hl', hc', hsub'⟩ := ih (y :: t') hlen_t hhead_t hlast_t hc_t
          match L', hh', hl', hc' with
          | [], hh', _, _ =>
              simp only [List.head?_nil] at hh'
              exact absurd hh' (by simp)
          | z :: L'', hh', hl', hc' =>
              have hz : z = (y, false) := by
                simp only [List.head?_cons] at hh'
                exact Option.some_inj.mp hh'
              subst hz
              refine ⟨(x, false) :: (x, true) :: (y, false) :: L'', rfl, ?_, ?_, ?_⟩
              · rw [List.getLast?_cons_cons, List.getLast?_cons_cons]
                exact hl'
              · rw [List.isChain_cons_cons]
                constructor
                · rw [splitCap_self]
                  by_cases h : x = s ∨ x = t
                  · rw [ite_eq_left h]
                    exact hbig
                  · rw [ite_eq_right h]
                    exact Nat.zero_lt_one
                · rw [List.isChain_cons_cons]
                  constructor
                  · rw [splitCap_edge G s t big hadj]
                    exact hbig
                  · exact hc'
              · intro w hw
                simp only [List.mem_cons] at hw
                rcases hw with rfl | rfl | rfl | hw
                · simp
                · simp
                · exact List.mem_cons_of_mem x (by simp : (y, false).1 ∈ y :: t')
                · exact List.mem_cons_of_mem x
                    (hsub' w (List.mem_cons_of_mem _ hw))

/-- A chain from inside a cut to outside uses a leaving step. -/
private theorem chain_leaving_step {W : Type*} (r : W → W → Prop)
    (C : Finset W) (l : List W) (hc : List.IsChain r l) {a b : W}
    (hhead : l.head? = some a) (hlast : l.getLast? = some b)
    (ha : a ∈ C) (hb : b ∉ C) :
    ∃ x y, isListStep l x y ∧ x ∈ C ∧ y ∉ C ∧ r x y := by
  classical
  suffices h : ∀ (n : ℕ) (l : List W), l.length ≤ n → ∀ {a b : W},
      List.IsChain r l → l.head? = some a → l.getLast? = some b →
      a ∈ C → b ∉ C → ∃ x y, isListStep l x y ∧ x ∈ C ∧ y ∉ C ∧ r x y by
    exact h l.length l le_rfl hc hhead hlast ha hb
  intro n
  induction n with
  | zero =>
      intro l hlen a b hc hhead hlast ha hb
      have hempty : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hempty
      simp only [List.head?_nil] at hhead
      exact absurd hhead (by simp)
  | succ n ih =>
      intro l hlen a b hc hhead hlast ha hb
      match l, hlen, hc, hhead, hlast, ha, hb with
      | [], _, _, hhead, _, _, _ =>
          simp only [List.head?_nil] at hhead
          exact absurd hhead (by simp)
      | [x], _, _, hhead, hlast, ha, hb =>
          have hxa : x = a := by simpa using hhead
          have hxb : x = b := by simpa using hlast
          subst hxa
          subst hxb
          exact absurd ha hb
      | x :: y :: t, hlen, hc, hhead, hlast, ha, hb =>
          have hxa : x = a := by simpa using hhead
          subst hxa
          by_cases hy : y ∈ C
          · have hc_t := hc.tail
            have hhead_t : (y :: t).head? = some y := rfl
            have hlast_t : (y :: t).getLast? = some b := by
              rw [List.getLast?_cons_cons] at hlast
              exact hlast
            have hlen_t : (y :: t).length ≤ n := by
              have e : (x :: y :: t).length = (y :: t).length + 1 := rfl
              omega
            obtain ⟨u, v, hstep, huC, hvC, hrv⟩ :=
              ih (y :: t) hlen_t hc_t hhead_t hlast_t hy hb
            obtain ⟨i, hi, hi1, ha', hb'⟩ := hstep
            have e : (x :: y :: t).length = (y :: t).length + 1 := rfl
            have hi1' : i + 1 < (x :: y :: t).length := by omega
            have hi2 : i + 1 + 1 < (x :: y :: t).length := by omega
            refine ⟨u, v, ⟨i + 1, hi1', hi2, ?_, ?_⟩, huC, hvC, hrv⟩
            · have : ((x :: y :: t)[i + 1]'hi1' : W) = (y :: t)[i]'hi := rfl
              rw [this]
              exact ha'
            · have : ((x :: y :: t)[i + 1 + 1]'hi2 : W) = (y :: t)[i + 1]'hi1 := rfl
              rw [this]
              exact hb'
          · have e : (x :: y :: t).length = t.length + 2 := rfl
            have hlen0 : 0 < (x :: y :: t).length := by omega
            have h1lt : 1 < (x :: y :: t).length := by omega
            have h01 : 0 + 1 < (x :: y :: t).length := by omega
            have hx0 : (x :: y :: t)[0]'hlen0 = x := rfl
            have hy1 : (x :: y :: t)[1]'h1lt = y := rfl
            have hstep : isListStep (x :: y :: t) x y :=
              ⟨0, hlen0, h01, hx0, hy1⟩
            have hrxy : r x y := (List.isChain_cons_cons.mp hc).1
            exact ⟨x, y, hstep, ha, hy, hrxy⟩

/-- A split-network cut yields a separator no larger than its capacity. -/
private theorem cut_to_separator {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (hne : s ≠ t)
    (hnadj : ¬ G.Adj s t)
    (R : Finset (V × Bool)) (hSR : (s, false) ∈ R) (hTR : (t, true) ∉ R) :
    ∃ C : Finset V, s ∉ C ∧ t ∉ C ∧
      (∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C) ∧
      C.card ≤ splitCutCap (splitCap G s t (Fintype.card V)) R := by
  classical
  set big := Fintype.card V with hbigdef
  set cap := splitCap G s t big with hcapdef
  have hcard2 : 2 ≤ Fintype.card V := by
    have hst : ({s, t} : Finset V).card = 2 := Finset.card_pair hne
    have hle : ({s, t} : Finset V).card ≤ Fintype.card V := by
      calc ({s, t} : Finset V).card ≤ Finset.univ.card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card V := Finset.card_univ
    omega
  have hbig : 0 < big := by omega
  set C : Finset V := Finset.univ.filter
    (fun v => v ≠ s ∧ v ≠ t ∧ (v, false) ∈ R ∧ (v, true) ∉ R) with hCdef
  have hCmem : ∀ v, v ∈ C ↔ v ≠ s ∧ v ≠ t ∧ (v, false) ∈ R ∧ (v, true) ∉ R := by
    intro v
    simp only [hCdef, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsC : s ∉ C := by
    intro hcon
    obtain ⟨h1, _, _, _⟩ := (hCmem s).mp hcon
    exact h1 rfl
  have htC : t ∉ C := by
    intro hcon
    obtain ⟨_, h2, _, _⟩ := (hCmem t).mp hcon
    exact h2 rfl
  have hcap1 : ∀ v ∈ C, cap (v, false) (v, true) = 1 := by
    intro v hv
    obtain ⟨hvs, hvt, _, _⟩ := (hCmem v).mp hv
    have hne_st : ¬ (v = s ∨ v = t) := fun h => h.elim hvs hvt
    rw [hcapdef, splitCap_self, ite_eq_right hne_st]
  have hcard_le : C.card ≤ splitCutCap cap R := by
    have himg_sub : C.image (fun v => (v, false)) ⊆ R := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ((hCmem v).mp hv).2.2.1
    have hsum1 : (∑ u ∈ C.image (fun v => (v, false)),
          ∑ w ∈ Finset.univ \ R, cap u w) ≤ splitCutCap cap R := by
      unfold splitCutCap
      apply Finset.sum_le_sum_of_subset_of_nonneg himg_sub
      intro u _ _
      exact Nat.zero_le _
    have hsum2 : ∀ u ∈ C.image (fun v => (v, false)),
        1 ≤ ∑ w ∈ Finset.univ \ R, cap u w := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      have hmem : (v, true) ∈ Finset.univ \ R :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ((hCmem v).mp hv).2.2.2⟩
      have hle : cap (v, false) (v, true) ≤
          ∑ w ∈ Finset.univ \ R, cap (v, false) w :=
        Finset.single_le_sum (fun w _ => Nat.zero_le _) hmem
      rw [hcap1 v hv] at hle
      exact hle
    have hinj : Set.InjOn (fun v => (v, false)) (C : Set V) := by
      intro x _ y _ hxy
      simpa using hxy
    have hsum3 : C.card ≤ ∑ u ∈ C.image (fun v => (v, false)),
        ∑ w ∈ Finset.univ \ R, cap u w := by
      have hcard_eq : C.card = ∑ _v ∈ C, 1 := by simp
      rw [hcard_eq, Finset.sum_image hinj]
      apply Finset.sum_le_sum
      intro v hv
      exact hsum2 _ (Finset.mem_image_of_mem _ hv)
    omega
  by_cases hsep : ∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C
  · exact ⟨C, hsC, htC, hsep, hcard_le⟩
  · obtain ⟨w, hw⟩ := not_forall.mp hsep
    have hw' : ∀ v ∈ w.support, v ∉ C := fun v hv hc => hw ⟨v, hv, hc⟩
    have hsup_head : w.support.head? = some s := by
      rw [List.head?_eq_some_head w.support_ne_nil, w.head_support]
    have hsup_last : w.support.getLast? = some t := by
      rw [List.getLast?_eq_some_getLast w.support_ne_nil, w.getLast_support]
    obtain ⟨L, hLhead, hLlast, hLchain, hLsub⟩ :=
      chain_to_split G s t big hbig w.support w.isChain_adj_support
        hsup_head hsup_last
    obtain ⟨x, y, hstep, hxR, hyR, hpos⟩ :=
      chain_leaving_step _ R L hLchain hLhead hLlast hSR hTR
    rw [← hcapdef] at hpos
    have hKxy : ∀ (x y : V × Bool), x ∈ R → y ∉ R →
        cap x y ≤ splitCutCap cap R := by
      intro x y hxR hyR
      have hyR' : y ∈ Finset.univ \ R :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyR⟩
      have hK1 : cap x y ≤ ∑ w ∈ Finset.univ \ R, cap x w :=
        Finset.single_le_sum (fun w _ => Nat.zero_le _) hyR'
      have hK2 : (∑ w ∈ Finset.univ \ R, cap x w) ≤ splitCutCap cap R := by
        have hle : (fun u => ∑ w ∈ Finset.univ \ R, cap u w) x ≤
            ∑ u ∈ R, (fun u => ∑ w ∈ Finset.univ \ R, cap u w) u :=
          Finset.single_le_sum
            (fun u _ => Nat.zero_le (∑ w ∈ Finset.univ \ R, cap u w)) hxR
        simpa only [splitCutCap] using hle
      exact le_trans hK1 hK2
    have hKbig : big ≤ splitCutCap cap R := by
      match x, y, hxR, hyR, hpos, hstep with
      | (u, false), (v, true), hxR, hyR, hpos, hstep =>
          have hle := hKxy _ _ hxR hyR
          by_cases huv : u = v
          · subst huv
            by_cases hst : u = s ∨ u = t
            · have hcap_eq : cap (u, false) (u, true) = big := by
                rw [hcapdef, splitCap_self, ite_eq_left hst]
              omega
            · have hvC : u ∈ C := (hCmem u).mpr
                ⟨fun h => hst (Or.inl h), fun h => hst (Or.inr h), hxR, hyR⟩
              have hxL : (u, false) ∈ L := isListStep_mem_left hstep
              have hvsup : u ∈ w.support := hLsub _ hxL
              exact absurd hvC (hw' u hvsup)
          · have hcap0 : cap (u, false) (v, true) = 0 := by
              rw [hcapdef]
              exact splitCap_self_ne G s t big huv
            omega
      | (u, true), (v, false), hxR, hyR, hpos, _ =>
          have hle := hKxy _ _ hxR hyR
          by_cases hadj : G.Adj u v
          · have hcap_eq : cap (u, true) (v, false) = big := by
              rw [hcapdef]
              exact splitCap_edge G s t big hadj
            omega
          · have hcap0 : cap (u, true) (v, false) = 0 := by
              rw [hcapdef]
              exact splitCap_edge_not G s t big hadj
            omega
      | (u, false), (v, false), hxR, hyR, hpos, _ =>
          have hle := hKxy _ _ hxR hyR
          have hcap0 : cap (u, false) (v, false) = 0 := by
            rw [hcapdef]
            exact splitCap_ff G s t big u v
          omega
      | (u, true), (v, true), hxR, hyR, hpos, _ =>
          have hle := hKxy _ _ hxR hyR
          have hcap0 : cap (u, true) (v, true) = 0 := by
            rw [hcapdef]
            exact splitCap_tt G s t big u v
          omega
    refine ⟨(Finset.univ.erase s).erase t, by simp, by simp, ?_, ?_⟩
    · intro p
      obtain ⟨v, hv, hvs, hvt⟩ := exists_internal_vertex G s t hne hnadj p
      refine ⟨v, hv, ?_⟩
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨hvt, hvs⟩
    · have hmem_s : s ∈ (Finset.univ : Finset V) := Finset.mem_univ s
      have hmem_t : t ∈ (Finset.univ : Finset V).erase s :=
        Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ t⟩
      have e1 := Finset.card_erase_of_mem hmem_s
      have e2 := Finset.card_erase_of_mem hmem_t
      have e3 : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
      omega

/-- One-point sum relation for functions agreeing off a point. -/
private theorem sum_one_diff {W : Type*} [Fintype W]
    (g h : W → ℕ) {p : W}
    (hothers : ∀ v, v ≠ p → g v = h v) :
    (∑ v, g v) + h p = (∑ v, h v) + g p := by
  classical
  have hp_mem : p ∈ (Finset.univ : Finset W) := Finset.mem_univ p
  have e1 := Finset.add_sum_erase Finset.univ g hp_mem
  have e2 := Finset.add_sum_erase Finset.univ h hp_mem
  have erest : ∑ v ∈ Finset.univ.erase p, g v =
      ∑ v ∈ Finset.univ.erase p, h v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_erase] at hv
    exact hothers v hv.1
  omega

/-- Chains map forward along pointwise implications. -/
private theorem isChain_mono {W : Type*} {r r' : W → W → Prop} {l : List W}
    (h : ∀ a b, r a b → r' a b) (hc : List.IsChain r l) :
    List.IsChain r' l := by
  induction hc with
  | nil => exact List.IsChain.nil
  | singleton a => exact List.IsChain.singleton a
  | cons_cons hr _ ih => exact List.IsChain.cons_cons (h _ _ hr) ih

/-- Positive flow value reaches the sink along positive arcs. -/
private theorem flow_pos_reachable {V : Type*} [Fintype V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (S T : V × Bool)
    (f : (V × Bool) → (V × Bool) → ℕ) (hf : IsSplitFlow cap S T f)
    (hpos : 0 < splitValue S f) :
    Relation.ReflTransGen (fun a b => 0 < f a b) S T := by
  classical
  obtain ⟨-, hcons, hSin, -⟩ := hf
  by_contra hcon
  set R : Finset (V × Bool) :=
    Finset.univ.filter (fun w => Relation.ReflTransGen (fun a b => 0 < f a b) S w)
    with hRdef
  have hSR : S ∈ R := by
    simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  have hTR : T ∉ R := by
    simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcon
  have hfwd : (∑ u ∈ R, ∑ v ∈ Finset.univ \ R, f u v) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    have huR : Relation.ReflTransGen (fun a b => 0 < f a b) S u := by
      simpa only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and] using hu
    by_contra hne
    have hpos' : 0 < f u v := by omega
    have hRv : Relation.ReflTransGen (fun a b => 0 < f a b) S v := huR.tail hpos'
    have hvR : v ∈ R := by
      simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hRv
    exact (Finset.mem_sdiff.mp hv).2 hvR
  have heq := split_cut_flow S T f hcons hSin R hSR hTR
  rw [hfwd] at heq
  omega

/-- Positive-capacity arcs leaving an entry node stay at the same vertex. -/
private theorem splitCap_from_false {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ)
    {u : V} {w : V × Bool} (h : 0 < splitCap G s t big (u, false) w) :
    w = (u, true) := by
  match w with
  | (v, false) =>
      rw [splitCap_ff G s t big u v] at h
      exact absurd h (by simp)
  | (v, true) =>
      by_cases huv : u = v
      · subst huv
        rfl
      · rw [splitCap_self_ne G s t big huv] at h
        exact absurd h (by simp)

/-- Positive-capacity arcs leaving an exit node follow graph edges. -/
private theorem splitCap_from_true {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ)
    {u : V} {w : V × Bool} (h : 0 < splitCap G s t big (u, true) w) :
    ∃ v, w = (v, false) ∧ G.Adj u v := by
  match w with
  | (v, false) =>
      by_cases hadj : G.Adj u v
      · exact ⟨v, rfl, hadj⟩
      · rw [splitCap_edge_not G s t big hadj] at h
        exact absurd h (by simp)
  | (v, true) =>
      rw [splitCap_tt G s t big u v] at h
      exact absurd h (by simp)

/-- A positive-capacity split chain from an entry to `(t, true)` projects to an
adjacency chain, using each vertex arc along the way. -/
private theorem split_chain_vertices {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ)
    (L : List (V × Bool))
    (hchain : List.IsChain (fun x y => 0 < splitCap G s t big x y) L)
    (hn : L.Nodup)
    {x : V} (hhead : L.head? = some (x, false))
    (hlast : L.getLast? = some (t, true)) :
    ∃ l : List V, l.head? = some x ∧ l.getLast? = some t ∧ List.IsChain G.Adj l ∧
      l.Nodup ∧ (∀ v ∈ l, isListStep L (v, false) (v, true)) := by
  suffices h : ∀ (n : ℕ) (L : List (V × Bool)), L.length ≤ n → ∀ {x : V},
      L.head? = some (x, false) → L.getLast? = some (t, true) →
      List.IsChain (fun x y => 0 < splitCap G s t big x y) L → L.Nodup →
      ∃ l : List V, l.head? = some x ∧ l.getLast? = some t ∧ List.IsChain G.Adj l ∧
        l.Nodup ∧ (∀ v ∈ l, isListStep L (v, false) (v, true)) by
    exact h L.length L le_rfl hhead hlast hchain hn
  intro n
  induction n with
  | zero =>
      intro L hlen x hhead _ _ _
      have hempty : L = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hempty
      simp only [List.head?_nil] at hhead
      exact absurd hhead (by simp)
  | succ n ih =>
      intro L hlen x hhead hlast hchain hn
      match L, hlen, hhead, hlast, hchain, hn with
      | [], _, hhead, _, _, _ =>
          simp only [List.head?_nil] at hhead
          exact absurd hhead (by simp)
      | [y], _, hhead, hlast, _, _ =>
          have hyx : y = (x, false) := by simpa using hhead
          have hyt : y = (t, true) := by simpa using hlast
          have hcon : (x, false) = (t, true) := hyx.symm.trans hyt
          simp at hcon
      | y :: z :: rest, hlen, hhead, hlast, hchain, hn =>
          have hy : y = (x, false) := by simpa using hhead
          subst hy
          have hstep : 0 < splitCap G s t big (x, false) z :=
            (List.isChain_cons_cons.mp hchain).1
          have hz : z = (x, true) := splitCap_from_false G s t big hstep
          subst hz
          match rest, hlast, hchain, hn, hlen with
          | [], hlast, _, _, _ =>
              have hx : t = x := by
                have h2 : (x, true) = (t, true) := by simpa using hlast
                simpa using h2.symm
              subst hx
              refine ⟨[t], rfl, by simp, List.isChain_singleton t,
                List.nodup_singleton t, ?_⟩
              intro v hv
              have hvx : t = v := by
                have h : v = t := by simpa using hv
                exact h.symm
              subst hvx
              have h0 : 0 < ([(t, false), (t, true)] : List (V × Bool)).length := by simp
              have h01 : 0 + 1 < ([(t, false), (t, true)] : List (V × Bool)).length := by simp
              exact ⟨0, h0, h01, rfl, rfl⟩
          | w :: rest', hlast, hchain, hn, hlen =>
              have hstep2 : 0 < splitCap G s t big (x, true) w :=
                (List.isChain_cons_cons.mp hchain.tail).1
              obtain ⟨v, rfl, hadj⟩ := splitCap_from_true G s t big hstep2
              have hlast_t : ((v, false) :: rest').getLast? = some (t, true) := by
                have h2 : (((x, false) :: (x, true) :: (v, false) :: rest') :
                    List (V × Bool)).getLast? = ((v, false) :: rest').getLast? := by
                  rw [List.getLast?_cons_cons, List.getLast?_cons_cons]
                rwa [h2] at hlast
              have hlen_t : ((v, false) :: rest').length ≤ n := by
                have e : (((x, false) :: (x, true) :: (v, false) :: rest') :
                    List (V × Bool)).length = ((v, false) :: rest').length + 2 := rfl
                omega
              have hchain_t : List.IsChain (fun x y => 0 < splitCap G s t big x y)
                  ((v, false) :: rest') := hchain.tail.tail
              have hn1 : ((x, true) :: (v, false) :: rest').Nodup :=
                (List.nodup_cons.mp hn).2
              have hn_t : ((v, false) :: rest').Nodup := (List.nodup_cons.mp hn1).2
              obtain ⟨l', hh', hl', hc', hnd', hsteps'⟩ :=
                ih ((v, false) :: rest') hlen_t rfl hlast_t hchain_t hn_t
              match l', hh', hl', hc' with
              | [], hh', _, _ =>
                  simp only [List.head?_nil] at hh'
                  exact absurd hh' (by simp)
              | v' :: l'', hh', hl', hc' =>
                  have hv' : v = v' := by
                    have h := hh'
                    simpa using h.symm
                  subst hv'
                  refine ⟨x :: v :: l'', rfl, ?_, ?_, ?_, ?_⟩
                  · rw [List.getLast?_cons_cons]
                    exact hl'
                  · rw [List.isChain_cons_cons]
                    exact ⟨hadj, hc'⟩
                  · refine List.nodup_cons.mpr ⟨?_, hnd'⟩
                    intro hcon
                    have hstepx := hsteps' x hcon
                    have hmem : (x, false) ∈ ((v, false) :: rest') :=
                      isListStep_mem_left hstepx
                    have hmem2 : (x, false) ∈
                        ((x, true) :: (v, false) :: rest') :=
                      List.mem_cons_of_mem _ hmem
                    exact (List.nodup_cons.mp hn).1 hmem2
                  · intro u hu
                    simp only [List.mem_cons] at hu
                    rcases hu with rfl | hu
                    · have hLlen : (((x, false) :: (x, true) :: (v, false) :: rest') :
                          List (V × Bool)).length = rest'.length + 3 := rfl
                      have hlen0 : 0 < (((x, false) :: (x, true) :: (v, false) :: rest') :
                          List (V × Bool)).length := by omega
                      have h01 : 0 + 1 < (((x, false) :: (x, true) :: (v, false) :: rest') :
                          List (V × Bool)).length := by omega
                      exact ⟨0, hlen0, h01, rfl, rfl⟩
                    · have hu' : u ∈ v :: l'' := List.mem_cons.mpr hu
                      obtain ⟨i, hi, hi1, ha, hb⟩ := hsteps' u hu'
                      have e : (((x, false) :: (x, true) :: (v, false) :: rest') :
                          List (V × Bool)).length =
                          ((v, false) :: rest').length + 2 := rfl
                      have hi1' : i + 2 < (((x, false) :: (x, true) :: (v, false) :: rest') :
                          List (V × Bool)).length := by omega
                      have hi2' : i + 2 + 1 < (((x, false) :: (x, true) :: (v, false) :: rest') :
                          List (V × Bool)).length := by omega
                      refine ⟨i + 2, hi1', hi2', ?_, ?_⟩
                      · have hget : ((((x, false) :: (x, true) :: (v, false) :: rest') :
                          List (V × Bool))[i + 2]'hi1') =
                          (((v, false) :: rest')[i]'hi) := rfl
                        rw [hget]
                        exact ha
                      · have hget : ((((x, false) :: (x, true) :: (v, false) :: rest') :
                          List (V × Bool))[i + 2 + 1]'hi2') =
                          (((v, false) :: rest')[i + 1]'hi1) := rfl
                        rw [hget]
                        exact hb

/-- An adjacency chain with endpoints yields a walk with that support. -/
private theorem walk_of_chain {V : Type*} (G : SimpleGraph V) :
    ∀ (l : List V), List.IsChain G.Adj l → ∀ {a b : V},
      l.head? = some a → l.getLast? = some b →
      ∃ w : G.Walk a b, w.support = l := by
  intro l
  induction l with
  | nil =>
      intro _ _ _ hhead _
      simp only [List.head?_nil] at hhead
      exact absurd hhead (by simp)
  | cons x t ih =>
      intro hc a b hhead hlast
      match t, hc, hhead, hlast with
      | [], _, hhead, hlast =>
          have hxa : x = a := by simpa using hhead
          have hxb : x = b := by simpa using hlast
          subst hxa
          subst hxb
          exact ⟨SimpleGraph.Walk.nil, rfl⟩
      | y :: t', hc, hhead, hlast =>
          have hxa : x = a := by simpa using hhead
          subst hxa
          have hadj : G.Adj x y := (List.isChain_cons_cons.mp hc).1
          have hc_t : List.IsChain G.Adj (y :: t') := hc.tail
          have hlast_t : (y :: t').getLast? = some b := by
            rw [List.getLast?_cons_cons] at hlast
            exact hlast
          obtain ⟨w', hw'⟩ := ih hc_t rfl hlast_t
          refine ⟨SimpleGraph.Walk.cons hadj w', ?_⟩
          rw [SimpleGraph.Walk.support_cons, hw']

/-- Removing a path: decrement flow along list steps. -/
private noncomputable def splitRemove {V : Type*}
    (l : List (V × Bool)) (f : (V × Bool) → (V × Bool) → ℕ) :
    (V × Bool) → (V × Bool) → ℕ :=
  fun a b => f a b - (if isListStep l a b then 1 else 0)

/-- Removing a nodup positive-flow path decreases flow value by exactly one. -/
private theorem split_remove {V : Type*} [Fintype V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (S T : V × Bool) (hST : S ≠ T)
    (f : (V × Bool) → (V × Bool) → ℕ) (hf : IsSplitFlow cap S T f)
    (l : List (V × Bool)) (hhead : l.head? = some S) (hlast : l.getLast? = some T)
    (hpos : ∀ a b, isListStep l a b → 0 < f a b) (hn : l.Nodup) :
    ∃ f' : (V × Bool) → (V × Bool) → ℕ,
      IsSplitFlow cap S T f' ∧ splitValue S f' + 1 = splitValue S f ∧
      (∀ a b, f' a b ≤ f a b) ∧
      (∀ a b, isListStep l a b → f' a b + 1 = f a b) := by
  classical
  obtain ⟨hle, hcons, hSin, hTout⟩ := hf
  have hlen2 : 2 ≤ l.length := by
    match l, hhead, hlast with
    | [], hhead, _ =>
        simp only [List.head?_nil] at hhead
        exact absurd hhead (by simp)
    | [x], hhead, hlast =>
        have hxS : x = S := by simpa using hhead
        have hxT : x = T := by simpa using hlast
        exact absurd (hxS.symm.trans hxT) hST
    | x :: y :: t, _, _ =>
        have e : (x :: y :: t).length = t.length + 2 := rfl
        omega
  have hlen_pos : 0 < l.length := by omega
  have hS0 : l[0]'hlen_pos = S := head?_getElem_zero hhead hlen_pos
  have h1lt : 1 < l.length := by omega
  have h01 : 0 + 1 < l.length := by omega
  have hstep0 : isListStep l S (l[1]'h1lt) := ⟨0, hlen_pos, h01, hS0, rfl⟩
  set f' : (V × Bool) → (V × Bool) → ℕ := splitRemove l f with hf'def
  have hf'_step : ∀ a b, isListStep l a b → f' a b + 1 = f a b := by
    intro a b hstep
    have h1 := hpos a b hstep
    simp only [hf'def, splitRemove, ite_eq_left hstep]
    omega
  have hf'_same : ∀ a b, ¬ isListStep l a b → f' a b = f a b := by
    intro a b hstep
    simp only [hf'def, splitRemove, ite_eq_right hstep, Nat.sub_zero]
  have hfle : ∀ a b, f' a b ≤ f a b := by
    intro a b
    by_cases hstep : isListStep l a b
    · have h := hf'_step a b hstep
      omega
    · exact le_of_eq (hf'_same a b hstep)
  have hcap' : ∀ a b, f' a b ≤ cap a b := fun a b => le_trans (hfle a b) (hle a b)
  have hcons' : ∀ x, x ≠ S → x ≠ T →
      (∑ u, f' u x) = ∑ v, f' x v := by
    intro x hxS hxT
    by_cases hxmem : x ∈ l
    · obtain ⟨j, hj, hjEq⟩ := mem_getElem_idx hxmem
      have hj0 : j ≠ 0 := by
        intro hcon
        subst hcon
        exact hxS (hjEq.symm.trans hS0)
      obtain ⟨hlast_idx, hTlast⟩ := getLast?_getElem_last hlast
      have hjlast : j ≠ l.length - 1 := by
        intro hcon
        subst hcon
        exact hxT (hjEq.symm.trans hTlast)
      have hj1 : j + 1 < l.length := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hk : k < l.length := by omega
      have hkin : isListStep l (l[k]'hk) x := ⟨k, hk, hj, rfl, hjEq⟩
      have hkout : isListStep l x (l[k + 1 + 1]'hj1) := ⟨k + 1, hj, hj1, hjEq, rfl⟩
      have hin_char : ∀ u, isListStep l u x ↔ u = l[k]'hk := by
        intro u
        constructor
        · intro hstep
          exact isListStep_unique_right hn hstep hkin
        · intro heq
          subst heq
          exact hkin
      have hout_char : ∀ v, isListStep l x v ↔ v = l[k + 1 + 1]'hj1 := by
        intro v
        constructor
        · intro hstep
          exact isListStep_unique_left hn hstep hkout
        · intro heq
          subst heq
          exact hkout
      have hcol := sum_one_diff (fun u => f' u x) (fun u => f u x)
        (p := l[k]'hk) (fun u hu => hf'_same u x (fun h => hu ((hin_char u).mp h)))
      have hrow := sum_one_diff (fun v => f' x v) (fun v => f x v)
        (p := l[k + 1 + 1]'hj1)
        (fun v hv => hf'_same x v (fun h => hv ((hout_char v).mp h)))
      have hcol' : (∑ u, f' u x) + f (l[k]'hk) x =
          (∑ u, f u x) + f' (l[k]'hk) x := hcol
      have hrow' : (∑ v, f' x v) + f x (l[k + 1 + 1]'hj1) =
          (∑ v, f x v) + f' x (l[k + 1 + 1]'hj1) := hrow
      have hstep_in := hf'_step _ _ hkin
      have hstep_out := hf'_step _ _ hkout
      have hcon0 := hcons x hxS hxT
      omega
    · have hrow : ∀ v, f' x v = f x v := by
        intro v
        apply hf'_same
        intro hcon
        exact hxmem (isListStep_mem_left hcon)
      have hcol : ∀ u, f' u x = f u x := by
        intro u
        apply hf'_same
        intro hcon
        exact hxmem (isListStep_mem_right hcon)
      rw [Finset.sum_congr rfl (fun u _ => hcol u),
        Finset.sum_congr rfl (fun v _ => hrow v)]
      exact hcons x hxS hxT
  have hSin' : ∀ v, f' v S = 0 := by
    intro v
    rw [hf'_same v S (fun hcon => isListStep_not_to_head hhead hn hcon)]
    exact hSin v
  have hTout' : ∀ v, f' T v = 0 := by
    intro v
    rw [hf'_same T v (fun hcon => isListStep_not_from_last hlast hn hcon)]
    exact hTout v
  have hval : splitValue S f' + 1 = splitValue S f := by
    have houtS : ∀ v, isListStep l S v ↔ v = l[1]'h1lt := by
      intro v
      constructor
      · intro hstep
        exact isListStep_unique_left hn hstep hstep0
      · intro heq
        subst heq
        exact hstep0
    have hrowS := sum_one_diff (fun v => f' S v) (fun v => f S v)
      (p := l[1]'h1lt) (fun v hv => hf'_same S v (fun h => hv ((houtS v).mp h)))
    have hrowS' : (∑ v, f' S v) + f S (l[1]'h1lt) =
        (∑ v, f S v) + f' S (l[1]'h1lt) := hrowS
    have hst := hf'_step _ _ hstep0
    simp only [splitValue]
    omega
  exact ⟨f', ⟨hcap', hcons', hSin', hTout'⟩, hval, hfle, hf'_step⟩

/-- Any split-network flow yields an internally-disjoint family no smaller than
its value, with paths using only positive vertex arcs. -/
private theorem flow_to_family {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V)
    (big : ℕ) (f : (V × Bool) → (V × Bool) → ℕ)
    (hf : IsSplitFlow (splitCap G s t big) (s, false) (t, true) f) :
    ∃ m : ℕ, ∃ Q : Fin m → G.Walk s t,
      (∀ i, (Q i).support.Nodup) ∧
      (∀ i j, i ≠ j → ∀ v, v ∈ (Q i).support → v ∈ (Q j).support → v = s ∨ v = t) ∧
      (∀ i, ∀ v ∈ (Q i).support, v ≠ s → v ≠ t → 0 < f (v, false) (v, true)) ∧
      splitValue (s, false) f ≤ m := by
  suffices h : ∀ (n : ℕ) (f : (V × Bool) → (V × Bool) → ℕ),
      IsSplitFlow (splitCap G s t big) (s, false) (t, true) f →
      splitValue (s, false) f ≤ n →
      ∃ m : ℕ, ∃ Q : Fin m → G.Walk s t,
        (∀ i, (Q i).support.Nodup) ∧
        (∀ i j, i ≠ j → ∀ v, v ∈ (Q i).support → v ∈ (Q j).support → v = s ∨ v = t) ∧
        (∀ i, ∀ v ∈ (Q i).support, v ≠ s → v ≠ t → 0 < f (v, false) (v, true)) ∧
        splitValue (s, false) f ≤ m by
    exact h (splitValue (s, false) f) f hf le_rfl
  intro n
  induction n with
  | zero =>
      intro f _ hle
      have hval : splitValue (s, false) f = 0 := by omega
      exact ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, by omega⟩
  | succ n ih =>
      intro f hf hle
      by_cases h0 : splitValue (s, false) f = 0
      · exact ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
          fun i => Fin.elim0 i, by omega⟩
      · have hpos : 0 < splitValue (s, false) f := by omega
        have hST : (s, false) ≠ (t, true) := by simp
        have hreach :=
          flow_pos_reachable (splitCap G s t big) (s, false) (t, true) f hf hpos
        obtain ⟨L, hhead, hlast, hchainL, hnL⟩ := reflTransGen_to_nodup _ hreach
        have hstep_pos : ∀ a b, isListStep L a b → 0 < f a b := by
          intro a b hstep
          have h := isListStep_chain hchainL hstep
          exact h
        have hchainCap : List.IsChain (fun x y => 0 < splitCap G s t big x y) L :=
          isChain_mono (fun a b hab => lt_of_lt_of_le hab (hf.1 a b)) hchainL
        obtain ⟨l, hheadl, hlastl, hchainl, hndl, hstepsl⟩ :=
          split_chain_vertices G s t big L hchainCap hnL hhead hlast
        obtain ⟨w, hwsup⟩ := walk_of_chain G l hchainl hheadl hlastl
        obtain ⟨f', hf', hval', hfle, hfstep⟩ :=
          split_remove (splitCap G s t big) (s, false) (t, true) hST f hf L hhead
            hlast hstep_pos hnL
        have hval'_le : splitValue (s, false) f' ≤ n := by omega
        obtain ⟨m', Q', hQn', hQd', hQuse', hQle'⟩ := ih f' hf' hval'_le
        have hQuse : ∀ i, ∀ v ∈ (Q' i).support, v ≠ s → v ≠ t →
            0 < f (v, false) (v, true) := by
          intro i v hv hvs hvt
          exact lt_of_lt_of_le (hQuse' i v hv hvs hvt) (hfle _ _)
        have hwNodup : w.support.Nodup := by rw [hwsup]; exact hndl
        have hwUse : ∀ v ∈ w.support, v ≠ s → v ≠ t →
            0 < f (v, false) (v, true) := by
          intro v hv _ _
          rw [hwsup] at hv
          exact hstep_pos _ _ (hstepsl v hv)
        have hdisjW : ∀ (j : Fin m') (v : V), v ∈ w.support →
            v ∈ (Q' j).support → v = s ∨ v = t := by
          intro j v hvw hvQ
          by_contra hcon
          have hvs : v ≠ s := fun h => hcon (Or.inl h)
          have hvt : v ≠ t := fun h => hcon (Or.inr h)
          have huse_f : 0 < f (v, false) (v, true) := hwUse v hvw hvs hvt
          have hcap1 : splitCap G s t big (v, false) (v, true) = 1 := by
            rw [splitCap_self, ite_eq_right (fun h => h.elim hvs hvt)]
          have hf1 : f (v, false) (v, true) = 1 := by
            have hle1 := hf.1 (v, false) (v, true)
            rw [hcap1] at hle1
            omega
          have hstepL : isListStep L (v, false) (v, true) := by
            rw [hwsup] at hvw
            exact hstepsl v hvw
          have hdec := hfstep _ _ hstepL
          have huse_f' : 0 < f' (v, false) (v, true) := hQuse' j v hvQ hvs hvt
          omega
        refine ⟨m' + 1, Fin.cons w Q', ?_, ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ ?_ i
          · simp only [Fin.cons_zero]
            exact hwNodup
          · intro j
            simp only [Fin.cons_succ]
            exact hQn' j
        · intro i
          refine Fin.cases ?_ ?_ i
          · intro j
            refine Fin.cases ?_ ?_ j
            · intro hij
              exact absurd rfl hij
            · intro j' _ v hvi hvj
              simp only [Fin.cons_zero, Fin.cons_succ] at hvi hvj
              exact hdisjW j' v hvi hvj
          · intro i' j
            refine Fin.cases ?_ ?_ j
            · intro _ v hvi hvj
              simp only [Fin.cons_succ, Fin.cons_zero] at hvi hvj
              exact hdisjW i' v hvj hvi
            · intro j' hij v hvi hvj
              simp only [Fin.cons_succ] at hvi hvj
              have hij' : i' ≠ j' := fun h => hij (by rw [h])
              exact hQd' i' j' hij' v hvi hvj
        · intro i
          refine Fin.cases ?_ ?_ i
          · intro v hv hvs hvt
            simp only [Fin.cons_zero] at hv
            exact hwUse v hv hvs hvt
          · intro j v hv hvs hvt
            simp only [Fin.cons_succ] at hv
            exact hQuse j v hv hvs hvt
        · omega

/-- **Menger's theorem, vertex form.** Let $G$ be a simple graph on a finite vertex set and let
$s$ and $t$ be distinct, nonadjacent vertices of $G$. Then there is a natural number $n$ with
the following two properties. First, there is a set $C$ of exactly $n$ vertices with
$s \notin C$ and $t \notin C$ such that every walk from $s$ to $t$ passes through a vertex of
$C$, and every set of vertices with these three properties has at least $n$ elements. Second,
there are $n$ paths $P_1, \dots, P_n$ from $s$ to $t$ (walks that repeat no vertex) such that
every vertex lying on both $P_i$ and $P_j$ for some $i \ne j$ is $s$ or $t$, and every finite
family of paths from $s$ to $t$ with this property has at most $n$ members. Thus the minimum
number of vertices other than $s$ and $t$ whose removal separates $s$ from $t$ equals the
maximum number of pairwise internally disjoint paths from $s$ to $t$.

Proves `Wanted` entry `menger_vertex`.

Source: K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927), 96–115,
doi:10.4064/fm-10-1-96-115; statement as in https://en.wikipedia.org/wiki/Menger%27s_theorem
(`menger-s1`).
-/
theorem menger_vertex :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : V),
      s ≠ t →
      ¬ G.Adj s t →
      ∃ n : ℕ,
        (∃ C : Finset V,
          C.card = n ∧
          s ∉ C ∧
          t ∉ C ∧
          (∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C) ∧
          ∀ C' : Finset V, s ∉ C' → t ∉ C' →
            (∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C') → n ≤ C'.card) ∧
        ∃ P : Fin n → G.Walk s t,
          (∀ i, (P i).support.Nodup) ∧
          (∀ i j, i ≠ j → ∀ v, v ∈ (P i).support → v ∈ (P j).support → v = s ∨ v = t) ∧
          ∀ (m : ℕ) (Q : Fin m → G.Walk s t),
            (∀ i, (Q i).support.Nodup) →
            (∀ i j, i ≠ j → ∀ v, v ∈ (Q i).support → v ∈ (Q j).support → v = s ∨ v = t) →
            m ≤ n := by
  intro V _ G s t hne hnadj
  obtain ⟨n₁, C, hCcard, hsC, htC, hhitC, hmin⟩ := min_separator G s t hne hnadj
  obtain ⟨n₂, P, hPn, hPd, hmax⟩ := max_family G s t hne hnadj
  -- Easy direction of the min-max equality: the max family is no larger than the min cut.
  have h12 : n₂ ≤ n₁ := by
    rw [← hCcard]
    exact family_le_sep G s t hne hnadj n₂ P hPn hPd C hsC htC hhitC
  -- Hard direction via max-flow/min-cut on the vertex-split network.
  have h21 : n₁ ≤ n₂ := by
    classical
    have := Fintype.ofFinite V
    have hST : (s, false) ≠ (t, true) := by simp
    obtain ⟨fl, hfl, -, hmaxfl⟩ :=
      split_max_flow (splitCap G s t (Fintype.card V)) (s, false) (t, true) hST
    obtain ⟨R, hSR, hTR, hval⟩ :=
      split_mincut (splitCap G s t (Fintype.card V)) (s, false) (t, true) fl hfl
        hmaxfl
    obtain ⟨C', hs', ht', hhit', hcard'⟩ :=
      cut_to_separator G s t hne hnadj R hSR hTR
    obtain ⟨m, Q, hQn, hQd, -, hQle⟩ :=
      flow_to_family G s t (Fintype.card V) fl hfl
    have h1 : n₁ ≤ C'.card := hmin C' hs' ht' hhit'
    have h2 : m ≤ n₂ := hmax m Q hQn hQd
    omega
  have heq : n₁ = n₂ := le_antisymm h21 h12
  subst heq
  exact ⟨n₁, ⟨C, hCcard, hsC, htC, hhitC, hmin⟩, ⟨P, hPn, hPd, hmax⟩⟩

end MetaMathlibExt

namespace MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted

/-
Adapted from `WantedExt/Combinatorics/SimpleGraph/MengerVertexWanted.lean`: the
definitions `IsInternallyVertexDisjointSTPaths` and `IsSTVertexCut`, and the statement
of `menger_vertex_max_min`, follow the API proposed there, originally contributed by
`@toskua, Avocado`. All proofs given here are new.
-/

/-- **Internally vertex-disjoint paths.** Let $G$ be a simple graph with vertices $s$ and $t$,
and let $P_0, \dots, P_{n-1}$ be a family of paths from $s$ to $t$ in $G$, indexed by
$\{0, \dots, n-1\}$. The family is internally vertex-disjoint when for all indices $i \ne j$,
every vertex lying on both $P_i$ and $P_j$ is $s$ or $t$. -/
def IsInternallyVertexDisjointSTPaths {V : Type*} {G : SimpleGraph V}
    {s t : V} {n : ℕ} (paths : Fin n → G.Path s t) : Prop :=
  ∀ i j, i ≠ j → ∀ v, v ∈ (paths i).val.support →
    v ∈ (paths j).val.support → v = s ∨ v = t

/-- **Vertex cuts separating two vertices.** Let $G$ be a simple graph on a finite vertex set, let
$s$ and $t$ be vertices of $G$, and let $C$ be a set of vertices of $G$. Then $C$ is an $s$-$t$
vertex cut when $s \notin C$, $t \notin C$, and $t$ is not reachable from $s$ in the graph
obtained from $G$ by deleting every edge that has an endpoint in $C$. -/
def IsSTVertexCut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (C : Finset V) : Prop :=
  s ∉ C ∧ t ∉ C ∧
    ¬ (((⊤ : G.Subgraph).deleteVerts (↑C : Set V)).spanningCoe.Reachable s t)

/-- Every path has a nodup vertex list. -/
private theorem path_val_nodup {V : Type*} {G : SimpleGraph V} {s t : V}
    (p : G.Path s t) : (p.val).support.Nodup :=
  p.property.support_nodup

/-- Every walk with a nodup vertex list is a path. -/
private def path_of_nodupWalk {V : Type*} {G : SimpleGraph V} {s t : V}
    (w : G.Walk s t) (h : w.support.Nodup) : G.Path s t :=
  ⟨w, SimpleGraph.Walk.IsPath.mk' h⟩

/-- A walk in the vertex-deleted spanning graph is a walk in `G` with the same support. -/
private theorem spanningWalk_to_walk {V : Type*} (G : SimpleGraph V) (C : Finset V)
    {a b : V}
    (q : (((⊤ : G.Subgraph).deleteVerts (↑C : Set V)).spanningCoe).Walk a b) :
    ∃ p : G.Walk a b, p.support = q.support := by
  induction q with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | cons h _ ih =>
    obtain ⟨p', hp'⟩ := ih
    exact ⟨SimpleGraph.Walk.cons (SimpleGraph.Subgraph.spanningCoe_le _ h) p', by
      simp only [SimpleGraph.Walk.support_cons, hp']⟩

/-- Every walk of the vertex-deleted graph starting outside `C` avoids `C`. -/
private theorem spanningWalk_avoids {V : Type*} (G : SimpleGraph V) (C : Finset V)
    {a b : V}
    (q : (((⊤ : G.Subgraph).deleteVerts (↑C : Set V)).spanningCoe).Walk a b) :
    a ∉ C → ∀ v ∈ q.support, v ∉ C := by
  induction q with
  | nil =>
    intro ha v hv
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv
    exact ha
  | cons h _ ih =>
    intro _ x hx
    have hsub : (((⊤ : G.Subgraph).deleteVerts (↑C : Set V)).spanningCoe).Adj _ _ := h
    rw [SimpleGraph.Subgraph.spanningCoe_adj,
      SimpleGraph.Subgraph.deleteVerts_adj] at hsub
    obtain ⟨-, huC, -, hvC, -⟩ := hsub
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact fun hcon => huC (Finset.mem_coe.mpr hcon)
    · exact ih (fun hcon => hvC (Finset.mem_coe.mpr hcon)) x hx

/-- A `G`-walk avoiding `C` lifts to a walk of the vertex-deleted graph. -/
private theorem walk_avoiding_reachable {V : Type*} (G : SimpleGraph V) (C : Finset V)
    {a b : V} (p : G.Walk a b) (havoid : ∀ v ∈ p.support, v ∉ C) :
    (((⊤ : G.Subgraph).deleteVerts (↑C : Set V)).spanningCoe).Reachable a b := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u v w h tail ih =>
    have hu : u ∉ C := havoid u (by simp [SimpleGraph.Walk.support_cons])
    have htail : ∀ x ∈ tail.support, x ∉ C := by
      intro x hx
      exact havoid x (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem u hx)
    have hv : v ∉ C := htail v (SimpleGraph.Walk.start_mem_support tail)
    obtain ⟨q'⟩ := ih htail
    have h' : (((⊤ : G.Subgraph).deleteVerts (↑C : Set V)).spanningCoe).Adj u v := by
      rw [SimpleGraph.Subgraph.spanningCoe_adj,
        SimpleGraph.Subgraph.deleteVerts_adj]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Subgraph.verts_top]
        exact Set.mem_univ _
      · exact fun hcon => hu (Finset.mem_coe.mp hcon)
      · rw [SimpleGraph.Subgraph.verts_top]
        exact Set.mem_univ _
      · exact fun hcon => hv (Finset.mem_coe.mp hcon)
      · exact SimpleGraph.Subgraph.top_adj.mpr h
    exact ⟨SimpleGraph.Walk.cons h' q'⟩

/-- **Vertex cuts are walk separators.** Let $G$ be a simple graph on a finite vertex set, let $s$
and $t$ be vertices of $G$, and let $C$ be a set of vertices of $G$. Then $C$ is an $s$-$t$ vertex
cut if and only if $s \notin C$, $t \notin C$, and every walk from $s$ to $t$ in $G$ passes
through a vertex of $C$. -/
theorem isSTVertexCut_iff_walkSeparator {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (C : Finset V) :
    IsSTVertexCut G s t C ↔
      s ∉ C ∧ t ∉ C ∧ ∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C := by
  constructor
  · rintro ⟨hs, ht, hnot⟩
    refine ⟨hs, ht, fun p => ?_⟩
    by_contra hcon
    exact hnot (walk_avoiding_reachable G C p (fun v hv hc => hcon ⟨v, hv, hc⟩))
  · rintro ⟨hs, ht, hhit⟩
    refine ⟨hs, ht, fun ⟨q⟩ => ?_⟩
    obtain ⟨p, hp⟩ := spanningWalk_to_walk G C q
    obtain ⟨v, hv, hvC⟩ := hhit p
    rw [hp] at hv
    exact (spanningWalk_avoids G C q hs v hv) hvC

/--
**Menger's theorem for vertex cuts and internally disjoint paths.** Let $G$ be a simple graph on a
finite vertex set and let $s$ and $t$ be distinct, nonadjacent vertices of $G$. Then there is a
natural number $k$ such that there exist $k$ internally vertex-disjoint paths from $s$ to $t$ and
an $s$-$t$ vertex cut with exactly $k$ vertices, every family of internally vertex-disjoint
paths from $s$ to $t$ has at most $k$ members, and every $s$-$t$ vertex cut has at least $k$
vertices. In words, the maximum number of internally vertex-disjoint paths from $s$ to $t$
equals the minimum size of an $s$-$t$ vertex cut.

Proves `Wanted` entry `menger_vertex_max_min`.

Source: K. Menger, Fund. Math. 10 (1927), DOI 10.4064/fm-10-1-96-115.
-/
theorem menger_vertex_max_min
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t) (hadj : ¬ G.Adj s t) :
    ∃ k : ℕ, ∃ (paths : Fin k → G.Path s t) (C : Finset V),
      IsInternallyVertexDisjointSTPaths paths ∧
      IsSTVertexCut G s t C ∧
      C.card = k ∧
      (∀ {l : ℕ} (paths' : Fin l → G.Path s t),
        IsInternallyVertexDisjointSTPaths paths' → l ≤ k) ∧
      (∀ C' : Finset V, IsSTVertexCut G s t C' → k ≤ C'.card) := by
  obtain ⟨n, ⟨C, hCcard, hsC, htC, hhitC, hmin⟩, ⟨P, hPn, hPd, hmax⟩⟩ :=
    MetaMathlibExt.menger_vertex G s t hst hadj
  refine ⟨n, (fun i => path_of_nodupWalk (P i) (hPn i)), C, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij v hvi hvj
    exact hPd i j hij v hvi hvj
  · exact (isSTVertexCut_iff_walkSeparator G s t C).mpr ⟨hsC, htC, hhitC⟩
  · exact hCcard
  · intro l paths' hdisj
    exact hmax l (fun i => (paths' i).val) (fun i => path_val_nodup (paths' i))
      (fun i j hij v hvi hvj => hdisj i j hij v hvi hvj)
  · intro C' hcut
    obtain ⟨hs', ht', hhit'⟩ := (isSTVertexCut_iff_walkSeparator G s t C').mp hcut
    exact hmin C' hs' ht' hhit'

end MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted
end
