/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Lattice.Nat

@[expose] public section

open scoped symmDiff

private theorem zipWith_get {α β γ : Type*} (f : α → β → γ) (l₁ : List α) (l₂ : List β)
    (i : ℕ) (hi : i < (List.zipWith f l₁ l₂).length)
    (h1 : i < l₁.length) (h2 : i < l₂.length) :
    (List.zipWith f l₁ l₂).get ⟨i, hi⟩ = f (l₁.get ⟨i, h1⟩) (l₂.get ⟨i, h2⟩) := by
  induction l₁ generalizing l₂ i with
  | nil => simp at hi
  | cons a t ih =>
    cases l₂ with
    | nil => simp at hi
    | cons b s =>
      cases i with
      | zero => rfl
      | succ n =>
        simp only [List.zipWith_cons_cons] at hi ⊢
        simp only [List.get_cons_succ]
        exact ih s n (by simpa using hi) (by simpa using h1) (by simpa using h2)

private theorem walk_edge_get {V : Type*} (G : SimpleGraph V) {u v : V} (p : G.Walk u v)
    (i : ℕ) (hi : i < p.edges.length)
    (e1 : i < p.support.length) (e2 : i + 1 < p.support.length) :
    p.edges.get ⟨i, hi⟩ =
      s(p.support.get ⟨i, e1⟩, p.support.get ⟨i + 1, e2⟩) := by
  have hsup_len : p.support.length = p.edges.length + 1 := by
    rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_edges]
  have htail_len : p.support.tail.length + 1 = p.support.length := by
    cases h : p.support with
    | nil => exact absurd h (SimpleGraph.Walk.support_ne_nil p)
    | cons a t => simp
  have e1' : i < p.support.length := e1
  have e2' : i < p.support.tail.length := by omega
  revert hi
  rw [SimpleGraph.Walk.edges_eq_zipWith_support]
  intro hi
  rw [zipWith_get _ _ _ _ _ e1' e2']
  congr 1
  exact List.get_tail _ _ _ (by omega)

private theorem walk_support_zero_get {V : Type*} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (h : 0 < p.support.length) :
    p.support.get ⟨0, h⟩ = u := by
  cases p with
  | nil => rfl
  | cons hadj q => rfl

private theorem walk_support_last_get {V : Type*} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (h : p.edges.length < p.support.length) :
    p.support.get ⟨p.edges.length, h⟩ = v := by
  induction p with
  | nil =>
    simp [SimpleGraph.Walk.edges_nil, SimpleGraph.Walk.support_nil]
  | cons hadj q ih =>
    have hq : q.edges.length < q.support.length := by
      have e1 := SimpleGraph.Walk.length_edges q
      have e2 := SimpleGraph.Walk.length_support q
      omega
    have hred :
        (SimpleGraph.Walk.cons hadj q).support.get
          ⟨(SimpleGraph.Walk.cons hadj q).edges.length, h⟩ =
        q.support.get ⟨q.edges.length, hq⟩ := by
      simp [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.support_cons]
    exact hred.trans (ih hq)

private theorem chain_consecutive_ne {V : Type*} (G : SimpleGraph V) (M : Finset (Sym2 V))
    {u v : V} (p : G.Walk u v)
    (hchain : List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges)
    (i : ℕ) (hi : i + 1 < p.edges.length) (h1 : i < p.edges.length) :
    (p.edges.get ⟨i, h1⟩ ∈ M) ≠ (p.edges.get ⟨i + 1, hi⟩ ∈ M) := by
  have h0 := hchain.getElem i hi
  simpa [List.get_eq_getElem] using h0

-- Partner lemma: a non-M path edge cannot share a vertex with an off-path M-edge.
private theorem aug_partner {V : Type*} [DecidableEq (Sym2 V)] (G : SimpleGraph V)
    (M : Finset (Sym2 V))
    (hMmatch : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ w : V, w ∈ e₁ → w ∉ e₂)
    {u v : V} (p : G.Walk u v)
    (hsup : p.support.Nodup)
    (hexpu : ∀ e ∈ M, u ∉ e) (hexpv : ∀ e ∈ M, v ∉ e)
    (hchain : List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges)
    (j : ℕ) (hj : j < p.edges.length) (w : V)
    (hwpath : w ∈ p.edges.get ⟨j, hj⟩) (hjnm : p.edges.get ⟨j, hj⟩ ∉ M)
    (m : Sym2 V) (hmM : m ∈ M) (hmE : m ∉ p.edges.toFinset) (hwm : w ∈ m) :
    False := by
  have hsup_len : p.support.length = p.edges.length + 1 := by
    rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_edges]
  have hinj : Function.Injective p.support.get :=
    List.nodup_iff_injective_get.mp hsup
  have hmem : p.edges.get ⟨j, hj⟩ ∈ p.edges := List.get_mem _ _
  have hwsup : w ∈ p.support :=
    p.mem_support_of_mem_edges hmem hwpath
  obtain ⟨⟨k, hk⟩, hwk⟩ := List.mem_iff_get.mp hwsup
  have ej1 : j < p.support.length := by omega
  have ej2 : j + 1 < p.support.length := by omega
  have heq := walk_edge_get G p j hj ej1 ej2
  rw [heq, Sym2.mem_iff] at hwpath
  rcases hwpath with hleft | hright
  · -- w = support[j]: partner is edge j-1, or endpoint u if j = 0
    have hfin : (⟨k, hk⟩ : Fin p.support.length) = ⟨j, ej1⟩ :=
      hinj (hwk.trans hleft)
    have hkj : j = k := (congrArg Fin.val hfin).symm
    subst hkj
    by_cases hj0 : j = 0
    · subst hj0
      have hwu : w = u := hwk.symm.trans (walk_support_zero_get G p _)
      rw [hwu] at hwm
      exact (hexpu m hmM) hwm
    · have hjm1 : j - 1 < p.edges.length := by omega
      have hjm1s : j - 1 < p.support.length := by omega
      have hjm1p1 : j - 1 + 1 < p.edges.length := by omega
      have hjm2 : j - 1 + 1 < p.support.length := by omega
      have hstar := walk_edge_get G p (j - 1) hjm1 hjm1s hjm2
      have hfin2 : (⟨j - 1 + 1, hjm2⟩ : Fin p.support.length) = ⟨j, ej1⟩ :=
        Fin.ext (show j - 1 + 1 = j by omega)
      rw [hfin2] at hstar
      have hwstar : w ∈ p.edges.get ⟨j - 1, hjm1⟩ := by
        rw [hstar, ← hwk]
        exact Sym2.mem_mk_right _ _
      have hstep := chain_consecutive_ne G M p hchain (j - 1) hjm1p1 hjm1
      have hfin3 : (⟨j - 1 + 1, hjm1p1⟩ : Fin p.edges.length) = ⟨j, hj⟩ :=
        Fin.ext (show j - 1 + 1 = j by omega)
      have hjnm' : p.edges.get ⟨j - 1 + 1, hjm1p1⟩ ∉ M := by
        rwa [← hfin3] at hjnm
      have hstarM : p.edges.get ⟨j - 1, hjm1⟩ ∈ M := by
        by_contra hcon
        exact hstep (propext (iff_of_false hcon hjnm'))
      have hstarE : p.edges.get ⟨j - 1, hjm1⟩ ∈ p.edges.toFinset :=
        List.mem_toFinset.mpr (List.get_mem _ _)
      have hnee : p.edges.get ⟨j - 1, hjm1⟩ ≠ m := fun hcon => hmE (hcon ▸ hstarE)
      exact (hMmatch _ hstarM _ hmM hnee _ hwstar) hwm
  · -- w = support[j+1]: partner is edge j+1, or endpoint v if j+1 = length
    have hfin : (⟨k, hk⟩ : Fin p.support.length) = ⟨j + 1, ej2⟩ :=
      hinj (hwk.trans hright)
    have hkj : k = j + 1 := congrArg Fin.val hfin
    subst hkj
    by_cases hj1 : j + 1 < p.edges.length
    · have hj1s : j + 1 < p.support.length := by omega
      have hj2s : j + 1 + 1 < p.support.length := by omega
      have hestar := walk_edge_get G p (j + 1) hj1 hj1s hj2s
      have hwstar : w ∈ p.edges.get ⟨j + 1, hj1⟩ := by
        rw [hestar, ← hwk]
        exact Sym2.mem_mk_left _ _
      have hstep := chain_consecutive_ne G M p hchain j hj1 hj
      have hstarM : p.edges.get ⟨j + 1, hj1⟩ ∈ M := by
        by_contra hcon
        exact hstep (propext (iff_of_false hjnm hcon))
      have hstarE : p.edges.get ⟨j + 1, hj1⟩ ∈ p.edges.toFinset :=
        List.mem_toFinset.mpr (List.get_mem _ _)
      have hnee : p.edges.get ⟨j + 1, hj1⟩ ≠ m := fun hcon => hmE (hcon ▸ hstarE)
      exact (hMmatch _ hstarM _ hmM hnee _ hwstar) hwm
    · have hlast : p.edges.length < p.support.length := by omega
      have hjeq : j + 1 = p.edges.length := by omega
      have hfin4 : (⟨j + 1, hk⟩ : Fin p.support.length) =
          ⟨p.edges.length, hlast⟩ := Fin.ext hjeq
      rw [hfin4, walk_support_last_get G p hlast] at hwk
      rw [← hwk] at hwm
      exact (hexpv m hmM) hwm

-- Edges at distance ≥ 2 in a Nodup-support walk are disjoint.
private theorem walk_far_edges_disjoint {V : Type*} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v)
    (hsup : p.support.Nodup) (i j : ℕ)
    (hi : i < p.edges.length) (hj : j < p.edges.length) (hfar : i + 1 < j) :
    ∀ (w : V), w ∈ p.edges.get ⟨i, hi⟩ → w ∉ p.edges.get ⟨j, hj⟩ := by
  have hsup_len : p.support.length = p.edges.length + 1 := by
    rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_edges]
  have ei1 : i < p.support.length := by omega
  have ei2 : i + 1 < p.support.length := by omega
  have ej1 : j < p.support.length := by omega
  have ej2 : j + 1 < p.support.length := by omega
  rw [walk_edge_get G p i hi ei1 ei2, walk_edge_get G p j hj ej1 ej2]
  intro w hw1 hw2
  rw [Sym2.mem_iff] at hw1 hw2
  have hinj : Function.Injective p.support.get :=
    List.nodup_iff_injective_get.mp hsup
  rcases hw1 with rfl | rfl
  · rcases hw2 with h2 | h2
    · have hEq := hinj h2
      have hv := congrArg Fin.val hEq
      simp at hv
      omega
    · have hEq := hinj h2
      have hv := congrArg Fin.val hEq
      simp at hv
      omega
  · rcases hw2 with h2 | h2
    · have hEq := hinj h2
      have hv := congrArg Fin.val hEq
      simp at hv
      omega
    · have hEq := hinj h2
      have hv := congrArg Fin.val hEq
      simp at hv
      omega

-- The augmented edge set is a matching.
private theorem aug_matching {V : Type*} [DecidableEq (Sym2 V)] (G : SimpleGraph V)
    (M : Finset (Sym2 V))
    (hMmatch : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ w : V, w ∈ e₁ → w ∉ e₂)
    {u v : V} (p : G.Walk u v)
    (hsup : p.support.Nodup)
    (hexpu : ∀ e ∈ M, u ∉ e) (hexpv : ∀ e ∈ M, v ∉ e)
    (hchain : List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges) :
    ∀ e₁ ∈ ((M \ p.edges.toFinset) ∪ (p.edges.toFinset.filter (· ∉ M))),
    ∀ e₂ ∈ ((M \ p.edges.toFinset) ∪ (p.edges.toFinset.filter (· ∉ M))),
    e₁ ≠ e₂ → ∀ w : V, w ∈ e₁ → w ∉ e₂ := by
  intro e₁ he₁ e₂ he₂ hne w hw₁
  rw [Finset.mem_union] at he₁ he₂
  rw [Finset.mem_sdiff] at he₁ he₂
  rw [Finset.mem_filter] at he₁ he₂
  rcases he₁ with ⟨he₁M, he₁E⟩ | ⟨he₁E, he₁nM⟩ <;>
    rcases he₂ with ⟨he₂M, he₂E⟩ | ⟨he₂E, he₂nM⟩
  · exact hMmatch e₁ he₁M e₂ he₂M hne w hw₁
  · rw [List.mem_toFinset] at he₂E
    obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.mp he₂E
    intro hcon
    exact aug_partner G M hMmatch p hsup hexpu hexpv hchain j hj w hcon he₂nM
      e₁ he₁M he₁E hw₁
  · rw [List.mem_toFinset] at he₁E
    obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_iff_get.mp he₁E
    intro hcon₂
    exact aug_partner G M hMmatch p hsup hexpu hexpv hchain i hi w hw₁ he₁nM
      e₂ he₂M he₂E hcon₂
  · rw [List.mem_toFinset] at he₁E he₂E
    obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_iff_get.mp he₁E
    obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.mp he₂E
    have hij : i ≠ j := fun h => hne (by subst h; rfl)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hcon : j = i + 1 ∨ i + 1 < j := by omega
      rcases hcon with rfl | hfar
      · have hstep := chain_consecutive_ne G M p hchain i
          (by omega : i + 1 < p.edges.length) hi
        exact False.elim (hstep (propext (iff_of_false he₁nM he₂nM)))
      · exact walk_far_edges_disjoint G p hsup i j hi hj hfar w hw₁
    · have hcon : i = j + 1 ∨ j + 1 < i := by omega
      rcases hcon with rfl | hfar
      · have hstep := chain_consecutive_ne G M p hchain j
          (by omega : j + 1 < p.edges.length) hj
        exact False.elim (hstep (propext (iff_of_false he₂nM he₁nM)))
      · intro hcon₂
        exact (walk_far_edges_disjoint G p hsup j i hj hi hfar w hcon₂) hw₁

-- Alternating-list counting lemma (pure list).
private theorem alternating_counts {α : Type*} (f : α → Bool) :
    ∀ (l : List α), List.IsChain (fun a b => f a ≠ f b) l →
    ∀ (b : Bool), l.head?.map f = some b →
    l.countP (fun a => f a == b)
      = l.countP (fun a => f a == !b) + (if l.length % 2 = 1 then 1 else 0) := by
  intro l
  induction l with
  | nil => intro h b hb; nomatch hb
  | cons a t ih =>
    intro h b hb
    have hb2 : f a = b := Option.some_inj.mp hb
    subst hb2
    cases t with
    | nil =>
      simp [List.countP_nil]
    | cons b2 t2 =>
      have htail : List.IsChain (fun a b => f a ≠ f b) (b2 :: t2) :=
        (List.isChain_cons_cons.mp h).2
      have hhead : (b2 :: t2).head?.map f = some (f b2) := rfl
      have ihn := ih htail (f b2) hhead
      have hflip : f b2 = !(f a) := by
        have hrel : f a ≠ f b2 := (List.isChain_cons_cons.mp h).1
        cases hf : f a <;> cases hg : f b2 <;> simp_all
      rw [hflip, Bool.not_not] at ihn
      have c1 : List.countP (fun x => f x == f a) (a :: b2 :: t2)
          = List.countP (fun x => f x == f a) (b2 :: t2) + 1 := by
        simp [List.countP_cons]
      have c2 : List.countP (fun x => f x == !(f a)) (a :: b2 :: t2)
          = List.countP (fun x => f x == !(f a)) (b2 :: t2) := by
        have ha : (f a == !(f a)) = false := by cases f a <;> rfl
        simp [List.countP_cons, ha]
      rw [c1, c2]
      have hlen : (a :: b2 :: t2).length = (b2 :: t2).length + 1 := rfl
      by_cases ho : (b2 :: t2).length % 2 = 1
      · have hf : ¬ ((a :: b2 :: t2).length % 2 = 1) := by omega
        simp only [ho, ite_true] at ihn
        simp only [hf, ite_false]
        omega
      · have hf : (a :: b2 :: t2).length % 2 = 1 := by omega
        simp only [ho, ite_false] at ihn
        simp only [hf, ite_true]
        omega

-- Alternating-list last-value lemma (pure list).
private theorem alternating_last {α : Type*} (f : α → Bool) :
    ∀ (l : List α), List.IsChain (fun a b => f a ≠ f b) l →
    ∀ (b : Bool), l.head?.map f = some b →
    l.getLast?.map f = some (if l.length % 2 = 1 then b else !b) := by
  intro l
  induction l with
  | nil => intro h b hb; nomatch hb
  | cons a t ih =>
    intro h b hb
    have hb2 : f a = b := Option.some_inj.mp hb
    subst hb2
    cases t with
    | nil => simp
    | cons b2 t2 =>
      have htail : List.IsChain (fun a b => f a ≠ f b) (b2 :: t2) :=
        (List.isChain_cons_cons.mp h).2
      have hhead : (b2 :: t2).head?.map f = some (f b2) := rfl
      have ihn := ih htail (f b2) hhead
      have hrel : f a ≠ f b2 := (List.isChain_cons_cons.mp h).1
      have hlast : (a :: b2 :: t2).getLast? = (b2 :: t2).getLast? := by simp
      rw [hlast, ihn]
      have hflip : f b2 = !(f a) := by
        cases hf : f a <;> cases hg : f b2 <;> simp_all
      rw [hflip]
      have hlen : (a :: b2 :: t2).length = (b2 :: t2).length + 1 := rfl
      by_cases ho : (b2 :: t2).length % 2 = 1
      · have hf : ¬ ((a :: b2 :: t2).length % 2 = 1) := by omega
        have ho' : (t2.length + 1) % 2 = 1 := ho
        have hf' : ¬ ((t2.length + 1 + 1) % 2 = 1) := hf
        simp [ho', hf']
      · have hf : (a :: b2 :: t2).length % 2 = 1 := by omega
        have ho' : ¬ ((t2.length + 1) % 2 = 1) := ho
        have hf' : (t2.length + 1 + 1) % 2 = 1 := hf
        simp [ho', hf']

-- First edge (head?) of a walk contains the start vertex.
private theorem walk_first_edge_mem {V : Type*} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (e : Sym2 V) (h : p.edges.head? = some e) : u ∈ e := by
  cases p with
  | nil => simp [SimpleGraph.Walk.edges_nil] at h
  | cons hadj q =>
    rw [SimpleGraph.Walk.edges_cons] at h
    have h2 := Option.some_inj.mp h
    subst h2
    exact Sym2.mem_mk_left _ _

-- Last edge of a walk (as Option) contains the endpoint.
private theorem walk_end_mem_last_edge {V : Type*} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (e : Sym2 V)
    (h : p.edges.getLast? = some e) : v ∈ e := by
  induction p generalizing e with
  | nil => simp [SimpleGraph.Walk.edges_nil] at h
  | cons hadj q ih =>
    rw [SimpleGraph.Walk.edges_cons] at h
    cases hq : q.edges with
    | nil =>
      rw [hq] at h
      have h2 := Option.some_inj.mp h
      subst h2
      have hlen : q.length = 0 := by
        rw [← SimpleGraph.Walk.length_edges, hq]; rfl
      have heq := q.eq_of_length_eq_zero hlen
      subst heq
      exact Sym2.mem_mk_right _ _
    | cons e2 es =>
      have hqq : (e2 :: es).getLast? = q.edges.getLast? := by rw [hq]
      rw [hq, List.getLast?_cons_cons] at h
      exact ih e (hqq ▸ h)

-- The augmented edge set has one more edge than M.
private theorem aug_card {V : Type*} [DecidableEq (Sym2 V)] (G : SimpleGraph V)
    (M : Finset (Sym2 V))
    {u v : V} (p : G.Walk u v)
    (hEnodup : p.edges.Nodup)
    (hchain : List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges)
    (hfirst : p.edges.head?.map (fun e => decide (e ∈ M)) = some false)
    (hlast : p.edges.getLast?.map (fun e => decide (e ∈ M)) = some false) :
    ((M \ p.edges.toFinset) ∪ (p.edges.toFinset.filter (· ∉ M))).card
      = M.card + 1 := by
  have key : ∀ a b : Sym2 V, ((a ∈ M) ≠ (b ∈ M)) →
      ((fun e => decide (e ∈ M)) a ≠ (fun e => decide (e ∈ M)) b) := by
    intro a b h hcon
    change decide (a ∈ M) = decide (b ∈ M) at hcon
    cases Decidable.em (a ∈ M) with
    | inl ha =>
      cases Decidable.em (b ∈ M) with
      | inl hb => exact h (propext (iff_of_true ha hb))
      | inr hb =>
        rw [decide_eq_true ha, decide_eq_false hb] at hcon
        exact Bool.noConfusion hcon
    | inr ha =>
      cases Decidable.em (b ∈ M) with
      | inl hb =>
        rw [decide_eq_false ha, decide_eq_true hb] at hcon
        exact Bool.noConfusion hcon
      | inr hb => exact h (propext (iff_of_false ha hb))
  have hchainf : List.IsChain
      (fun a b => (fun e => decide (e ∈ M)) a ≠ (fun e => decide (e ∈ M)) b)
      p.edges := hchain.imp key
  have hodd : p.edges.length % 2 = 1 := by
    by_contra hcon
    have hLast := alternating_last (fun e => decide (e ∈ M)) p.edges hchainf
      false hfirst
    rw [hlast, ite_eq_right hcon] at hLast
    simp at hLast
  have hcount := alternating_counts (fun e => decide (e ∈ M)) p.edges hchainf
    false hfirst
  simp only [hodd, ite_true] at hcount
  have hA : (p.edges.toFinset.filter (· ∈ M)).card =
      p.edges.countP (fun e => decide (e ∈ M) == true) := by
    rw [List.countP_eq_length_filter]
    have h1 : (p.edges.filter (fun e => decide (e ∈ M) == true)).toFinset =
        p.edges.toFinset.filter (· ∈ M) := by
      rw [List.toFinset_filter]
      apply Finset.filter_congr
      intro x _
      by_cases hx : x ∈ M <;> simp_all
    rw [← h1, List.toFinset_card_of_nodup]
    exact List.Sublist.nodup List.filter_sublist hEnodup
  have hB : (p.edges.toFinset.filter (· ∉ M)).card =
      p.edges.countP (fun e => decide (e ∈ M) == false) := by
    rw [List.countP_eq_length_filter]
    have h1 : (p.edges.filter (fun e => decide (e ∈ M) == false)).toFinset =
        p.edges.toFinset.filter (· ∉ M) := by
      rw [List.toFinset_filter]
      apply Finset.filter_congr
      intro x _
      by_cases hx : x ∈ M <;> simp_all
    rw [← h1, List.toFinset_card_of_nodup]
    exact List.Sublist.nodup List.filter_sublist hEnodup
  have hAE : p.edges.toFinset ∩ M = p.edges.toFinset.filter (· ∈ M) :=
    Finset.filter_mem_eq_inter.symm
  have hdisj : Disjoint (M \ p.edges.toFinset)
      (p.edges.toFinset.filter (· ∉ M)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_filter.mp hb).2 (Finset.mem_sdiff.mp ha).1
  have hle : (p.edges.toFinset ∩ M).card ≤ M.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hAEc : (p.edges.toFinset ∩ M).card =
      (p.edges.toFinset.filter (· ∈ M)).card := by rw [hAE]
  simp only [Bool.not_false] at hcount
  rw [← hA, ← hB] at hcount
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff]
  omega

-- Forward direction: a maximum matching has no augmenting path.
private theorem berge_forward {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hmax : ∀ (M' : Finset (Sym2 V)),
      (∀ e ∈ M', e ∈ G.edgeSet) →
      (∀ e₁ ∈ M', ∀ e₂ ∈ M', e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) →
      M'.card ≤ M.card) :
    ¬ ∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
      p.support.Nodup ∧ (∀ e ∈ M, u ∉ e) ∧ (∀ e ∈ M, v ∉ e) ∧
      List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges ∧ 0 < p.length := by
  rintro ⟨u, v, hne, p, hnodup, hexpu, hexpv, hchain, hpos⟩
  classical
  obtain ⟨w, hadj, q, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne p
  have hEnodup : (SimpleGraph.Walk.cons hadj q).edges.Nodup :=
    SimpleGraph.Walk.edges_nodup_of_support_nodup hnodup
  have hfirst0 : s(u, w) ∉ M := by
    intro hcon
    exact absurd (Sym2.mem_mk_left u w) (hexpu _ hcon)
  have hfirst : (SimpleGraph.Walk.cons hadj q).edges.head?.map (fun e => decide (e ∈ M))
      = some false := by
    have hdec : decide (s(u, w) ∈ M) = false := decide_eq_false hfirst0
    simp [SimpleGraph.Walk.edges_cons, hdec]
  have hne_list : (SimpleGraph.Walk.cons hadj q).edges ≠ [] := by
    simp [SimpleGraph.Walk.edges_cons]
  have hne_opt : (SimpleGraph.Walk.cons hadj q).edges.getLast? ≠ none := by
    intro hcon
    rw [List.getLast?_eq_none_iff] at hcon
    exact hne_list hcon
  obtain ⟨e₁, he₁⟩ := Option.ne_none_iff_exists'.mp hne_opt
  have he₁nm : e₁ ∉ M := fun hcon =>
    absurd (walk_end_mem_last_edge G (SimpleGraph.Walk.cons hadj q) e₁ he₁) (hexpv e₁ hcon)
  have hlast : (SimpleGraph.Walk.cons hadj q).edges.getLast?.map (fun e => decide (e ∈ M))
      = some false := by
    simp only [he₁, Option.map_some, decide_eq_false he₁nm]
  have hcard := aug_card G M (SimpleGraph.Walk.cons hadj q) hEnodup hchain hfirst hlast
  have hM'G : ∀ e ∈ (M \ (SimpleGraph.Walk.cons hadj q).edges.toFinset) ∪
      ((SimpleGraph.Walk.cons hadj q).edges.toFinset.filter (· ∉ M)), e ∈ G.edgeSet := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · exact hG e (Finset.mem_sdiff.mp he).1
    · exact (SimpleGraph.Walk.cons hadj q).edges_subset_edgeSet
        (List.mem_toFinset.mp (Finset.mem_filter.mp he).1)
  have hM'm := aug_matching G M hM (SimpleGraph.Walk.cons hadj q) hnodup hexpu hexpv hchain
  have hle := hmax _ hM'G hM'm
  omega

-- A single G-edge between two M-exposed vertices is an M-augmenting path
-- (first step toward the backward direction).
private theorem aug_single_edge {V : Type*} (G : SimpleGraph V) (M : Finset (Sym2 V))
    {a b : V} (hadj : G.Adj a b) (hne : a ≠ b)
    (hexpa : ∀ e ∈ M, a ∉ e) (hexpb : ∀ e ∈ M, b ∉ e) :
    ∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
      p.support.Nodup ∧ (∀ e ∈ M, u ∉ e) ∧ (∀ e ∈ M, v ∉ e) ∧
      List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges ∧ 0 < p.length := by
  refine ⟨a, b, hne, hadj.toWalk, ?_, hexpa, hexpb, ?_, ?_⟩
  · simp [hadj.support_toWalk, hne]
  · rw [hadj.edges_toWalk]
    exact List.isChain_singleton _
  · rw [hadj.length_toWalk]
    decide

private theorem mem_biUnion_toFinset {V : Type*} [DecidableEq V]
    (M : Finset (Sym2 V)) (v : V) :
    v ∈ M.biUnion Sym2.toFinset ↔ ∃ e ∈ M, v ∈ e := by
  simp only [Finset.mem_biUnion, Sym2.mem_toFinset]

private theorem card_covered {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (M : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) :
    (M.biUnion Sym2.toFinset).card = 2 * M.card := by
  have hdisj : (↑M : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e₁ he₁ e₂ he₂ hne
    rw [Finset.mem_coe] at he₁ he₂
    apply Finset.disjoint_left.mpr
    intro a ha1 ha2
    rw [Sym2.mem_toFinset] at ha1 ha2
    exact (hM e₁ he₁ e₂ he₂ hne a ha1) ha2
  have h2 : ∀ e ∈ M, (e.toFinset).card = 2 := by
    intro e he
    exact Sym2.card_toFinset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeSet (hG e he))
  calc (M.biUnion Sym2.toFinset).card
      = ∑ _u ∈ M, (_u.toFinset).card := Finset.card_biUnion hdisj
    _ = ∑ _u ∈ M, 2 := Finset.sum_congr rfl h2
    _ = 2 * M.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

private def mateSet {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq (Sym2 V)] (M : Finset (Sym2 V)) (v : V) : Finset V :=
  Finset.univ.filter (fun w => s(v, w) ∈ M)

private theorem mem_mateSet {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq (Sym2 V)] (M : Finset (Sym2 V)) (v w : V) :
    w ∈ mateSet M v ↔ s(v, w) ∈ M := by
  simp only [mateSet, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem card_mateSet_le_one {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq (Sym2 V)] (G : SimpleGraph V) (M : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (v : V) : (mateSet M v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro w1 hw1 w2 hw2
  rw [mem_mateSet] at hw1 hw2
  have heq : s(v, w1) = s(v, w2) := by
    by_contra hne
    exact (hM s(v, w1) hw1 s(v, w2) hw2 hne v
      (Sym2.mem_mk_left v w1)) (Sym2.mem_mk_left v w2)
  have hmem : w1 ∈ s(v, w2) := by
    rw [← heq]
    exact Sym2.mem_mk_right v w1
  rw [Sym2.mem_iff] at hmem
  rcases hmem with h1 | h2
  · exfalso
    rw [h1] at hw1
    have hdiag : (s(v, v)).IsDiag := Sym2.mk_isDiag_iff.mpr rfl
    exact (G.not_isDiag_of_mem_edgeSet (hG s(v, v) hw1)) hdiag
  · exact h2

private theorem mateSet_nonempty_iff {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq (Sym2 V)] (M : Finset (Sym2 V)) (v : V) :
    (mateSet M v).Nonempty ↔ ∃ e ∈ M, v ∈ e := by
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_mateSet] at hw
    exact ⟨s(v, w), hw, Sym2.mem_mk_left v w⟩
  · rintro ⟨e, heM, hve⟩
    obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e
    have hab2 : s(a, b) = e := hab
    subst hab2
    rw [Sym2.mem_iff] at hve
    rcases hve with h1 | h2
    · have heM2 : s(v, b) ∈ M := by
        rw [← h1] at heM
        exact heM
      exact ⟨b, by rw [mem_mateSet]; exact heM2⟩
    · have heM2 : s(a, v) ∈ M := by
        rw [← h2] at heM
        exact heM
      exact ⟨a, by rw [mem_mateSet, Sym2.eq_swap]; exact heM2⟩

private theorem fromEdgeSet_symmDiff_le {V : Type*} [DecidableEq (Sym2 V)]
    (G : SimpleGraph V) (M N : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hNG : ∀ e ∈ N, e ∈ G.edgeSet) :
    SimpleGraph.fromEdgeSet (↑(M ∆ N) : Set (Sym2 V)) ≤ G := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  intro e he
  rw [SimpleGraph.edgeSet_fromEdgeSet] at he
  rw [Set.mem_sdiff, Finset.mem_coe, Finset.mem_symmDiff] at he
  rcases he with ⟨hmn, _⟩
  rcases hmn with ⟨heM, _⟩ | ⟨heN, _⟩
  · exact hG e heM
  · exact hNG e heN

private theorem neighborFinset_symmDiff {V : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq (Sym2 V)] (G : SimpleGraph V)
    (M N : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hNG : ∀ e ∈ N, e ∈ G.edgeSet) (v : V) :
    (SimpleGraph.fromEdgeSet (↑(M ∆ N) : Set (Sym2 V))).neighborFinset v
      = mateSet M v ∆ mateSet N v := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.fromEdgeSet_adj,
    Finset.mem_coe, Finset.mem_symmDiff, mem_mateSet]
  constructor
  · rintro ⟨hmn, _⟩
    exact hmn
  · intro h
    refine ⟨h, ?_⟩
    rcases h with ⟨heM, _⟩ | ⟨heN, _⟩
    · have hnd := G.not_isDiag_of_mem_edgeSet (hG s(v, w) heM)
      rwa [Sym2.mk_isDiag_iff] at hnd
    · have hnd := G.not_isDiag_of_mem_edgeSet (hNG s(v, w) heN)
      rwa [Sym2.mk_isDiag_iff] at hnd

private theorem odd_symmDiff_card {V : Type*} [DecidableEq V]
    (A B : Finset V) (hA : A.card ≤ 1) (hB : B.card ≤ 1) :
    Odd (A ∆ B).card ↔
      (A.Nonempty ∧ ¬ B.Nonempty) ∨ (B.Nonempty ∧ ¬ A.Nonempty) := by
  have hdisj : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    rw [Finset.mem_sdiff] at hx1 hx2
    exact hx1.2 hx2.1
  have hcard : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisj]
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  have hinter : (A ∩ B).card = (B ∩ A).card := by rw [Finset.inter_comm]
  have hA1 : A.Nonempty ↔ A.card = 1 := by
    constructor
    · intro h
      have hpos : 0 < A.card := Finset.card_pos.mpr h
      omega
    · intro h
      have hpos : 0 < A.card := by omega
      exact Finset.card_pos.mp hpos
  have hB1 : B.Nonempty ↔ B.card = 1 := by
    constructor
    · intro h
      have hpos : 0 < B.card := Finset.card_pos.mpr h
      omega
    · intro h
      have hpos : 0 < B.card := by omega
      exact Finset.card_pos.mp hpos
  have hsum : (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
    omega
  have hpar : Odd (A ∆ B).card ↔ Odd (A.card + B.card) := by
    rw [Nat.odd_iff, Nat.odd_iff]
    omega
  have hfin : Odd (A.card + B.card) ↔
      (A.card = 1 ∧ ¬ B.card = 1) ∨ (B.card = 1 ∧ ¬ A.card = 1) := by
    rw [Nat.odd_iff]
    omega
  rw [hA1, hB1]
  exact hpar.trans hfin

private theorem odd_degree_iff {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq (Sym2 V)] (G : SimpleGraph V)
    (M N : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hNG : ∀ e ∈ N, e ∈ G.edgeSet)
    (hNM : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (v : V) :
    Odd ((SimpleGraph.fromEdgeSet (↑(M ∆ N) : Set (Sym2 V))).degree v) ↔
      ((∃ e ∈ M, v ∈ e) ∧ ¬ ∃ e ∈ N, v ∈ e) ∨
        ((∃ e ∈ N, v ∈ e) ∧ ¬ ∃ e ∈ M, v ∈ e) := by
  have hleM := card_mateSet_le_one G M hG hM v
  have hleN := card_mateSet_le_one G N hNG hNM v
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_symmDiff G M N hG hNG v,
    odd_symmDiff_card _ _ hleM hleN,
    mateSet_nonempty_iff M v, mateSet_nonempty_iff N v]

private theorem exists_reachable_odd_of_odd {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x : V)
    (hodd : Odd (H.degree x)) :
    ∃ y : V, y ≠ x ∧ Odd (H.degree y) ∧ H.Reachable x y := by
  classical
  have hx : x ∈ (H.connectedComponentMk x).supp :=
    SimpleGraph.ConnectedComponent.mem_supp_iff _ x |>.mpr rfl
  have hsub_x : H.neighborSet x ⊆ (H.connectedComponentMk x).supp := by
    intro w hw
    rw [SimpleGraph.mem_neighborSet] at hw
    exact (H.connectedComponentMk x).mem_supp_of_adj_mem_supp hx hw
  have hdeg_x : (H.induce (H.connectedComponentMk x).supp).degree ⟨x, hx⟩ =
      H.degree x :=
    SimpleGraph.degree_induce_of_neighborSet_subset (v := ⟨x, hx⟩) hsub_x
  have hodd_x : Odd ((H.induce (H.connectedComponentMk x).supp).degree
      ⟨x, hx⟩) := by
    rw [hdeg_x]
    exact hodd
  obtain ⟨y', hne', hodd'⟩ :=
    SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree
      (H.induce (H.connectedComponentMk x).supp) ⟨x, hx⟩ hodd_x
  obtain ⟨y, hy⟩ := y'
  have hne : y ≠ x := fun h => hne' (Subtype.ext h)
  have hsub_y : H.neighborSet y ⊆ (H.connectedComponentMk x).supp := by
    intro w hw
    rw [SimpleGraph.mem_neighborSet] at hw
    exact (H.connectedComponentMk x).mem_supp_of_adj_mem_supp hy hw
  have hdeg_y : (H.induce (H.connectedComponentMk x).supp).degree ⟨y, hy⟩ =
      H.degree y :=
    SimpleGraph.degree_induce_of_neighborSet_subset (v := ⟨y, hy⟩) hsub_y
  have hodd_y : Odd (H.degree y) := by
    rw [← hdeg_y]
    exact hodd'
  have hreach : H.Reachable x y :=
    (H.connectedComponentMk x).reachable_of_mem_supp hx hy
  exact ⟨y, hne, hodd_y, hreach⟩

private theorem isChain_of_mem_symmDiff {V : Type*} [DecidableEq (Sym2 V)]
    {H G : SimpleGraph V} (hle : H ≤ G)
    (M N : Finset (Sym2 V))
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hNM : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    {x y : V} (q : H.Walk x y) (hpath : q.IsPath)
    (hmem : ∀ e ∈ q.edges, e ∈ M ∆ N) :
    List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M))
      (q.mapLe hle).edges := by
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  revert hpath hmem
  induction q with
  | nil =>
    intro hpath hmem
    rw [SimpleGraph.Walk.edges_nil]
    exact List.IsChain.nil
  | @cons u v w hadj q' ih =>
    intro hpath hmem
    have hpath' : q'.IsPath := SimpleGraph.Walk.IsPath.of_cons hpath
    have hmem' : ∀ e ∈ q'.edges, e ∈ M ∆ N := by
      intro e he
      apply hmem
      rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons.mpr (Or.inr he)
    have hih := ih hpath' hmem'
    cases he : q'.edges with
    | nil =>
      rw [SimpleGraph.Walk.edges_cons, he]
      exact List.isChain_singleton _
    | cons e2 rest =>
      rw [he] at hih
      have hhead : q'.edges.head? = some e2 := by
        rw [he]
        rfl
      have hve2 : v ∈ e2 := walk_first_edge_mem H q' e2 hhead
      have hvs : v ∈ s(u, v) := Sym2.mem_mk_right u v
      have hnodup := hpath.isTrail.edges_nodup
      rw [SimpleGraph.Walk.edges_cons, he] at hnodup
      have hne : s(u, v) ≠ e2 := by
        intro hcon
        have hmem2 : s(u, v) ∈ e2 :: rest := by
          rw [← hcon]
          exact List.mem_cons.mpr (Or.inl rfl)
        exact (List.nodup_cons.mp hnodup).1 hmem2
      have hs_mem : s(u, v) ∈ (SimpleGraph.Walk.cons hadj q').edges := by
        rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons.mpr (Or.inl rfl)
      have he2_mem : e2 ∈ (SimpleGraph.Walk.cons hadj q').edges := by
        rw [SimpleGraph.Walk.edges_cons, he]
        exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      have hsMN := hmem s(u, v) hs_mem
      have he2MN := hmem e2 he2_mem
      have hR : (s(u, v) ∈ M) ≠ (e2 ∈ M) := by
        intro heq
        have hiff : (s(u, v) ∈ M) ↔ (e2 ∈ M) := iff_of_eq heq
        rw [Finset.mem_symmDiff] at hsMN he2MN
        rcases hsMN with ⟨hsM, hsN⟩ | ⟨hsN, hsM⟩
        · have he2M : e2 ∈ M := hiff.mp hsM
          rcases he2MN with ⟨_, _⟩ | ⟨_, he2M'⟩
          · exact (hM s(u, v) hsM e2 he2M hne v hvs) hve2
          · exact he2M' he2M
        · have he2nM : e2 ∉ M := fun he => hsM (hiff.mpr he)
          rcases he2MN with ⟨he2M, _⟩ | ⟨he2N, _⟩
          · exact he2nM he2M
          · exact (hNM s(u, v) hsN e2 he2N hne v hvs) hve2
      rw [SimpleGraph.Walk.edges_cons, he]
      exact List.IsChain.cons_cons hR hih

private theorem aug_of_path {V : Type*} [DecidableEq (Sym2 V)]
    (G : SimpleGraph V)
    (M N : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hNG : ∀ e ∈ N, e ∈ G.edgeSet)
    (hNM : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    {x y : V} (hne : x ≠ y)
    (q : (SimpleGraph.fromEdgeSet (↑(M ∆ N) : Set (Sym2 V))).Walk x y)
    (hpath : q.IsPath)
    (hexpx : ∀ e ∈ M, x ∉ e) (hexpy : ∀ e ∈ M, y ∉ e) :
    ∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
      p.support.Nodup ∧ (∀ e ∈ M, u ∉ e) ∧ (∀ e ∈ M, v ∉ e) ∧
        List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges ∧
        0 < p.length := by
  have hle := fromEdgeSet_symmDiff_le G M N hG hNG
  have hmem : ∀ e ∈ q.edges, e ∈ M ∆ N := by
    intro e he
    have hedge : e ∈ (SimpleGraph.fromEdgeSet
      (↑(M ∆ N) : Set (Sym2 V))).edgeSet := q.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hedge
    rw [Set.mem_sdiff, Finset.mem_coe] at hedge
    exact hedge.1
  refine ⟨x, y, hne, q.mapLe hle, ?_, hexpx, hexpy, ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_mapLe_eq_support]
    exact hpath.support_nodup
  · exact isChain_of_mem_symmDiff hle M N hM hNM q hpath hmem
  · have hpos : 0 < q.length := by
      by_contra hcon
      have h0 : q.length = 0 := by omega
      exact hne (SimpleGraph.Walk.eq_of_length_eq_zero h0)
    have hlen := SimpleGraph.Walk.length_mapLe (p := q) (h := hle)
    omega

private theorem berge_backward {V : Type*} [Finite V] (G : SimpleGraph V)
    (M : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hnoaug : ¬ ∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
      p.support.Nodup ∧ (∀ e ∈ M, u ∉ e) ∧ (∀ e ∈ M, v ∉ e) ∧
        List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges ∧
        0 < p.length)
    (N : Finset (Sym2 V))
    (hNG : ∀ e ∈ N, e ∈ G.edgeSet)
    (hNM : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) :
    N.card ≤ M.card := by
  classical
  let : Fintype V := Fintype.ofFinite V
  by_contra hcon
  have hlt : M.card < N.card := lt_of_not_ge hcon
  have hCM := card_covered G M hG hM
  have hCN := card_covered G N hNG hNM
  set A := (N.biUnion Sym2.toFinset) \ (M.biUnion Sym2.toFinset) with hA
  set B := (M.biUnion Sym2.toFinset) \ (N.biUnion Sym2.toFinset) with hB
  have hAB : B.card < A.card := by
    have h1 := Finset.card_sdiff_add_card_inter
      (M.biUnion Sym2.toFinset) (N.biUnion Sym2.toFinset)
    have h2 := Finset.card_sdiff_add_card_inter
      (N.biUnion Sym2.toFinset) (M.biUnion Sym2.toFinset)
    have hinter : ((M.biUnion Sym2.toFinset) ∩ (N.biUnion Sym2.toFinset)).card
        = ((N.biUnion Sym2.toFinset) ∩ (M.biUnion Sym2.toFinset)).card := by
      rw [Finset.inter_comm]
    rw [hA, hB]
    omega
  have hex : ∀ x ∈ A, ∃ y ∈ B,
      (SimpleGraph.fromEdgeSet (↑(M ∆ N) : Set (Sym2 V))).Reachable x y := by
    intro x hx
    rw [hA, Finset.mem_sdiff, mem_biUnion_toFinset,
      mem_biUnion_toFinset] at hx
    have hodd : Odd ((SimpleGraph.fromEdgeSet
        (↑(M ∆ N) : Set (Sym2 V))).degree x) := by
      rw [odd_degree_iff G M N hG hM hNG hNM x]
      exact Or.inr ⟨hx.1, hx.2⟩
    obtain ⟨y, hne, hodd_y, hreach⟩ :=
      exists_reachable_odd_of_odd
        (SimpleGraph.fromEdgeSet (↑(M ∆ N) : Set (Sym2 V))) x hodd
    rw [odd_degree_iff G M N hG hM hNG hNM y] at hodd_y
    rcases hodd_y with ⟨hexM, hexN⟩ | ⟨hexN, hexM⟩
    · have hyB : y ∈ B := by
        simp only [hB, Finset.mem_sdiff, mem_biUnion_toFinset]
        exact ⟨hexM, hexN⟩
      exact ⟨y, hyB, hreach⟩
    · exfalso
      have hexpx : ∀ e ∈ M, x ∉ e := fun e he hxe => hx.2 ⟨e, he, hxe⟩
      have hexpy : ∀ e ∈ M, y ∉ e := fun e he hye => hexM ⟨e, he, hye⟩
      obtain ⟨q, hqpath⟩ := hreach.exists_isPath
      exact hnoaug (aug_of_path G M N hG hM hNG hNM hne.symm q hqpath
        hexpx hexpy)
  choose f hf using hex
  have hinj : Function.Injective
      (fun a : ↥A => (⟨f a.val a.property, (hf a.val a.property).1⟩ : ↥B)) := by
    intro a b hab
    have heq : f a.val a.property = f b.val b.property :=
      congrArg Subtype.val hab
    apply Subtype.ext
    show a.val = b.val
    by_contra hne2
    have hr1 := (hf a.val a.property).2
    have hr2 := (hf b.val b.property).2
    rw [heq] at hr1
    have hreach2 : (SimpleGraph.fromEdgeSet
        (↑(M ∆ N) : Set (Sym2 V))).Reachable a.val b.val :=
      hr1.trans hr2.symm
    obtain ⟨q, hqpath⟩ := hreach2.exists_isPath
    have haA' : a.val ∈ (N.biUnion Sym2.toFinset) \
        (M.biUnion Sym2.toFinset) := a.property
    have hbA' : b.val ∈ (N.biUnion Sym2.toFinset) \
        (M.biUnion Sym2.toFinset) := b.property
    rw [Finset.mem_sdiff, mem_biUnion_toFinset,
      mem_biUnion_toFinset] at haA' hbA'
    have hexpa : ∀ e ∈ M, a.val ∉ e :=
      fun e he h => haA'.2 ⟨e, he, h⟩
    have hexpb : ∀ e ∈ M, b.val ∉ e :=
      fun e he h => hbA'.2 ⟨e, he, h⟩
    exact hnoaug (aug_of_path G M N hG hM hNG hNM hne2 q hqpath
      hexpa hexpb)
  have hle2 : Fintype.card ↥A ≤ Fintype.card ↥B :=
    Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe, Fintype.card_coe] at hle2
  omega

/-- A `Finset` matching as a `SimpleGraph.Subgraph`: vertices are the covered
vertices, adjacency is edge membership. -/
private def subgraphOfFinset {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) : G.Subgraph where
  verts := {v | ∃ e ∈ M, v ∈ e}
  Adj v w := s(v, w) ∈ M
  adj_sub {v w} h := (SimpleGraph.mem_edgeSet G).mp (hG _ h)
  edge_vert {v w} h := ⟨s(v, w), h, Sym2.mem_mk_left v w⟩
  symm := ⟨fun a b h => by rwa [Sym2.eq_swap]⟩

/-- The edge set of `subgraphOfFinset` is the coercion of `M`. -/
private theorem edgeSet_subgraphOfFinset {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) :
    (subgraphOfFinset G M hG).edgeSet = (↑M : Set (Sym2 V)) := by
  ext e
  refine Sym2.ind (fun a b => ?_) e
  simp only [SimpleGraph.Subgraph.mem_edgeSet, Finset.mem_coe]
  rfl

private theorem mem_edgeSet_subgraphOfFinset {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) (e : Sym2 V) :
    e ∈ (subgraphOfFinset G M hG).edgeSet ↔ e ∈ M := by
  rw [edgeSet_subgraphOfFinset]
  rfl

private theorem mem_verts_subgraphOfFinset {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) (v : V) :
    v ∈ (subgraphOfFinset G M hG).verts ↔ ∃ e ∈ M, v ∈ e :=
  Iff.rfl

private theorem not_mem_verts_subgraphOfFinset {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) (v : V) :
    v ∉ (subgraphOfFinset G M hG).verts ↔ ∀ e ∈ M, v ∉ e := by
  simp [mem_verts_subgraphOfFinset]

private theorem ncard_edgeSet_subgraphOfFinset {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) :
    (subgraphOfFinset G M hG).edgeSet.ncard = M.card := by
  rw [edgeSet_subgraphOfFinset, Set.ncard_coe_finset]

/-- A `Finset` matching gives an `IsMatching` subgraph. -/
private theorem isMatching_subgraphOfFinset {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V))
    (hG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) :
    (subgraphOfFinset G M hG).IsMatching := by
  intro v hv
  rw [mem_verts_subgraphOfFinset] at hv
  obtain ⟨e, heM, hve⟩ := hv
  refine ⟨Sym2.Mem.other hve, ?_, ?_⟩
  · change s(v, Sym2.Mem.other hve) ∈ M
    rw [Sym2.other_spec hve]
    exact heM
  · intro w hw
    have hwsM : s(v, w) ∈ M := hw
    have heq : s(v, w) = e := by
      by_contra hne
      exact (hM e heM s(v, w) hwsM (Ne.symm hne) v hve) (Sym2.mem_mk_left v w)
    have hne : v ≠ w := by
      have hadj : G.Adj v w :=
        (SimpleGraph.mem_edgeSet G).mp (hG _ hwsM)
      exact hadj.ne
    have hwmem : w ∈ e := heq ▸ Sym2.mem_mk_right v w
    rw [← Sym2.other_spec hve] at hwmem
    rcases Sym2.mem_iff.mp hwmem with h | h
    · exact absurd h.symm hne
    · exact h

/-- A `Subgraph`'s edge set as a `Finset`, for `Finite` vertex types. -/
private noncomputable def finsetOfSubgraph {V : Type*} [Finite V]
    (G : SimpleGraph V) (M : G.Subgraph) : Finset (Sym2 V) :=
  haveI : Finite (Sym2 V) := Quot.finite _
  (Set.finite_univ.subset (Set.subset_univ M.edgeSet)).toFinset

private theorem mem_finsetOfSubgraph {V : Type*} [Finite V] (G : SimpleGraph V)
    (M : G.Subgraph) (e : Sym2 V) :
    e ∈ finsetOfSubgraph G M ↔ e ∈ M.edgeSet := by
  have : Finite (Sym2 V) := Quot.finite _
  exact Set.Finite.mem_toFinset _

private theorem card_finsetOfSubgraph {V : Type*} [Finite V] (G : SimpleGraph V)
    (M : G.Subgraph) :
    (finsetOfSubgraph G M).card = M.edgeSet.ncard := by
  have : Finite (Sym2 V) := Quot.finite _
  rw [Set.ncard_eq_toFinset_card M.edgeSet
    (Set.finite_univ.subset (Set.subset_univ M.edgeSet))]
  rfl

private theorem edge_mem_finsetOfSubgraph {V : Type*} [Finite V]
    (G : SimpleGraph V) (M : G.Subgraph) :
    ∀ e ∈ finsetOfSubgraph G M, e ∈ G.edgeSet := by
  intro e he
  rw [mem_finsetOfSubgraph] at he
  exact M.edgeSet_subset he

/-- An `IsMatching` subgraph gives a `Finset` matching. -/
private theorem matching_finsetOfSubgraph {V : Type*} [Finite V]
    (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching) :
    ∀ e₁ ∈ finsetOfSubgraph G M, ∀ e₂ ∈ finsetOfSubgraph G M,
      e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂ := by
  intro e₁ he₁ e₂ he₂ hne v hv1 hv2
  rw [mem_finsetOfSubgraph] at he₁ he₂
  obtain ⟨a, b⟩ := e₁
  obtain ⟨c, d⟩ := e₂
  rw [SimpleGraph.Subgraph.mem_edgeSet] at he₁ he₂
  rcases Sym2.mem_iff.mp hv1 with rfl | rfl
  · rcases Sym2.mem_iff.mp hv2 with h | h
    · subst h
      have hbd : b = d := hM.eq_of_adj_left he₁ he₂
      subst hbd
      exact hne rfl
    · subst h
      have hbc : b = c := hM.eq_of_adj_left he₁ (M.adj_symm he₂)
      subst hbc
      exact hne Sym2.eq_swap
  · rcases Sym2.mem_iff.mp hv2 with h | h
    · subst h
      have hac : a = d := hM.eq_of_adj_left (M.adj_symm he₁) he₂
      subst hac
      exact hne Sym2.eq_swap
    · subst h
      have hac : a = c :=
        hM.eq_of_adj_left (M.adj_symm he₁) (M.adj_symm he₂)
      subst hac
      exact hne rfl

/-- Exposed vertices agree: `u ∉ M.verts` iff no `Finset` edge covers `u`. -/
private theorem not_mem_verts_iff_forall_not_mem {V : Type*} [Finite V]
    (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching) (u : V) :
    u ∉ M.verts ↔ ∀ e ∈ finsetOfSubgraph G M, u ∉ e := by
  constructor
  · intro hu e he hmem
    rw [mem_finsetOfSubgraph] at he
    exact hu (M.mem_verts_of_mem_edge he hmem)
  · intro hall hu
    obtain ⟨w, hvw, -⟩ := hM hu
    have hmem : s(u, w) ∈ finsetOfSubgraph G M := by
      rw [mem_finsetOfSubgraph]
      exact SimpleGraph.Subgraph.mem_edgeSet.mpr hvw
    exact hall s(u, w) hmem (Sym2.mem_mk_left u w)

/-- Alternating predicates agree between `finsetOfSubgraph` and `edgeSet`. -/
private theorem isChain_finsetOfSubgraph_iff {V : Type*} [Finite V]
    (G : SimpleGraph V) (M : G.Subgraph) (l : List (Sym2 V)) :
    List.IsChain (fun e₁ e₂ => (e₁ ∈ finsetOfSubgraph G M) ≠ (e₂ ∈ finsetOfSubgraph G M)) l ↔
    List.IsChain (fun e₁ e₂ => (e₁ ∈ M.edgeSet) ≠ (e₂ ∈ M.edgeSet)) l := by
  apply List.IsChain.iff
  intro a b
  rw [mem_finsetOfSubgraph, mem_finsetOfSubgraph]

/-- Alternating predicates agree between `M` and `subgraphOfFinset`. -/
private theorem isChain_subgraphOfFinset_iff {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) (l : List (Sym2 V)) :
    List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) l ↔
    List.IsChain
      (fun e₁ e₂ => (e₁ ∈ (subgraphOfFinset G M hG).edgeSet) ≠
        (e₂ ∈ (subgraphOfFinset G M hG).edgeSet)) l := by
  apply List.IsChain.iff
  intro a b
  rw [mem_edgeSet_subgraphOfFinset, mem_edgeSet_subgraphOfFinset]

/-- Augmenting paths agree between `finsetOfSubgraph` and the subgraph. -/
private theorem aug_exists_finsetOfSubgraph_iff {V : Type*} [Finite V]
    (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching) :
    (∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
      p.support.Nodup ∧ (∀ e ∈ finsetOfSubgraph G M, u ∉ e) ∧
        (∀ e ∈ finsetOfSubgraph G M, v ∉ e) ∧
        List.IsChain
          (fun e₁ e₂ => (e₁ ∈ finsetOfSubgraph G M) ≠ (e₂ ∈ finsetOfSubgraph G M))
          p.edges ∧ 0 < p.length) ↔
    (∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
      p.support.Nodup ∧ u ∉ M.verts ∧ v ∉ M.verts ∧
        List.IsChain (fun e₁ e₂ => (e₁ ∈ M.edgeSet) ≠ (e₂ ∈ M.edgeSet)) p.edges ∧
        0 < p.length) := by
  constructor
  · rintro ⟨u, v, hne, p, hnodup, hexpu, hexpv, hchain, hpos⟩
    refine ⟨u, v, hne, p, hnodup, ?_, ?_, ?_, hpos⟩
    · exact (not_mem_verts_iff_forall_not_mem G M hM u).mpr hexpu
    · exact (not_mem_verts_iff_forall_not_mem G M hM v).mpr hexpv
    · exact (isChain_finsetOfSubgraph_iff G M p.edges).mp hchain
  · rintro ⟨u, v, hne, p, hnodup, hexpu, hexpv, hchain, hpos⟩
    refine ⟨u, v, hne, p, hnodup, ?_, ?_, ?_, hpos⟩
    · exact (not_mem_verts_iff_forall_not_mem G M hM u).mp hexpu
    · exact (not_mem_verts_iff_forall_not_mem G M hM v).mp hexpv
    · exact (isChain_finsetOfSubgraph_iff G M p.edges).mpr hchain

/-- Augmenting paths agree between `M` and `subgraphOfFinset`. -/
private theorem aug_exists_subgraphOfFinset_iff {V : Type*} (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hG : ∀ e ∈ M, e ∈ G.edgeSet) :
    (∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
      p.support.Nodup ∧ (∀ e ∈ M, u ∉ e) ∧ (∀ e ∈ M, v ∉ e) ∧
        List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges ∧
        0 < p.length) ↔
    (∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
      p.support.Nodup ∧ u ∉ (subgraphOfFinset G M hG).verts ∧
        v ∉ (subgraphOfFinset G M hG).verts ∧
        List.IsChain
          (fun e₁ e₂ => (e₁ ∈ (subgraphOfFinset G M hG).edgeSet) ≠
            (e₂ ∈ (subgraphOfFinset G M hG).edgeSet)) p.edges ∧
        0 < p.length) := by
  constructor
  · rintro ⟨u, v, hne, p, hnodup, hexpu, hexpv, hchain, hpos⟩
    refine ⟨u, v, hne, p, hnodup, ?_, ?_, ?_, hpos⟩
    · exact (not_mem_verts_subgraphOfFinset G M hG u).mpr hexpu
    · exact (not_mem_verts_subgraphOfFinset G M hG v).mpr hexpv
    · exact (isChain_subgraphOfFinset_iff G M hG p.edges).mp hchain
  · rintro ⟨u, v, hne, p, hnodup, hexpu, hexpv, hchain, hpos⟩
    refine ⟨u, v, hne, p, hnodup, ?_, ?_, ?_, hpos⟩
    · exact (not_mem_verts_subgraphOfFinset G M hG u).mp hexpu
    · exact (not_mem_verts_subgraphOfFinset G M hG v).mp hexpv
    · exact (isChain_subgraphOfFinset_iff G M hG p.edges).mpr hchain

section
namespace MetaMathlibExt

/-- **Berge's lemma for matching subgraphs.** Let $G$ be a simple graph on a finite vertex set and
let $M$ be a matching subgraph of $G$, so that every vertex of $M$ is incident to exactly one
edge of $M$. Then $M$ has the maximum number of edges among all matching subgraphs of $G$ if and
only if there is no $M$-augmenting path: a path in $G$ of positive length between two distinct
vertices $u$ and $v$, neither of which is a vertex of $M$, whose consecutive edges alternate
between edges of $M$ and edges not in $M$. -/
theorem berge_general {V : Type*} [Finite V] (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching) :
    (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ↔
    ¬ ∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
      p.support.Nodup ∧ u ∉ M.verts ∧ v ∉ M.verts ∧
        List.IsChain (fun e₁ e₂ => (e₁ ∈ M.edgeSet) ≠ (e₂ ∈ M.edgeSet)) p.edges ∧
        0 < p.length := by
  have hGfin : ∀ e ∈ finsetOfSubgraph G M, e ∈ G.edgeSet :=
    edge_mem_finsetOfSubgraph G M
  have hMfin : ∀ e₁ ∈ finsetOfSubgraph G M, ∀ e₂ ∈ finsetOfSubgraph G M,
      e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂ :=
    matching_finsetOfSubgraph G M hM
  have hcard : (finsetOfSubgraph G M).card = M.edgeSet.ncard :=
    card_finsetOfSubgraph G M
  have finset_iff :
      (∀ N : Finset (Sym2 V), (∀ e ∈ N, e ∈ G.edgeSet) →
        (∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) →
        N.card ≤ (finsetOfSubgraph G M).card) ↔
      ¬ ∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
        p.support.Nodup ∧ (∀ e ∈ finsetOfSubgraph G M, u ∉ e) ∧
          (∀ e ∈ finsetOfSubgraph G M, v ∉ e) ∧
          List.IsChain
            (fun e₁ e₂ => (e₁ ∈ finsetOfSubgraph G M) ≠
              (e₂ ∈ finsetOfSubgraph G M)) p.edges ∧ 0 < p.length := by
    constructor
    · intro hmax
      exact berge_forward _ _ hGfin hMfin hmax
    · intro hnoaug N hNG hNM
      exact berge_backward _ _ hGfin hMfin hnoaug N hNG hNM
  have max_iff :
      (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ↔
      (∀ N : Finset (Sym2 V), (∀ e ∈ N, e ∈ G.edgeSet) →
        (∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) →
        N.card ≤ (finsetOfSubgraph G M).card) := by
    constructor
    · intro hSub N hNG hNM
      have hle := hSub _ (isMatching_subgraphOfFinset G N hNG hNM)
      rw [ncard_edgeSet_subgraphOfFinset, ← hcard] at hle
      exact hle
    · intro hFin N' hN'
      have hle := hFin _ (edge_mem_finsetOfSubgraph G N')
        (matching_finsetOfSubgraph G N' hN')
      rw [card_finsetOfSubgraph G N', hcard] at hle
      exact hle
  have aug_iff := aug_exists_finsetOfSubgraph_iff G M hM
  rw [max_iff, ← aug_iff]
  exact finset_iff

set_option linter.unusedFintypeInType false in
/-- **Berge's lemma.** Let $G$ be a simple graph on a finite vertex set and let $M$ be a matching
of $G$, that is, a finite set of edges of $G$ no two distinct members of which share a vertex.
Then $M$ has maximum cardinality among all matchings of $G$ if and only if there is no
$M$-augmenting path: a path in $G$ of positive length between two distinct vertices $u$ and $v$,
neither of which lies on an edge of $M$, whose consecutive edges alternate between edges of $M$
and edges not in $M$.

Proves `Wanted` entry `Berge`.

Source: Wikipedia, Berge's theorem, statement `berge-s1`,
https://en.wikipedia.org/wiki/Berge%27s_theorem.
-/
theorem Berge :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
      (M : Finset (Sym2 V)),
      (∀ e ∈ M, e ∈ G.edgeSet) →
      (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) →
      ((∀ (M' : Finset (Sym2 V)),
        (∀ e ∈ M', e ∈ G.edgeSet) →
        (∀ e₁ ∈ M', ∀ e₂ ∈ M', e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) →
        M'.card ≤ M.card) ↔
      ¬ ∃ (u v : V) (_ : u ≠ v) (p : G.Walk u v),
        p.support.Nodup ∧ (∀ e ∈ M, u ∉ e) ∧ (∀ e ∈ M, v ∉ e) ∧
        List.IsChain (fun e₁ e₂ => (e₁ ∈ M) ≠ (e₂ ∈ M)) p.edges ∧ 0 < p.length) := by
  intro V inst G M hG hM
  have hSub : (subgraphOfFinset G M hG).IsMatching :=
    isMatching_subgraphOfFinset G M hG hM
  have hgen := berge_general (V := V) G _ hSub
  have max_iff' :
      (∀ M' : Finset (Sym2 V), (∀ e ∈ M', e ∈ G.edgeSet) →
        (∀ e₁ ∈ M', ∀ e₂ ∈ M', e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) →
        M'.card ≤ M.card) ↔
      (∀ M' : G.Subgraph, M'.IsMatching →
        M'.edgeSet.ncard ≤ (subgraphOfFinset G M hG).edgeSet.ncard) := by
    constructor
    · intro hFin N' hN'
      have hle := hFin _ (edge_mem_finsetOfSubgraph G N')
        (matching_finsetOfSubgraph G N' hN')
      rw [card_finsetOfSubgraph G N'] at hle
      rw [ncard_edgeSet_subgraphOfFinset G M hG]
      exact hle
    · intro hSub' N hNG hNM
      have hle := hSub' _ (isMatching_subgraphOfFinset G N hNG hNM)
      rw [ncard_edgeSet_subgraphOfFinset G N hNG,
        ncard_edgeSet_subgraphOfFinset G M hG] at hle
      exact hle
  have aug_iff' := aug_exists_subgraphOfFinset_iff G M hG
  rw [max_iff', aug_iff']
  exact hgen

end MetaMathlibExt
end
