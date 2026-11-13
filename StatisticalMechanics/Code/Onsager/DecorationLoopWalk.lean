/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationTransitionWalk
import Code.Onsager.DecorationCycleWeight










namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_walk_count_incident_edges
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (x : V) :
    p.edges.countP (fun edge ↦ x ∈ edge) =
      p.support.dropLast.count x + p.support.tail.count x := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
      rw [SimpleGraph.Walk.edges_cons,
        SimpleGraph.Walk.support_cons]
      simp only [List.countP_cons, List.tail_cons]
      rw [ih]
      rw [← p.cons_tail_support]
      simp only [List.dropLast_cons_cons, List.count_cons,
        List.tail_cons]
      have huvne : u ≠ v := huv.ne
      have hvune : v ≠ u := huv.ne.symm
      simp only [Sym2.mem_iff]
      by_cases hxu : x = u
      · subst x
        simp [huvne, hvune]
        omega
      · by_cases hxv : x = v
        · subst x
          simp [huvne, hvune]
          omega
        · have hux : u ≠ x := fun h ↦ hxu h.symm
          have hvx : v ≠ x := fun h ↦ hxv h.symm
          simp [hxu, hxv, hux, hvx]

theorem ons_closed_walk_count_incident_edges
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u : V} (p : G.Walk u u) (x : V) :
    p.edges.countP (fun edge ↦ x ∈ edge) =
      2 * p.support.tail.count x := by
  rw [ons_walk_count_incident_edges]
  have hsupport :
      p.support.dropLast ++ [u] = u :: p.support.tail :=
    (p.dropLast_support_concat).trans p.cons_tail_support.symm
  have hcount := congrArg (List.count x) hsupport
  simp only [List.count_append, List.count_cons, List.count_nil,
    Nat.add_zero] at hcount
  omega

theorem ons_trail_count_incident_edges_le_degree
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) (x : V) :
    p.edges.countP (fun edge ↦ x ∈ edge) ≤ G.degree x := by
  let F := p.edges.toFinset
  have hFsub : F ⊆ G.edgeFinset := by
    intro edge hedge
    rw [SimpleGraph.mem_edgeFinset]
    exact p.edges_subset_edgeSet (List.mem_toFinset.mp hedge)
  have hcount :
      p.edges.countP (fun edge ↦ x ∈ edge) =
        StatMech.Ising.incCount F x := by
    calc
      p.edges.countP (fun edge ↦ x ∈ edge) =
          (p.edges.filter (fun edge ↦ x ∈ edge)).length :=
        List.countP_eq_length_filter
      _ = (p.edges.filter (fun edge ↦ x ∈ edge)).toFinset.card :=
        (List.toFinset_card_of_nodup
          (hp.edges_nodup.filter (fun edge ↦ x ∈ edge))).symm
      _ = StatMech.Ising.incCount F x := by
        unfold StatMech.Ising.incCount F
        congr 1
        ext edge
        simp
  rw [hcount]
  exact incCount_le_degree G F hFsub x

theorem ons_closed_trail_isCycle_of_degree_le_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u : V} (p : G.Walk u u) (hp : p.IsTrail)
    (hne : p ≠ .nil) (hdeg : ∀ v, G.degree v ≤ 3) :
    p.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨hp, hne, List.nodup_iff_count_le_one.mpr ?_⟩
  intro x
  have hcount := ons_closed_walk_count_incident_edges p x
  have hle := ons_trail_count_incident_edges_le_degree G hp x
  have hdegree := hdeg x
  omega

theorem ons_decWalkExternalDarts_append
    {L : ℕ} {u v w : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (q : (ons_decGraph L).Walk v w) :
    ons_decWalkExternalDarts (p.append q) =
      ons_decWalkExternalDarts p ++ ons_decWalkExternalDarts q := by
  unfold ons_decWalkExternalDarts
  rw [SimpleGraph.Walk.darts_append, List.filter_append,
    List.map_append]

theorem ons_decPortChainPath_externalDarts_eq_nil
    (L : ℕ) [Fact (2 < L)] (site : ZMod L × ZMod L)
    (a b : Fin 4) :
    ons_decWalkExternalDarts (ons_decPortChainPath L site a b) = [] := by
  unfold ons_decWalkExternalDarts
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro dart hdart hdartExt
  have hedge : dart.edge ∈
      (ons_decPortChainPath L site a b).edges.toFinset := by
    rw [List.mem_toFinset]
    unfold SimpleGraph.Walk.edges
    exact List.mem_map.mpr ⟨dart, hdart, rfl⟩
  rw [ons_decPortChainPath_edges_toFinset] at hedge
  have hrev : dart.snd = ons_dartRev L dart.fst := by
    simpa [ons_decDartIsExternal] using hdartExt
  change s(dart.fst, dart.snd) ∈ ons_decChainPathEdges site a b at hedge
  rw [hrev] at hedge
  exact ons_externalEdge_not_mem_chainPath L dart.fst site a b hedge

theorem ons_decTransitionWalk_externalDarts
    (L : ℕ) [Fact (2 < L)] (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    ons_decWalkExternalDarts (ons_decTransitionWalk L d₂ d₁ hstep) = [d₁] := by
  have hstart : (d₂.1, d₁.2 + 2) = ons_dartRev L d₁ := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L d₁).symm
    · simp [ons_dartRev]
  simp only [ons_decTransitionWalk, ons_decWalkExternalDarts_append]
  rw [ons_decWalkExternalDarts_cons_external]
  · simp only [ons_decWalkExternalDarts, SimpleGraph.Walk.darts_nil,
      List.filter_nil, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq, true_and]
    rw [List.map_eq_nil_iff]
    rw [SimpleGraph.Walk.darts_copy, List.filter_eq_nil_iff]
    intro dart hdart hdartExt
    have hnil := ons_decPortChainPath_externalDarts_eq_nil
      L d₂.1 (d₁.2 + 2) d₂.2
    unfold ons_decWalkExternalDarts at hnil
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hnil
    exact hnil dart hdart hdartExt
  · rfl

def ons_decGeometricStep (L : ℕ) (source target : ons_Dart L) : Prop :=
  target.1 = ons_dirStep L source.2 source.1

noncomputable def ons_decWalkEdgeCount
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : ons_DecEdge L →₀ ℕ := by
  classical
  exact Multiset.toFinsupp (p.edges : Multiset (ons_DecEdge L))

theorem ons_finsetExponent_toFinset_eq_edgeCount
    {E : Type*} [DecidableEq E] (l : List E) (hl : l.Nodup) :
    ons_finsetExponent l.toFinset =
      Multiset.toFinsupp (l : Multiset E) := by
  ext edge
  rw [ons_finsetExponent_apply, Multiset.toFinsupp_apply,
    Multiset.coe_count]
  by_cases hedge : edge ∈ l
  · rw [if_pos (List.mem_toFinset.mpr hedge)]
    simpa using (Multiset.count_eq_one_of_mem
      (show (l : Multiset E).Nodup from hl) hedge).symm
  · rw [if_neg (mt List.mem_toFinset.mp hedge)]
    exact (List.count_eq_zero.mpr hedge).symm

theorem ons_decTransitionExponent_eq_edgeCount
    (L : ℕ) [Fact (2 < L)] (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    ons_decTransitionExponent L d₂ d₁ =
      ons_decWalkEdgeCount
        (ons_decTransitionWalk L d₂ d₁ hstep) := by
  rw [ons_decTransitionExponent_eq_walkEdges]
  exact ons_finsetExponent_toFinset_eq_edgeCount _
    ((SimpleGraph.Walk.isTrail_def _).mp
      (ons_decTransitionWalk_isTrail L d₂ d₁ hstep))

noncomputable def ons_decKWChainExponent
    (L : ℕ) (start : ons_Dart L) :
    List (ons_Dart L) → ons_DecEdge L →₀ ℕ
  | [] => 0
  | target :: rest =>
      ons_decTransitionExponent L target start +
        ons_decKWChainExponent L target rest

theorem ons_decKWChainExponent_eq_zipWith
    (L : ℕ) (start : ons_Dart L) (tail : List (ons_Dart L)) :
    ons_decKWChainExponent L start tail =
      (List.zipWith
        (fun source target ↦ ons_decTransitionExponent L target source)
        (start :: tail) tail).sum := by
  induction tail generalizing start with
  | nil => rfl
  | cons target rest ih =>
      simp [ons_decKWChainExponent, ih]

theorem ons_isChain_closed_ofFn_mk
    {alpha : Type*} {R : alpha → alpha → Prop}
    {n : ℕ} [NeZero n] (f : Fin n → alpha)
    (hstep : ∀ k : Fin n, R (f k) (f (k + 1))) :
    List.IsChain R (List.ofFn f ++ [f 0]) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  apply List.IsChain.append
  · rw [List.isChain_ofFn]
    intro i hi
    let k : Fin (m + 1) := ⟨i, by omega⟩
    have hk : k ≠ Fin.last m := by
      intro h
      have := Fin.mk.inj_iff.mp h
      omega
    have hnext : k + 1 = ⟨i + 1, by omega⟩ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last k) hk)
    simpa [k, hnext] using hstep k
  · exact .singleton _
  · intro x hx y hy
    have hxlast : x = f (Fin.last m) := by
      rw [List.getLast?_eq_getLast (by simp), List.getLast_ofFn] at hx
      simpa using hx.symm
    have hyzero : y = f 0 := by simpa using hy.symm
    subst x
    subst y
    simpa using hstep (Fin.last m)

def ons_decKWChainLast (start : ons_Dart L) :
    List (ons_Dart L) → ons_Dart L
  | [] => start
  | target :: rest => ons_decKWChainLast target rest

@[simp] theorem ons_decKWChainLast_append_singleton
    (start : ons_Dart L) (tail : List (ons_Dart L)) (finish : ons_Dart L) :
    ons_decKWChainLast start (tail ++ [finish]) = finish := by
  induction tail generalizing start with
  | nil => rfl
  | cons target rest ih => exact ih target

noncomputable def ons_decWalkOfKWChain
    (L : ℕ) (start : ons_Dart L) :
    (tail : List (ons_Dart L)) →
    List.IsChain (ons_decGeometricStep L) (start :: tail) →
    (ons_decGraph L).Walk start (ons_decKWChainLast start tail)
  | [], _ => .nil
  | target :: rest, hchain => by
      have hstep : target.1 = ons_dirStep L start.2 start.1 :=
        hchain.rel
      let first := ons_decTransitionWalk L target start hstep
      let remaining :=
        ons_decWalkOfKWChain L target rest hchain.tail
      exact first.append remaining

theorem ons_decWalkOfKWChain_edgeCount
    (L : ℕ) [Fact (2 < L)] (start : ons_Dart L)
    (tail : List (ons_Dart L))
    (hchain : List.IsChain (ons_decGeometricStep L) (start :: tail)) :
    ons_decWalkEdgeCount (ons_decWalkOfKWChain L start tail hchain) =
      ons_decKWChainExponent L start tail := by
  induction tail generalizing start with
  | nil =>
      change Multiset.toFinsupp (0 : Multiset (ons_DecEdge L)) = 0
      simp
  | cons target rest ih =>
      have hstep : target.1 = ons_dirStep L start.2 start.1 :=
        hchain.rel
      have htail : List.IsChain (ons_decGeometricStep L) (target :: rest) :=
        hchain.tail
      simp only [ons_decWalkOfKWChain]
      unfold ons_decWalkEdgeCount
      rw [SimpleGraph.Walk.edges_append]
      change Multiset.toFinsupp
          ((ons_decTransitionWalk L target start hstep).edges +
            (ons_decWalkOfKWChain L target rest htail).edges :
              Multiset (ons_DecEdge L)) = _
      rw [Multiset.toFinsupp_add]
      have htrans :=
        ons_decTransitionExponent_eq_edgeCount L target start hstep
      unfold ons_decWalkEdgeCount at htrans
      rw [← htrans]
      have hrest := ih target htail
      unfold ons_decWalkEdgeCount at hrest
      rw [hrest]
      rfl

theorem ons_decWalkOfKWChain_externalDarts
    (L : ℕ) [Fact (2 < L)] (start : ons_Dart L)
    (tail : List (ons_Dart L))
    (hchain : List.IsChain (ons_decGeometricStep L) (start :: tail)) :
    ons_decWalkExternalDarts
        (ons_decWalkOfKWChain L start tail hchain) =
      (start :: tail).dropLast := by
  induction tail generalizing start with
  | nil => rfl
  | cons target rest ih =>
      have hstep : target.1 = ons_dirStep L start.2 start.1 :=
        hchain.rel
      have htail : List.IsChain (ons_decGeometricStep L) (target :: rest) :=
        hchain.tail
      change ons_decWalkExternalDarts
          ((ons_decTransitionWalk L target start hstep).append
            (ons_decWalkOfKWChain L target rest htail)) = _
      rw [ons_decWalkExternalDarts_append,
        ons_decTransitionWalk_externalDarts L target start hstep]
      rw [ih target htail]
      simp

theorem ons_decWalkOfKWChain_snd
    (L : ℕ) (start target : ons_Dart L)
    (rest : List (ons_Dart L))
    (hchain : List.IsChain (ons_decGeometricStep L)
      (start :: target :: rest)) :
    (ons_decWalkOfKWChain L start (target :: rest) hchain).snd =
      ons_dartRev L start := by
  have hstep : target.1 = ons_dirStep L start.2 start.1 := hchain.rel
  have htail : List.IsChain (ons_decGeometricStep L) (target :: rest) :=
    hchain.tail
  have hstart : (target.1, start.2 + 2) = ons_dartRev L start := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L start).symm
    · simp [ons_dartRev]
  change ((ons_decTransitionWalk L target start hstep).append
    (ons_decWalkOfKWChain L target rest htail)).snd = _
  simp [ons_decTransitionWalk, hstart]

theorem ons_decWalkOfKWChain_snd_of_ne_nil
    (L : ℕ) (start : ons_Dart L) (tail : List (ons_Dart L))
    (hchain : List.IsChain (ons_decGeometricStep L) (start :: tail))
    (htail : tail ≠ []) :
    (ons_decWalkOfKWChain L start tail hchain).snd =
      ons_dartRev L start := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons target rest =>
      exact ons_decWalkOfKWChain_snd L start target rest hchain

theorem ons_decKWChainExponent_closed_eq_sum
    (L : ℕ) {n : ℕ} [NeZero n] (f : Fin n → ons_Dart L) :
    let states := List.ofFn f
    ons_decKWChainExponent L (f 0) (states.tail ++ [f 0]) =
      ∑ k : Fin n, ons_decTransitionExponent L (f (k + 1)) (f k) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let states := List.ofFn f
  have htail : states.tail = List.ofFn (fun i : Fin m ↦ f i.succ) := by
    simp [states, List.ofFn_succ]
  change ons_decKWChainExponent L (f 0)
      (states.tail ++ [f 0]) = _
  rw [ons_decKWChainExponent_eq_zipWith]
  rw [htail]
  rw [← List.sum_ofFn]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i hi h'i
    simp only [List.length_zipWith] at hi
    simp only [List.getElem_zipWith]
    rw [List.getElem_ofFn]
    have hiN : i < m + 1 := by simpa using h'i
    let k : Fin (m + 1) := ⟨i, hiN⟩
    have hsource :
        (f 0 :: (List.ofFn (fun j : Fin m ↦ f j.succ) ++ [f 0]))[i] =
          f k := by
      cases i with
      | zero => simp [k]
      | succ i =>
          have hiM : i < m := by omega
          simp [List.getElem_append, hiM, k]
    have htarget :
        (List.ofFn (fun j : Fin m ↦ f j.succ) ++ [f 0])[i] =
          f (k + 1) := by
      by_cases hiM : i < m
      · simp [List.getElem_append, hiM, k]
        congr 1
        apply Fin.ext
        have hk : k < Fin.last m := by
          change i < m
          exact hiM
        exact (Fin.val_add_one_of_lt hk).symm
      · have hiEq : i = m := by omega
        subst i
        simp only [List.getElem_append, List.length_ofFn, lt_self_iff_false,
          ↓reduceDIte, Nat.sub_self, List.getElem_singleton,
          Fin.isValue]
        congr 1
        apply Fin.ext
        have hklast : k = Fin.last m := by
          apply Fin.ext
          simp [k]
        rw [hklast, Fin.last_add_one]
    rw [hsource, htarget]

def ons_decGeometricLoopStates
    {L n : ℕ} (d : Fin n → ons_Dart L) : Fin n → ons_Dart L :=
  fun k ↦ d (-k)

theorem ons_decGeometricLoopStates_valid
    {L n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ∀ k : Fin n,
      ons_decGeometricStep L
        (ons_decGeometricLoopStates d k)
        (ons_decGeometricLoopStates d (k + 1)) := by
  intro k
  unfold ons_decGeometricStep ons_decGeometricLoopStates
  have h := hvalid (-(k + 1))
  have hidx : -(k + 1) + 1 = -k := by
    simp
  simpa [hidx] using h

theorem ons_decGeometricLoopStates_sum_exponent
    {L n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    (∑ k : Fin n, ons_decTransitionExponent L
      (ons_decGeometricLoopStates d (k + 1))
      (ons_decGeometricLoopStates d k)) =
        ons_decLoopExponent L d := by
  unfold ons_decGeometricLoopStates ons_decLoopExponent
  let e : Fin n ≃ Fin n :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  have hsum := Equiv.sum_comp e
    (fun k : Fin n ↦ ons_decTransitionExponent L (d k) (d (k + 1)))
  simpa [e] using hsum

theorem ons_list_reverse_ofFn
    {alpha : Type*} {n : ℕ} (f : Fin n → alpha) :
    (List.ofFn f).reverse = List.ofFn (fun i ↦ f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i hi h'i
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.val_rev]
    omega

theorem ons_decGeometricLoopStates_tail_reverse
    {L n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    d 0 :: (List.ofFn (ons_decGeometricLoopStates d)).tail.reverse =
      List.ofFn d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [show List.ofFn (ons_decGeometricLoopStates d) =
      d 0 :: List.ofFn
        (fun i : Fin m ↦ ons_decGeometricLoopStates d i.succ) by
    rw [List.ofFn_succ]
    simp [ons_decGeometricLoopStates]]
  simp only [List.tail_cons]
  rw [ons_list_reverse_ofFn, List.ofFn_succ]
  congr 1
  apply congrArg (fun f : Fin m → ons_Dart L ↦ List.ofFn f)
  funext i
  unfold ons_decGeometricLoopStates
  congr 1
  apply Fin.ext
  rw [Fin.val_neg]
  have hne : i.rev.succ ≠ (0 : Fin (m + 1)) := by
    intro hzero
    have hval := congrArg Fin.val hzero
    simp [Fin.val_succ, Fin.val_rev] at hval
  rw [if_neg hne]
  simp only [Fin.val_succ, Fin.val_rev]
  omega

noncomputable def ons_decLoopWalk
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (ons_decGraph L).Walk (d 0) (d 0) := by
  let states := List.ofFn (ons_decGeometricLoopStates d)
  have hstatesNonempty : states ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    exact NeZero.pos n
  have hhead : states.head? = some (d 0) := by
    rw [List.head?_eq_head hstatesNonempty,
      List.head_ofFn hstatesNonempty]
    simp [ons_decGeometricLoopStates]
  have hstates : states = d 0 :: states.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have hchain : List.IsChain (ons_decGeometricStep L)
      (states ++ [d 0]) := by
    simpa [states, ons_decGeometricLoopStates] using
      ons_isChain_closed_ofFn_mk (ons_decGeometricLoopStates d)
        (ons_decGeometricLoopStates_valid d hvalid)
  have hchain' : List.IsChain (ons_decGeometricStep L)
      (d 0 :: (states.tail ++ [d 0])) := by
    rw [← List.cons_append, ← hstates]
    exact hchain
  let walk := ons_decWalkOfKWChain L (d 0)
    (states.tail ++ [d 0]) hchain'
  exact walk.copy rfl (ons_decKWChainLast_append_singleton _ _ _)

theorem ons_decLoopWalk_snd
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (ons_decLoopWalk L d hvalid).snd = ons_dartRev L (d 0) := by
  unfold ons_decLoopWalk
  dsimp only
  change ((ons_decWalkOfKWChain L (d 0)
      ((List.ofFn (ons_decGeometricLoopStates d)).tail ++ [d 0]) _).copy _ _).getVert 1 = _
  rw [SimpleGraph.Walk.getVert_copy]
  apply ons_decWalkOfKWChain_snd_of_ne_nil
  simp

theorem ons_decLoopWalk_externalDarts
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decWalkExternalDarts (ons_decLoopWalk L d hvalid) =
      List.ofFn (ons_decGeometricLoopStates d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  unfold ons_decLoopWalk
  simp only [ons_decWalkExternalDarts, SimpleGraph.Walk.darts_copy]
  change ons_decWalkExternalDarts
      (ons_decWalkOfKWChain L (d 0)
        ((List.ofFn (ons_decGeometricLoopStates d)).tail ++ [d 0]) _) = _
  rw [ons_decWalkOfKWChain_externalDarts]
  rw [← List.cons_append]
  have hhead :
      d 0 :: (List.ofFn (ons_decGeometricLoopStates d)).tail =
        List.ofFn (ons_decGeometricLoopStates d) := by
    rw [List.ofFn_succ]
    simp [ons_decGeometricLoopStates]
  rw [hhead, List.dropLast_concat]

theorem ons_decLoopWalk_cycleDartList
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decCycleDartList (ons_decLoopWalk L d hvalid) =
      List.ofFn d := by
  rw [ons_decCycleDartList_eq, ons_decLoopWalk_externalDarts]
  exact ons_decGeometricLoopStates_tail_reverse d

theorem ons_decLoopWalk_cycleDartLoop
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (k : Fin n) :
    ons_decCycleDartLoop (ons_decLoopWalk L d hvalid)
        ⟨k.val, by
          rw [ons_decLoopWalk_cycleDartList, List.length_ofFn]
          exact k.isLt⟩ =
      d k := by
  unfold ons_decCycleDartLoop
  simp [ons_decLoopWalk_cycleDartList]

theorem ons_decLoopWalk_edgeCount
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decWalkEdgeCount (ons_decLoopWalk L d hvalid) =
      ons_decLoopExponent L d := by
  unfold ons_decLoopWalk
  simp only [ons_decWalkEdgeCount, SimpleGraph.Walk.edges_copy]
  change ons_decWalkEdgeCount
      (ons_decWalkOfKWChain L (d 0)
        ((List.ofFn (ons_decGeometricLoopStates d)).tail ++ [d 0]) _) = _
  rw [ons_decWalkOfKWChain_edgeCount]
  calc
    ons_decKWChainExponent L (d 0)
        ((List.ofFn (ons_decGeometricLoopStates d)).tail ++ [d 0]) =
        ∑ k : Fin n, ons_decTransitionExponent L
          (ons_decGeometricLoopStates d (k + 1))
          (ons_decGeometricLoopStates d k) := by
      simpa [ons_decGeometricLoopStates] using
        ons_decKWChainExponent_closed_eq_sum L
          (ons_decGeometricLoopStates d)
    _ = ons_decLoopExponent L d :=
      ons_decGeometricLoopStates_sum_exponent d

theorem ons_decLoopWalk_isTrail_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    (ons_decLoopWalk L d hvalid).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  apply List.nodup_iff_count_le_one.mpr
  intro edge
  have hcount := DFunLike.congr_fun
    (ons_decLoopWalk_edgeCount L d hvalid) edge
  unfold ons_decWalkEdgeCount at hcount
  rw [Multiset.toFinsupp_apply, hexponent,
    ons_finsetExponent_apply] at hcount
  by_cases hedge : edge ∈ S
  · rw [if_pos hedge] at hcount
    rw [Multiset.coe_count] at hcount
    omega
  · rw [if_neg hedge] at hcount
    rw [Multiset.coe_count] at hcount
    omega

theorem ons_decLoopWalk_ne_nil
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decLoopWalk L d hvalid ≠ .nil := by
  intro hnil
  have hcount := ons_decLoopWalk_edgeCount L d hvalid
  rw [hnil] at hcount
  change (0 : ons_DecEdge L →₀ ℕ) = ons_decLoopExponent L d at hcount
  have hdegree := ons_decLoopExponent_length_le L d
  rw [← hcount] at hdegree
  simp [ons_finsuppTotalDegree] at hdegree
  exact (NeZero.ne n) hdegree

theorem ons_decLoopWalk_isCycle_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    (ons_decLoopWalk L d hvalid).IsCycle := by
  apply ons_closed_trail_isCycle_of_degree_le_three (ons_decGraph L)
  · exact ons_decLoopWalk_isTrail_of_squarefree L d hvalid S hexponent
  · exact ons_decLoopWalk_ne_nil L d hvalid
  · exact ons_decGraph_degree_le_three L

theorem ons_decLoopWalk_edges_toFinset_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    (ons_decLoopWalk L d hvalid).edges.toFinset = S := by
  apply ons_finsetExponent_injective
  rw [ons_finsetExponent_toFinset_eq_edgeCount _
    ((ons_decLoopWalk_isTrail_of_squarefree
      L d hvalid S hexponent).edges_nodup)]
  change ons_decWalkEdgeCount (ons_decLoopWalk L d hvalid) = _
  rw [ons_decLoopWalk_edgeCount, hexponent]

theorem ons_decLoop_valid_of_scalar_ne_zero
    (L : ℕ) (omega u v : ℂ) {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hscalar : ons_decLoopScalar L omega u v d ≠ 0) :
    ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1 := by
  intro k
  have hfactor :
      ons_decTransitionScalar L omega u v (d k) (d (k + 1)) ≠ 0 := by
    intro hzero
    apply hscalar
    unfold ons_decLoopScalar
    exact Finset.prod_eq_zero (Finset.mem_univ k) hzero
  unfold ons_decTransitionScalar at hfactor
  by_contra hstep
  rw [if_neg hstep] at hfactor
  exact hfactor rfl

theorem ons_decLoopScalar_eq_loopWeight_one
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_decLoopScalar L omega u v d =
      ons_loopWeight
        (ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v) d := by
  have hspecialized :
      ons_decSpecializedWeight (fun _ : Sym2 (ZMod L × ZMod L) ↦ (1 : ℂ)) =
        (fun _ : ons_DecEdge L ↦ (1 : ℂ)) := by
    funext edge
    classical
    unfold ons_decSpecializedWeight
    split <;> rfl
  have hmatrix := ons_KWmatDecorationWeightedPhase_specialized
    L (fun _ : Sym2 (ZMod L × ZMod L) ↦ (1 : ℂ)) omega u v
  rw [hspecialized] at hmatrix
  have hloop := ons_loopWeight_KWmatDecorationWeightedPhase
    (L := L) (fun _ : ons_DecEdge L ↦ (1 : ℂ)) omega u v d
  rw [hmatrix] at hloop
  simpa using hloop.symm

theorem ons_decLoopScalar_eq_cycleFirstReturn
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decLoopScalar L omega u v d =
      ons_edgeWeight
        (ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v)
        (ons_decCycleFirstReturn (ons_decLoopWalk L d hvalid)) := by
  let q := ons_decLoopWalk L d hvalid
  let Lambda := ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v
  rw [ons_decLoopScalar_eq_loopWeight_one]
  calc
    ons_loopWeight Lambda d =
        ons_edgeWeight Lambda (List.ofFn d ++ [d 0]) :=
      ons_loopWeight_eq_edgeWeight_neZero Lambda d
    _ = ons_edgeWeight Lambda
        (List.ofFn (ons_decCycleDartLoop q) ++
          [ons_decCycleDartLoop q 0]) := by
      rw [ons_decCycleDartLoop_zero,
        ons_decCycleDartList_ofFn,
        ons_decLoopWalk_cycleDartList]
    _ = ons_loopWeight Lambda (ons_decCycleDartLoop q) :=
      (ons_loopWeight_eq_edgeWeight_neZero Lambda
        (ons_decCycleDartLoop q)).symm
    _ = ons_edgeWeight Lambda (ons_decCycleFirstReturn q) :=
      (ons_decCycleFirstReturn_edgeWeight_eq_loopWeight q Lambda).symm

theorem ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
    (hscalar : ons_decLoopScalar L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) d ≠ 0) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d =
      -((ons_spinCharacter a b
        (ons_evenHomology L
          (ons_walkOriginalEdges
            (ons_decLoopWalk L d
              (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
                (ons_spinPhase L a) (ons_spinPhase L b) d hscalar))))) : ℂ) := by
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hscalar
  let q := ons_decLoopWalk L d hvalid
  have hq : q.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hexponent
  have hsnd : q.snd = ons_dartRev L (d 0) :=
    ons_decLoopWalk_snd L d hvalid
  rw [ons_decLoopScalar_eq_cycleFirstReturn L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hvalid]
  simpa [q, hvalid] using
    ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
      q hq hsnd (fun _ ↦ 1) a b

end StatMech.Onsager
