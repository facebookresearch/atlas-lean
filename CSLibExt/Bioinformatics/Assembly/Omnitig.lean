/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Order.MinMax
import Mathlib.Data.Nat.Find

/-!
# Omnitigs are exactly the safe walks

In genome assembly a contig is *safe* when it occurs in every possible reconstruction of the
genome. In the edge-centric model of Tomescu and Medvedev a reconstruction is a circular
edge-covering walk of the assembly graph, so a walk is safe when it is a subwalk of every
circular edge-covering walk. Their Theorem 1 characterises the safe walks combinatorially as the
*omnitigs*: a walk `e₀ … e_t` (nodes `vᵢ = src eᵢ`) is an omnitig iff for all `1 ≤ i ≤ j ≤ t`
no path from `v_j` to `v_i` starts with an edge other than `e_j` and ends with an edge other
than `e_{i-1}`. The source builds its safe and complete contig assembly algorithm on this
characterisation.

## Definitions

* `Multigraph`: a directed multigraph given by edge sources and targets.
* `IsWalk`, `IsPath`, `IsCircularCovering`, `IsCircularSubwalk`: walks as edge lists, paths
  (distinct nodes except possibly first = last), circular edge-covering walks, and occurrence in
  a circular walk with wrap-around (several turns and overlap of tail and head allowed, as in
  the source).
* `IsSafe`, `IsOmnitig`: safe walks and omnitigs (Definition 5).

## Main results

* `IsOmnitig.isSafe`: every omnitig is safe (Theorem 1, (2) ⇒ (1)).
* `isOmnitig_of_isSafe`: if a circular edge-covering walk exists, every safe walk is an omnitig
  (Theorem 1, (1) ⇒ (2)).

## Design notes

Theorem 1 is stated in the source for strings spelled by walks in a genome graph, where a string
is spelled by a unique walk; here it is stated directly for walks. Walks are nonempty edge lists;
the source requires at least two edges, but for a single edge the omnitig condition is vacuous
and the edge is trivially safe, so nothing changes. The source's standing assumption that the
graph is not a single cycle is used only by its algorithmic lemma, not by Theorem 1; it is not
assumed here. Without any circular edge-covering walk every walk is vacuously safe, which is why
the converse assumes one exists. The omnitig-listing algorithm (the source's Algorithm 1) is not
covered.

## References

* A. I. Tomescu and P. Medvedev, *Safe and complete contig assembly through omnitigs*,
  J. Comput. Biol. 24 (2017), 590–602 (RECOMB 2016; arXiv:1601.02932).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Assembly.Omnitig

/-- A directed multigraph given by the source and target of each edge. -/
structure Multigraph (V : Type*) (E : Type*) where
  /-- The source (tail) of an edge. -/
  src : E → V
  /-- The target (head) of an edge. -/
  tgt : E → V

variable {V E : Type*} (G : Multigraph V E)

/-- A list of edges is a walk when consecutive edges are incident (head to tail). -/
def IsWalk (w : List E) : Prop := w.IsChain (fun e f => G.tgt e = G.src f)

/-- A path: a nonempty walk whose nodes `src e₀, tgt e₀, …, tgt e_ℓ` are distinct, except that
the first and last node may coincide. -/
def IsPath (p : List E) : Prop :=
  p ≠ [] ∧ IsWalk G p ∧ (p.map G.tgt).Nodup ∧
    ∀ e₀ ∈ p.head?, G.src e₀ ∉ (p.map G.tgt).dropLast

/-- A circular edge-covering walk: a nonempty closed walk through every edge. -/
def IsCircularCovering (A : List E) : Prop :=
  A ≠ [] ∧ IsWalk G A ∧ (∀ a ∈ A.getLast?, ∀ b ∈ A.head?, G.tgt a = G.src b) ∧ ∀ e, e ∈ A

/-- `w` is a subwalk of the circular walk `A`: it is read off `A` from some start position,
wrapping around (possibly several times). -/
def IsCircularSubwalk (w A : List E) : Prop :=
  ∃ p : ℕ, ∀ (i : ℕ) (hi : i < w.length), A[(p + i) % A.length]? = some w[i]

/-- Safe walk: a subwalk of every circular edge-covering walk. -/
def IsSafe (w : List E) : Prop :=
  ∀ A, IsCircularCovering G A → IsCircularSubwalk w A

/-- Omnitig (Tomescu–Medvedev, Definition 5): for all `1 ≤ i ≤ j ≤ t` (`t + 1 = w.length`),
no path from `v_j = src e_j` to `v_i = src e_i` has first edge `≠ e_j` and last edge
`≠ e_{i-1}`. -/
def IsOmnitig (w : List E) : Prop :=
  w ≠ [] ∧ IsWalk G w ∧
    ∀ (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j < w.length) (p : List E), IsPath G p →
      ∀ f ∈ p.head?, ∀ l ∈ p.getLast?,
        G.src f = G.src w[j] → G.tgt l = G.src w[i] → f ≠ w[j] → l ≠ w[i - 1] → False

private def WalkFrom {V E : Type*} (G : Multigraph V E) (u v : V) : List E → Prop
  | [] => u = v
  | e :: es => G.src e = u ∧ WalkFrom G (G.tgt e) v es

private theorem walkFrom_append {V E : Type*} (G : Multigraph V E)
    (u v z : V) (s t : List E) (hs : WalkFrom G u v s) (ht : WalkFrom G v z t) :
    WalkFrom G u z (s ++ t) := by
  induction s generalizing u with
  | nil => simp only [WalkFrom] at hs; simpa [hs] using ht
  | cons e es ih => exact ⟨hs.1, ih _ hs.2⟩

private theorem walkFrom_split {V E : Type*} (G : Multigraph V E)
    (u v : V) (s t : List E) (h : WalkFrom G u v (s ++ t)) :
    ∃ z, WalkFrom G u z s ∧ WalkFrom G z v t := by
  induction s generalizing u with
  | nil => exact ⟨u, rfl, h⟩
  | cons e es ih =>
    obtain ⟨z, hz, ht⟩ := ih _ h.2
    exact ⟨z, ⟨h.1, hz⟩, ht⟩

private theorem walkFrom_walk {V E : Type*} (G : Multigraph V E)
    (u v : V) (s : List E) (h : WalkFrom G u v s) : IsWalk G s := by
  induction s generalizing u with
  | nil => exact .nil
  | cons e es ih =>
    cases es with
    | nil => exact .singleton e
    | cons f fs => exact .cons_cons (h.2.1.symm) (ih _ h.2)

private theorem walkFrom_endpoints {V E : Type*} (G : Multigraph V E)
    (u v : V) (s : List E) (h : WalkFrom G u v s) :
    (∀ e ∈ s.head?, G.src e = u) ∧ (∀ e ∈ s.getLast?, G.tgt e = v) := by
  induction s generalizing u with
  | nil => simp
  | cons e es ih =>
    constructor
    · simpa using h.1
    · cases es with
      | nil => simpa [WalkFrom] using h.2
      | cons f fs => simpa using (ih _ h.2).2

private theorem walkFrom_of_walk {V E : Type*} (G : Multigraph V E)
    (u v : V) (s : List E) (hne : s ≠ []) (hw : IsWalk G s)
    (hh : ∀ e ∈ s.head?, G.src e = u) (hl : ∀ e ∈ s.getLast?, G.tgt e = v) :
    WalkFrom G u v s := by
  induction s generalizing u with
  | nil => exact (hne rfl).elim
  | cons e es ih =>
    refine ⟨hh e (by simp), ?_⟩
    cases es with
    | nil => exact hl e (by simp)
    | cons f fs =>
      apply ih _ (by simp) hw.tail
      · intro a ha
        have he : a = f := by simpa using ha.symm
        subst a
        exact (List.isChain_cons_cons.mp hw).1.symm
      · simpa using hl

private theorem walkFrom_trim {V E : Type*} (G : Multigraph V E)
    (u v : V) (s : List E) (hs : WalkFrom G u v s) :
    ∃ q, WalkFrom G u v q ∧ ∀ e ∈ q, G.src e ≠ v ∧ G.tgt e ≠ u := by
  classical
  by_cases huv : u = v
  · exact ⟨[], huv, by simp⟩
  have hex : ∃ n, ∃ q : List E, q.length = n ∧ WalkFrom G u v q :=
    ⟨s.length, s, rfl, hs⟩
  obtain ⟨q, hlen, hq⟩ := Nat.find_spec hex
  refine ⟨q, hq, ?_⟩
  intro e he
  obtain ⟨pre, post, heq⟩ := List.mem_iff_append.mp he
  subst q
  obtain ⟨z, hpre, hrest⟩ := walkFrom_split G u v pre (e :: post) hq
  constructor
  · intro hev
    have hzv : z = v := hrest.1.symm.trans hev
    have hshort : pre.length < Nat.find hex := by
      simp only [List.length_append, List.length_cons] at hlen
      omega
    exact (Nat.find_min' hex ⟨pre, rfl, hzv ▸ hpre⟩).not_gt hshort
  · intro heu
    have hpost : WalkFrom G u v post := heu ▸ hrest.2
    have hshort : post.length < Nat.find hex := by
      simp only [List.length_append, List.length_cons] at hlen
      omega
    exact (Nat.find_min' hex ⟨post, rfl, hpost⟩).not_gt hshort

private theorem path_src_ne {V E : Type*} (G : Multigraph V E)
    (p : List E) (hp : IsPath G p) (f b : E) (hf : f ∈ p.head?)
    (hb : G.src b = G.src f) (hbf : b ≠ f) : b ∉ p := by
  intro hm
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
  by_cases hzero : k = 0
  · subst k
    have hhead : p[0]? = some f := by simpa [List.head?_eq_getElem?] using hf
    have hfe : p[0] = f := (List.getElem?_eq_some_iff.mp hhead).2
    exact hbf (he.symm.trans hfe)
  · have hkm : k - 1 + 1 = k := by omega
    have hinc := List.isChain_iff_getElem.mp hp.2.1 (k - 1) (by omega)
    simp only [hkm, he, hb] at hinc
    apply hp.2.2.2 f hf
    have hbound : k - 1 < (p.map G.tgt).dropLast.length := by simp; omega
    have hmem := List.getElem_mem hbound
    simpa only [List.getElem_dropLast, List.getElem_map, hinc] using hmem

private theorem path_tgt_ne {V E : Type*} (G : Multigraph V E)
    (p : List E) (hp : IsPath G p) (l a : E) (hl : l ∈ p.getLast?)
    (ha : G.tgt a = G.tgt l) (hal : a ≠ l) : a ∉ p := by
  intro hm
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
  have hlast : p[p.length - 1]? = some l := by
    simpa [List.getLast?_eq_getElem?] using hl
  obtain ⟨hbound, hel⟩ := List.getElem?_eq_some_iff.mp hlast
  have hmk : k < (p.map G.tgt).length := by simpa using hk
  have hml : p.length - 1 < (p.map G.tgt).length := by simpa using hbound
  have heq : (p.map G.tgt)[k] = (p.map G.tgt)[p.length - 1] := by
    simpa only [List.getElem_map, he, hel] using ha
  have hk' := hp.2.2.1.getElem_inj_iff.mp heq
  subst k
  exact hal (he.symm.trans hel)

private theorem circularSubwalk_singleton {E : Type*} (e : E) (A : List E)
    (he : e ∈ A) : IsCircularSubwalk [e] A := by
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp he
  refine ⟨k, ?_⟩
  intro i hi
  have hzero : i = 0 := by simpa using hi
  subst i
  simpa [Nat.mod_eq_of_lt hk, he] using List.getElem?_eq_getElem hk

private theorem walkFrom_segment {V E : Type*} (G : Multigraph V E)
    (w : List E) (hw : IsWalk G w) (i n : ℕ) (hn : i + n < w.length) :
    WalkFrom G (G.src w[i]) (G.src w[i + n]) ((w.drop i).take n) := by
  induction n with
  | zero => simp [WalkFrom]
  | succ n ih =>
    have hd : n < (w.drop i).length := by simp; omega
    rw [List.take_succ_eq_append_getElem hd]
    apply walkFrom_append G _ (G.src w[i + n]) _ _ _ (ih (by omega))
    simp only [WalkFrom, List.getElem_drop]
    exact ⟨trivial, List.isChain_iff_getElem.mp hw (i + n) (by omega)⟩

private theorem long_buffer {V E : Type*} (G : Multigraph V E)
    (u : V) (D : List E) (hD : WalkFrom G u u D) (hne : D ≠ [])
    (a b : E) (ha : a ∉ D) (hb : b ∉ D) (n : ℕ) :
    ∃ C, WalkFrom G u u C ∧ n ≤ C.length ∧ a ∉ C ∧ b ∉ C := by
  induction n with
  | zero => exact ⟨[], rfl, by simp⟩
  | succ n ih =>
    obtain ⟨C, hC, hlen, hCa, hCb⟩ := ih
    refine ⟨C ++ D, walkFrom_append G u u u C D hC hD, ?_, ?_, ?_⟩
    · have hpos := List.length_pos_iff.mpr hne
      simp only [List.length_append]
      omega
    · simpa using And.intro hCa ha
    · simpa using And.intro hCb hb

private noncomputable def bufferEdges {E : Type*} (b : E) (C A : List E) : List E := by
  classical
  exact A.flatMap fun e => if e = b then C ++ [e] else [e]

private theorem bufferEdges_nil {E : Type*} (b : E) (C : List E) :
    bufferEdges b C [] = [] := by simp [bufferEdges]

private theorem bufferEdges_cons {E : Type*} [DecidableEq E] (b e : E) (C A : List E) :
    bufferEdges b C (e :: A) =
      (if e = b then C ++ [e] else [e]) ++ bufferEdges b C A := by
  classical
  simp [bufferEdges]

private theorem bufferEdges_mem {E : Type*} (b : E) (C A : List E) (e : E)
    (he : e ∈ A) : e ∈ bufferEdges b C A := by
  classical
  apply List.mem_flatMap.mpr
  exact ⟨e, he, by split <;> simp⟩

private theorem bufferEdges_walkFrom {V E : Type*} (G : Multigraph V E)
    (b : E) (C A : List E) (hC : WalkFrom G (G.src b) (G.src b) C)
    (u v : V) (hA : WalkFrom G u v A) : WalkFrom G u v (bufferEdges b C A) := by
  classical
  induction A generalizing u with
  | nil => simpa [bufferEdges_nil] using hA
  | cons e es ih =>
    rw [bufferEdges_cons]
    by_cases heb : e = b
    · subst e
      simp only [ite_true, List.append_assoc, List.singleton_append]
      have htail : WalkFrom G (G.src b) v (b :: bufferEdges b C es) :=
        ⟨rfl, ih _ hA.2⟩
      have hfull := walkFrom_append G (G.src b) (G.src b) v C _ hC htail
      simpa only [hA.1] using hfull
    · simp only [ite_eq_right heb, List.singleton_append]
      exact ⟨hA.1, ih _ hA.2⟩

private theorem bufferEdges_predecessor {E : Type*} (a b : E) (C A : List E)
    (L : ℕ) (hL : 0 < L) (hCL : L ≤ C.length) (hCa : a ∉ C) (hCb : b ∉ C) :
    ∀ r (hr : r < (bufferEdges b C A).length),
      (bufferEdges b C A)[r] = b →
        ∃ (hpred : r - L < (bufferEdges b C A).length),
          L ≤ r ∧ (bufferEdges b C A)[r - L] ≠ a := by
  classical
  induction A with
  | nil => simp [bufferEdges_nil]
  | cons e es ih =>
    intro r hr hb
    simp only [bufferEdges_cons] at hr hb ⊢
    by_cases heb : e = b
    · subst e
      simp only [ite_true, List.append_assoc, List.singleton_append] at hr hb ⊢
      by_cases hrC : r < C.length
      · have hbr : C[r] = b := by simpa [List.getElem_append, hrC] using hb
        exact (hCb (hbr ▸ List.getElem_mem hrC)).elim
      · by_cases hre : r = C.length
        · subst r
          have hpred : C.length - L < (C ++ b :: bufferEdges b C es).length := by
            simp; omega
          refine ⟨hpred, hCL, ?_⟩
          have hinside : C.length - L < C.length := by omega
          simp only [List.getElem_append, dite_eq_left hinside]
          exact fun h => hCa (h ▸ List.getElem_mem hinside)
        · have ht : r - C.length - 1 < (bufferEdges b C es).length := by
            simp only [List.length_append, List.length_cons] at hr
            omega
          have htail : (bufferEdges b C es)[r - C.length - 1] = b := by
            simpa [List.getElem_append, hrC, List.getElem_cons, hre,
              show r - C.length ≠ 0 by omega] using hb
          obtain ⟨hp, hlow, hne⟩ := ih _ ht htail
          have hpred : r - L < (C ++ b :: bufferEdges b C es).length := by
            simp only [List.length_append, List.length_cons] at hr ⊢
            omega
          refine ⟨hpred, by omega, ?_⟩
          have hnotC : ¬r - L < C.length := by omega
          have hnot0 : r - L - C.length ≠ 0 := by omega
          simpa [List.getElem_append, hnotC, List.getElem_cons, hnot0,
            show r - L - C.length - 1 = r - C.length - 1 - L by omega] using hne
    · simp only [ite_eq_right heb, List.singleton_append] at hr hb ⊢
      cases r with
      | zero => exact (heb (by simpa using hb)).elim
      | succ r =>
        have ht : r < (bufferEdges b C es).length := by simpa using hr
        have htail : (bufferEdges b C es)[r] = b := by simpa using hb
        obtain ⟨hp, hlow, hne⟩ := ih r ht htail
        have hpred : r + 1 - L < (e :: bufferEdges b C es).length := by simp; omega
        refine ⟨hpred, by omega, ?_⟩
        simpa [show r + 1 - L = (r - L) + 1 by omega] using hne

private theorem bufferEdges_covering {V E : Type*} (G : Multigraph V E)
    (b : E) (C A : List E) (hC : WalkFrom G (G.src b) (G.src b) C)
    (hA : IsCircularCovering G A) : IsCircularCovering G (bufferEdges b C A) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp
    (List.isSome_head?.mpr hA.1)
  have hfm : f ∈ A.head? := hf
  have hAF : WalkFrom G (G.src f) (G.src f) A := by
    apply walkFrom_of_walk G _ _ A hA.1 hA.2.1
    · intro e he
      have heq : e = f := Option.mem_unique he hf
      simp [heq]
    · intro e he
      exact hA.2.2.1 e he f hfm
  have hBF := bufferEdges_walkFrom G b C A hC _ _ hAF
  have hmem : b ∈ bufferEdges b C A := bufferEdges_mem b C A b (hA.2.2.2 b)
  refine ⟨List.ne_nil_of_mem hmem, walkFrom_walk G _ _ _ hBF, ?_, ?_⟩
  · intro e he f hf
    exact ((walkFrom_endpoints G _ _ _ hBF).2 e he).trans
      ((walkFrom_endpoints G _ _ _ hBF).1 f hf).symm
  · exact fun e => bufferEdges_mem b C A e (hA.2.2.2 e)

private theorem mod_offset {n p L : ℕ} (hn : 0 < n) (hL : L < n)
    (hr : L ≤ (p + L) % n) : (p + L) % n = p % n + L := by
  have hp : p % n < n := Nat.mod_lt p hn
  have hadd : (p + L) % n = (p % n + L) % n := by simp [Nat.add_mod]
  rw [hadd] at hr ⊢
  by_cases hlt : p % n + L < n
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hr ⊢
    omega

private theorem bufferEdges_noPair {E : Type*} (a b : E) (C A : List E)
    (L p : ℕ) (hL : 0 < L) (hCL : L ≤ C.length) (hCa : a ∉ C) (hCb : b ∉ C)
    (hb : (bufferEdges b C A)[(p + L) % (bufferEdges b C A).length]? = some b) :
    (bufferEdges b C A)[p % (bufferEdges b C A).length]? ≠ some a := by
  obtain ⟨hr, he⟩ := List.getElem?_eq_some_iff.mp hb
  obtain ⟨hp, hlow, hne⟩ := bufferEdges_predecessor a b C A L hL hCL hCa hCb _ hr he
  have hn : 0 < (bufferEdges b C A).length := by omega
  have hLn : L < (bufferEdges b C A).length := by omega
  have heq := mod_offset hn hLn hlow
  have hsub : (p + L) % (bufferEdges b C A).length - L =
      p % (bufferEdges b C A).length := by omega
  intro ha
  obtain ⟨hpa, hea⟩ := List.getElem?_eq_some_iff.mp ha
  exact hne (by simpa only [hsub] using hea)

private theorem walkFrom_suffix {V E : Type*} (G : Multigraph V E)
    (u v : V) (s : List E) (hs : WalkFrom G u v s) (k : ℕ) (hk : k < s.length) :
    WalkFrom G (G.src s[k]) v (s.drop k) := by
  induction s generalizing u k with
  | nil => simp at hk
  | cons e es ih =>
    cases k with
    | zero => simpa [hs.1] using hs
    | succ k => simpa using ih _ hs.2 k (by simpa using hk)

private theorem path_tail {V E : Type*} (G : Multigraph V E)
    (p : List E) (hp : IsPath G p) (hne : p.tail ≠ []) : IsPath G p.tail := by
  cases p with
  | nil => simp at hne
  | cons e es =>
    cases es with
    | nil => simp at hne
    | cons f fs =>
      have hnodes := List.nodup_cons.mp hp.2.2.1
      refine ⟨hne, hp.2.1.tail, hnodes.2, ?_⟩
      intro a ha
      have haf : a = f := by simpa using ha.symm
      subst a
      have hsrc := (List.isChain_cons_cons.mp hp.2.1).1
      rw [← hsrc]
      exact fun hm => hnodes.1 (List.mem_of_mem_dropLast hm)

private theorem path_drop {V E : Type*} (G : Multigraph V E)
    (p : List E) (hp : IsPath G p) (k : ℕ) (hk : k < p.length) :
    IsPath G (p.drop k) := by
  induction k generalizing p with
  | zero => simpa using hp
  | succ k ih =>
    have ht : p.tail ≠ [] := by
      intro h
      have hh : p.tail.length = 0 := by simp [h]
      simp only [List.length_tail] at hh
      omega
    cases p with
    | nil => simp at hk
    | cons e es =>
      simpa using ih es (path_tail G (e :: es) hp ht) (by simpa using hk)

private theorem walkFrom_shortest_simple {V E : Type*} (G : Multigraph V E)
    (b : E) (u v : V) (q : List E) (hq : WalkFrom G u v q) (hb : b ∉ q)
    (hmin : ∀ r, WalkFrom G u v r → b ∉ r → q.length ≤ r.length) :
    (q.map G.tgt).Nodup ∧ u ∉ q.map G.tgt := by
  induction q generalizing u with
  | nil => simp
  | cons e es ih =>
    have hnotu : u ∉ (e :: es).map G.tgt := by
      intro hu
      obtain ⟨d, hd, hdu⟩ := List.mem_map.mp hu
      obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hd
      obtain ⟨z, hz, hr⟩ := walkFrom_split G u v pre (d :: post) (hsplit ▸ hq)
      have hpost : WalkFrom G u v post := hdu ▸ hr.2
      have hbpost : b ∉ post := by
        intro hm
        apply hb
        rw [hsplit]
        simp [hm]
      have hlen := hmin post hpost hbpost
      have hslen := congrArg List.length hsplit
      simp only [List.length_cons, List.length_append] at hslen hlen
      omega
    have hbe : b ≠ e := by intro h; exact hb (by simp [h])
    have hbes : b ∉ es := fun hm => hb (by simp [hm])
    have hmines : ∀ r, WalkFrom G (G.tgt e) v r → b ∉ r → es.length ≤ r.length := by
      intro r hr hbr
      have hh := hmin (e :: r) ⟨hq.1, hr⟩ (by simp [hbe, hbr])
      simpa using hh
    obtain ⟨hes, hsrc⟩ := ih _ hq.2 hbes hmines
    exact ⟨List.nodup_cons.mpr ⟨hsrc, hes⟩, hnotu⟩

private theorem walkFrom_shortest {V E : Type*} (G : Multigraph V E)
    (b : E) (u v : V) (s : List E) (hs : WalkFrom G u v s) (hb : b ∉ s) :
    ∃ q, WalkFrom G u v q ∧ b ∉ q ∧ (q.map G.tgt).Nodup ∧ u ∉ q.map G.tgt := by
  classical
  have hex : ∃ n, ∃ q : List E, q.length = n ∧ WalkFrom G u v q ∧ b ∉ q :=
    ⟨s.length, s, rfl, hs, hb⟩
  obtain ⟨q, hlen, hq, hqb⟩ := Nat.find_spec hex
  have hmin : ∀ r, WalkFrom G u v r → b ∉ r → q.length ≤ r.length := by
    intro r hr hbr
    rw [hlen]
    exact Nat.find_min' hex ⟨r, rfl, hr, hbr⟩
  exact ⟨q, hq, hqb, walkFrom_shortest_simple G b u v q hq hqb hmin⟩

private theorem path_append_edge {V E : Type*} (G : Multigraph V E)
    (u v : V) (q : List E) (d : E) (h : WalkFrom G u v (q ++ [d]))
    (hn : (q.map G.tgt).Nodup) (hu : u ∉ q.map G.tgt) (hv : v ∉ q.map G.tgt)
    (hd : G.tgt d = v) : IsPath G (q ++ [d]) := by
  refine ⟨by simp, walkFrom_walk G u v _ h, ?_, ?_⟩
  · simpa [List.nodup_append, hd] using And.intro hn hv
  · intro e he
    have hsrc := (walkFrom_endpoints G u v _ h).1 e he
    simpa [List.map_append, hsrc] using hu

private theorem last_path_or_cycle {V E : Type*} (G : Multigraph V E)
    (b : E) (u v : V) (s : List E) (hs : WalkFrom G u v s) (hb : b ∉ s)
    (d : E) (hd : d ∈ s.getLast?) :
    ∃ c, IsPath G c ∧ b ∉ c ∧ d ∈ c.getLast? ∧
      (WalkFrom G u v c ∨ WalkFrom G v v c) := by
  classical
  obtain ⟨t, heq⟩ := List.getLast?_eq_some_iff.mp hd
  obtain ⟨z, ht, hlast⟩ := walkFrom_split G u v t [d] (heq ▸ hs)
  have hzd : z = G.src d := hlast.1.symm
  have hdv : G.tgt d = v := hlast.2
  have htb : b ∉ t := fun hm => hb (heq ▸ List.mem_append_left [d] hm)
  have hdb : b ≠ d := by intro h; apply hb; simp [heq, h]
  obtain ⟨q, hq, hqb, hqn, hqu⟩ := walkFrom_shortest G b u (G.src d) t
    (hzd ▸ ht) htb
  by_cases hvq : v ∈ q.map G.tgt
  · obtain ⟨e, he, hev⟩ := List.mem_map.mp hvq
    obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp he
    obtain ⟨z, hz, hrest⟩ := walkFrom_split G u (G.src d) pre (e :: post) (hsplit ▸ hq)
    have hpost : WalkFrom G v (G.src d) post := hev ▸ hrest.2
    have hfull := walkFrom_append G v (G.src d) v post [d] hpost ⟨rfl, hdv⟩
    have hpn : (G.tgt e :: post.map G.tgt).Nodup := by
      simpa only [hsplit, List.map_append, List.map_cons] using
        (List.nodup_append.mp (by simpa [hsplit] using hqn)).2.1
    have hpostv : v ∉ post.map G.tgt := by simpa [hev] using (List.nodup_cons.mp hpn).1
    have hpostn := (List.nodup_cons.mp hpn).2
    have hpostb : b ∉ post := by
      intro hm
      apply hqb
      simp [hsplit, hm]
    refine ⟨post ++ [d], path_append_edge G v v post d hfull hpostn hpostv hpostv hdv,
      by simp [hpostb, hdb], by simp, Or.inr hfull⟩
  · have hfull := walkFrom_append G u (G.src d) v q [d] hq ⟨rfl, hdv⟩
    exact ⟨q ++ [d], path_append_edge G u v q d hfull hqn hqu hvq hdv,
      by simp [hqb, hdb], by simp, Or.inl hfull⟩

private theorem periodic_incident {V E : Type*} (G : Multigraph V E)
    (c : List E) (hne : c ≠ []) (hw : IsWalk G c)
    (hc : ∀ e ∈ c.getLast?, ∀ f ∈ c.head?, G.tgt e = G.src f) (n : ℕ) :
    G.tgt ((c)[n % c.length]'(Nat.mod_lt n (List.length_pos_iff.mpr hne))) =
      G.src ((c)[(n + 1) % c.length]'(Nat.mod_lt _ (List.length_pos_iff.mpr hne))) := by
  have hpos : 0 < c.length := List.length_pos_iff.mpr hne
  have hr : n % c.length < c.length := Nat.mod_lt n hpos
  have hmod : (n + 1) % c.length = (n % c.length + 1) % c.length := by
    simp [Nat.add_mod]
  by_cases hlt : n % c.length + 1 < c.length
  · simpa only [hmod, Nat.mod_eq_of_lt hlt] using
      List.isChain_iff_getElem.mp hw (n % c.length) hlt
  · have heq : n % c.length + 1 = c.length := by omega
    have hlast : (c)[n % c.length] ∈ c.getLast? := by
      rw [List.getLast?_eq_getElem?]
      have hidx : c.length - 1 = n % c.length := by omega
      simpa only [Option.mem_def, hidx] using List.getElem?_eq_getElem hr
    have hhead : (c)[0] ∈ c.head? := by
      simp [List.head?_eq_getElem?]
    simpa only [hmod, heq, Nat.mod_self] using hc _ hlast _ hhead

private theorem omnitig_cycle_contains {V E : Type*} (G : Multigraph V E)
    (w : List E) (hw : IsOmnitig G w) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i ≤ j) (hj : j < w.length) (c : List E) (hp : IsPath G c)
    (hc : WalkFrom G (G.src w[i]) (G.src w[i]) c)
    (d : E) (hd : d ∈ c.getLast?) (hda : d ≠ w[i - 1]) : w[j] ∈ c := by
  have hpos : 0 < c.length := List.length_pos_iff.mpr hp.1
  have hclosed : ∀ e ∈ c.getLast?, ∀ f ∈ c.head?, G.tgt e = G.src f := by
    intro e he f hf
    exact ((walkFrom_endpoints G _ _ _ hc).2 e he).trans
      ((walkFrom_endpoints G _ _ _ hc).1 f hf).symm
  have hforce : ∀ n (hn : i + n < w.length), (c)[n % c.length]'(Nat.mod_lt n hpos) = w[i + n] := by
    intro n
    induction n with
    | zero =>
      intro hn
      have hsrc : G.src (c)[0] = G.src w[i] := by
        apply (walkFrom_endpoints G _ _ _ hc).1
        simp [List.head?_eq_getElem?]
      by_contra hne
      apply hw.2.2 i i hi (by omega) hn c hp (c)[0] _ d hd hsrc
        ((walkFrom_endpoints G _ _ _ hc).2 d hd) _ hda
      · simp [List.head?_eq_getElem?]
      · simpa using hne
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hinc := periodic_incident G c hp.1 hp.2.1 hclosed n
      simp only [hprev] at hinc
      have hsrc : G.src ((c)[(n + 1) % c.length]'(Nat.mod_lt _ hpos)) = G.src w[i + (n + 1)] := by
        have hwinc := List.isChain_iff_getElem.mp hw.2.1 (i + n) (by omega)
        simpa only [Nat.add_assoc] using hinc.symm.trans hwinc
      have hr : (n + 1) % c.length < c.length := Nat.mod_lt _ hpos
      let r := (n + 1) % c.length
      have hrc : r < c.length := hr
      have hdrop := path_drop G c hp r hr
      have hW := walkFrom_suffix G _ _ c hc r hr
      have hdlast : d ∈ (c.drop r).getLast? := by
        simpa [List.getLast?_drop, Nat.not_le.mpr hrc] using hd
      have hhead : (c)[r] ∈ (c.drop r).head? := by
        simp [List.head?_eq_getElem?, List.getElem?_drop]
      by_contra hne
      exact hw.2.2 i (i + (n + 1)) hi (by omega) hn _ hdrop _ hhead d hdlast
        hsrc ((walkFrom_endpoints G _ _ _ hW).2 d hdlast) hne hda
  have hfinal := hforce (j - i) (by omega)
  have hf : (c)[(j - i) % c.length]'(Nat.mod_lt _ hpos) = w[j] := by
    simpa only [show i + (j - i) = j by omega] using hfinal
  rw [← hf]
  exact List.getElem_mem (Nat.mod_lt (j - i) hpos)

private theorem omnitig_last_edge {V E : Type*} (G : Multigraph V E)
    (w : List E) (hw : IsOmnitig G w) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i ≤ j) (hj : j < w.length) (s : List E)
    (hs : WalkFrom G (G.src w[j]) (G.src w[i]) s) (hb : w[j] ∉ s)
    (d : E) (hd : d ∈ s.getLast?) : d = w[i - 1] := by
  by_contra hda
  obtain ⟨c, hp, hcb, hcd, hW | hW⟩ := last_path_or_cycle G w[j] _ _ s hs hb d hd
  · let f := c.head hp.1
    have hf : f ∈ c.head? := List.head?_eq_some_head hp.1
    have hfb : f ≠ w[j] := fun h => hcb (h ▸ List.mem_of_mem_head? hf)
    exact hw.2.2 i j hi hij hj c hp f hf d hcd
      ((walkFrom_endpoints G _ _ _ hW).1 f hf)
      ((walkFrom_endpoints G _ _ _ hW).2 d hcd) hfb hda
  · exact hcb (omnitig_cycle_contains G w hw i j hi hij hj c hp hW d hcd hda)

private theorem omnitig_backward {V E : Type*} (G : Multigraph V E)
    (w : List E) (hw : IsOmnitig G w) (j : ℕ) (hj : j < w.length)
    (i : ℕ) (hij : i ≤ j) (s : List E)
    (hs : WalkFrom G (G.src w[j]) (G.src w[i]) s) (hb : w[j] ∉ s)
    (hlen : i ≤ s.length) :
    ∃ pre, s = pre ++ w.take i ∧ WalkFrom G (G.src w[j]) (G.src w[0]) pre := by
  induction i generalizing s with
  | zero => exact ⟨s, by simp, by simpa using hs⟩
  | succ k ih =>
    have hne : s ≠ [] := by intro h; simp [h] at hlen
    let d := s.getLast hne
    have hd : d ∈ s.getLast? := List.getLast?_eq_some_getLast hne
    have hde : d = w[k] := by
      simpa using omnitig_last_edge G w hw (k + 1) j (by omega) hij hj s hs hb d hd
    have hlast : s.getLast? = some w[k] := by simpa [hde] using hd
    obtain ⟨t, heq⟩ := List.getLast?_eq_some_iff.mp hlast
    obtain ⟨z, ht, hz⟩ := walkFrom_split G _ _ t [w[k]] (heq ▸ hs)
    have htz : WalkFrom G (G.src w[j]) (G.src w[k]) t := hz.1.symm ▸ ht
    have htb : w[j] ∉ t := fun hm => hb (heq ▸ List.mem_append_left _ hm)
    have htl : k ≤ t.length := by simp [heq] at hlen; omega
    obtain ⟨pre, hpre, hWF⟩ := ih (by omega) t htz htb htl
    refine ⟨pre, ?_, hWF⟩
    rw [heq, hpre, List.take_succ_eq_append_getElem (by omega), List.append_assoc]

private theorem suffix_of_suffix_append {E : Type*} (x pre y : List E)
    (hx : x <:+ pre ++ y) (hlen : x.length ≤ y.length) : x <:+ y := by
  rw [List.suffix_iff_eq_drop] at hx ⊢
  have hbig : pre.length ≤ (pre ++ y).length - x.length := by
    simp only [List.length_append]
    omega
  have hdrop : pre.drop ((pre ++ y).length - x.length) = [] :=
    List.drop_eq_nil_of_le hbig
  have hind : (pre ++ y).length - x.length - pre.length = y.length - x.length := by
    simp only [List.length_append]
    omega
  simpa only [List.drop_append, hdrop, List.nil_append, hind] using hx

private theorem omnitig_prefix_stable {V E : Type*} (G : Multigraph V E)
    (w : List E) (hw : IsOmnitig G w) (j : ℕ) (hj : j < w.length)
    (c : List E) (hne : c ≠ []) (hc : WalkFrom G (G.src w[j]) (G.src w[j]) c)
    (hb : w[j] ∉ c) : w.take j <:+ w.take j ++ c := by
  obtain ⟨C, hC, hlen, hCb, _⟩ := long_buffer G (G.src w[j]) c hc hne w[j] w[j] hb hb j
  obtain ⟨pre, heq, hpre⟩ := omnitig_backward G w hw j hj j (by omega) C hC hCb hlen
  have hpb : w[j] ∉ w.take j := fun hm => hCb (heq ▸ List.mem_append_right pre hm)
  have hpreb : w[j] ∉ pre := fun hm => hCb (heq ▸ List.mem_append_left _ hm)
  have hpw : WalkFrom G (G.src w[0]) (G.src w[j]) (w.take j) := by
    simpa using walkFrom_segment G w hw.2.1 0 j (by omega)
  have hfull : WalkFrom G (G.src w[j]) (G.src w[j]) (pre ++ (w.take j ++ c)) :=
    walkFrom_append G _ _ _ pre _ hpre (walkFrom_append G _ _ _ _ _ hpw hc)
  have hfullb : w[j] ∉ pre ++ (w.take j ++ c) := by simp [hpreb, hpb, hb]
  obtain ⟨pre', heq', _⟩ := omnitig_backward G w hw j hj j (by omega) _ hfull hfullb
    (by simp; omega)
  apply suffix_of_suffix_append (w.take j) pre (w.take j ++ c)
  · exact ⟨pre', heq'.symm⟩
  · simp only [List.length_append, List.length_take]
    omega

private def cyclicAt {E : Type*} (A : List E) (hne : A ≠ []) (n : ℕ) : E :=
  A[n % A.length]'(Nat.mod_lt n (List.length_pos_iff.mpr hne))

private def circularSegment {E : Type*} (A : List E) (hne : A ≠ []) (p n : ℕ) : List E :=
  List.ofFn fun k : Fin n => cyclicAt A hne (p + k)

private theorem circularSegment_succ {E : Type*} (A : List E) (hne : A ≠ []) (p n : ℕ) :
    circularSegment A hne p (n + 1) =
      circularSegment A hne p n ++ [cyclicAt A hne (p + n)] := by
  rw [circularSegment, List.ofFn_succ_last]
  rfl

private theorem circularSegment_add {E : Type*} (A : List E) (hne : A ≠ []) (p m n : ℕ) :
    circularSegment A hne p (m + n) =
      circularSegment A hne p m ++ circularSegment A hne (p + m) n := by
  simp [circularSegment, List.ofFn_add, Nat.add_assoc]

private theorem circularSegment_walkFrom {V E : Type*} (G : Multigraph V E)
    (A : List E) (hne : A ≠ []) (hw : IsWalk G A)
    (hc : ∀ e ∈ A.getLast?, ∀ f ∈ A.head?, G.tgt e = G.src f) (p n : ℕ) :
    WalkFrom G (G.src (cyclicAt A hne p)) (G.src (cyclicAt A hne (p + n)))
      (circularSegment A hne p n) := by
  induction n with
  | zero => simp [circularSegment, WalkFrom]
  | succ n ih =>
    rw [circularSegment_succ]
    apply walkFrom_append G _ (G.src (cyclicAt A hne (p + n))) _ _ _ ih
    refine ⟨rfl, ?_⟩
    simpa only [cyclicAt, WalkFrom, Nat.add_assoc] using periodic_incident G A hne hw hc (p + n)

private theorem cyclicAt_eventually {E : Type*} (A : List E) (hne : A ≠ [])
    (p : ℕ) (b : E) (hb : b ∈ A) : ∃ d, cyclicAt A hne (p + d) = b := by
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hb
  have hpos : 0 < A.length := List.length_pos_iff.mpr hne
  have hr := Nat.mod_lt p hpos
  let d := A.length + k - p % A.length
  have hsum : p % A.length + d = A.length + k := by dsimp [d]; omega
  have hmod : (p + d) % A.length = k := by
    calc
      (p + d) % A.length = (p % A.length + d) % A.length := by simp [Nat.add_mod]
      _ = (A.length + k) % A.length := by rw [hsum]
      _ = k := by simp [Nat.mod_eq_of_lt hk]
  exact ⟨d, by simpa only [cyclicAt, hmod] using he⟩

private theorem omnitig_extend_prefix {V E : Type*} (G : Multigraph V E)
    (w : List E) (hw : IsOmnitig G w) (A : List E) (hA : IsCircularCovering G A)
    (j : ℕ) (hj0 : 0 < j) (hj : j < w.length)
    (hs : IsCircularSubwalk (w.take j) A) : IsCircularSubwalk (w.take (j + 1)) A := by
  classical
  obtain ⟨p, hp⟩ := hs
  have hmatch : ∀ k (hk : k < j), cyclicAt A hA.1 (p + k) = w[k] := by
    intro k hk
    have hm := hp k (by simp; omega)
    obtain ⟨hidx, he⟩ := List.getElem?_eq_some_iff.mp hm
    simpa only [cyclicAt, List.getElem_take] using he
  have hjle : j ≤ w.length := by omega
  have hseg : circularSegment A hA.1 p j = w.take j := by
    apply List.ext_getElem (by simp [circularSegment, Nat.min_eq_left hjle])
    intro k hk hkw
    simpa [circularSegment] using hmatch k (by simpa [circularSegment] using hk)
  have hex := cyclicAt_eventually A hA.1 (p + j) w[j] (hA.2.2.2 w[j])
  let d := Nat.find hex
  have hd : cyclicAt A hA.1 (p + j + d) = w[j] := Nat.find_spec hex
  let c := circularSegment A hA.1 (p + j) d
  have hsrc : G.src (cyclicAt A hA.1 (p + j)) = G.src w[j] := by
    have hinc := periodic_incident G A hA.1 hA.2.1 hA.2.2.1 (p + (j - 1))
    change G.tgt (cyclicAt A hA.1 (p + (j - 1))) =
      G.src (cyclicAt A hA.1 (p + (j - 1) + 1)) at hinc
    have hwinc := List.isChain_iff_getElem.mp hw.2.1 (j - 1) (by omega)
    have hprev := hmatch (j - 1) (by omega)
    have hinc' : G.tgt w[j - 1] = G.src (cyclicAt A hA.1 (p + j)) := by
      simpa only [show p + (j - 1) + 1 = p + j by omega, hprev] using hinc
    simpa only [show j - 1 + 1 = j by omega] using hinc'.symm.trans hwinc
  have hc : WalkFrom G (G.src w[j]) (G.src w[j]) c := by
    have hh := circularSegment_walkFrom G A hA.1 hA.2.1 hA.2.2.1 (p + j) d
    simpa only [hsrc, hd] using hh
  have hcb : w[j] ∉ c := by
    intro hm
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
    have hkd : k < d := by simpa [c, circularSegment] using hk
    have he' : cyclicAt A hA.1 (p + j + k) = w[j] := by
      simpa [c, circularSegment] using he
    exact Nat.find_min hex hkd he'
  have hstable : w.take j <:+ circularSegment A hA.1 p (j + d) := by
    rw [circularSegment_add, hseg]
    by_cases hd0 : d = 0
    · simp [hd0, circularSegment]
    · exact omnitig_prefix_stable G w hw j hj c
        (by simpa [c, circularSegment, List.ofFn_eq_nil_iff] using hd0) hc hcb
  refine ⟨p + d, ?_⟩
  intro k hk
  have hk' : k < j + 1 := by simpa [Nat.min_eq_left (by omega : j + 1 ≤ w.length)] using hk
  by_cases hkj : k < j
  · have ht : k < (w.take j).length := by simp; omega
    have he := hstable.getElem ht
    have he' : cyclicAt A hA.1 (p + d + k) = w[k] := by
      simpa [circularSegment, Nat.min_eq_left hjle, show j + d - j = d by omega,
        Nat.add_assoc] using he.symm
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨Nat.mod_lt _ (List.length_pos_iff.mpr hA.1),
      by simpa only [cyclicAt, List.getElem_take] using he'⟩
  · have hkeq : k = j := by omega
    subst k
    have he' : cyclicAt A hA.1 (p + d + j) = w[j] := by
      simpa only [show p + d + j = p + j + d by omega] using hd
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨Nat.mod_lt _ (List.length_pos_iff.mpr hA.1),
      by simpa only [cyclicAt, List.getElem_take] using he'⟩

/-- Omnitigs are safe (Theorem 1, (2) ⇒ (1)). -/
theorem IsOmnitig.isSafe {w : List E} (hw : IsOmnitig G w) : IsSafe G w := by
  intro A hA
  have hprefix : ∀ n, n ≤ w.length → IsCircularSubwalk (w.take n) A := by
    intro n
    induction n with
    | zero => intro _; exact ⟨0, by simp⟩
    | succ n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst n
        have hwpos : 0 < w.length := List.length_pos_iff.mpr hw.1
        have hs := circularSubwalk_singleton w[0] A (hA.2.2.2 w[0])
        simpa [List.take_succ_eq_append_getElem hwpos] using hs
      · exact omnitig_extend_prefix G w hw A hA n (by omega) (by omega) (ih (by omega))
  simpa using hprefix w.length (by omega)

/-- Safe walks are omnitigs (Theorem 1, (1) ⇒ (2)), when a circular edge-covering walk exists
(otherwise every walk is vacuously safe). -/
theorem isOmnitig_of_isSafe {w : List E} (hne : w ≠ []) (hwalk : IsWalk G w)
    (hA : ∃ A, IsCircularCovering G A) (hs : IsSafe G w) : IsOmnitig G w := by
  classical
  refine ⟨hne, hwalk, ?_⟩
  intro i j hi hij hj p hp f hf l hl hsrc htgt hfirst hlast
  have hiw : i < w.length := by omega
  have him : i - 1 < w.length := by omega
  let a := w[i - 1]
  let b := w[j]
  let u := G.src b
  let v := G.src w[i]
  have hinc : G.tgt a = v := by
    have hstep := List.isChain_iff_getElem.mp hwalk (i - 1) (by omega)
    simpa only [show i - 1 + 1 = i by omega] using hstep
  have hPa : a ∉ p := path_tgt_ne G p hp l a hl
    (hinc.trans htgt.symm) hlast.symm
  have hPb : b ∉ p := path_src_ne G p hp f b hf hsrc.symm hfirst.symm
  have hP : WalkFrom G u v p := by
    apply walkFrom_of_walk G u v p hp.1 hp.2.1
    · intro e he
      have heq : e = f := Option.mem_unique he hf
      simpa [heq] using hsrc
    · intro e he
      have heq : e = l := Option.mem_unique he hl
      simpa [heq] using htgt
  have hS := walkFrom_segment G w hwalk i (j - i) (by omega)
  have hSv : WalkFrom G v u ((w.drop i).take (j - i)) := by
    simpa only [show i + (j - i) = j by omega] using hS
  obtain ⟨q, hq, havoid⟩ := walkFrom_trim G v u _ hSv
  have hqa : a ∉ q := by
    intro ha
    exact (havoid a ha).2 hinc
  have hqb : b ∉ q := by
    intro hb
    exact (havoid b hb).1 rfl
  let D := p ++ q
  have hD : WalkFrom G u u D := walkFrom_append G u v u p q hP hq
  have hDne : D ≠ [] := by
    intro h
    exact hp.1 (List.append_eq_nil_iff.mp h).1
  have hDa : a ∉ D := by simpa [D] using And.intro hPa hqa
  have hDb : b ∉ D := by simpa [D] using And.intro hPb hqb
  let L := j - (i - 1)
  have hL : 0 < L := by dsimp [L]; omega
  obtain ⟨C, hC, hCL, hCa, hCb⟩ := long_buffer G u D hD hDne a b hDa hDb L
  obtain ⟨A, hAc⟩ := hA
  have hB := bufferEdges_covering G b C A hC hAc
  obtain ⟨start, hstart⟩ := hs _ hB
  have hbj := hstart j hj
  have hai := hstart (i - 1) him
  have hsum : start + (i - 1) + L = start + j := by dsimp [L]; omega
  have hno := bufferEdges_noPair a b C A L (start + (i - 1)) hL hCL hCa hCb
    (by simpa only [hsum] using hbj)
  exact hno hai

end Cslib.Bioinformatics.Assembly.Omnitig
