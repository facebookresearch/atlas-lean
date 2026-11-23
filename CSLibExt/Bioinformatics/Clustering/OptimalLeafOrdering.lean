/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Tactic.Ring

/-!
# Optimal leaf ordering of a dendrogram

A hierarchical clustering returns a rooted binary tree (`Dendrogram`) whose leaves are the
clustered objects. Drawing it fixes, at every internal node, which child goes left; the
`2 ^ (number of internal nodes)` choices give the leaf orders `orderings t`. Given a similarity
`S : α → α → ℝ`, the *optimal leaf ordering* problem asks for an order maximizing
`adjScore S o`, the sum of `S` over adjacent leaves.

Bar-Joseph, Gifford and Jaakkola solve it by dynamic programming over the tree: for a node `v`
and leaves `i`, `j`, let `M(v, i, j)` be the best score of an order of the leaves below `v` that
starts with `i` and ends with `j`. If `v` has children `w`, `x` and `i` lies below `w`, `j`
below `x`, then
`M(v, i, j) = max_{k below w, l below x} M(w, i, k) + S(k, l) + M(x, l, j)`
(and symmetrically with the children swapped). `bestEnds` is this recursion, with `⊥` for
impossible end pairs.

## Main results

* `length_orderings`: a dendrogram with `m` internal nodes has `2 ^ m` leaf orders (counted
  with the flip choices, as a list).
* `perm_of_mem_orderings`: every leaf order is a permutation of the leaves.
* `bestEnds_eq_optEnds`: **correctness of the recursion**: `bestEnds S t i j` is the maximum of
  `adjScore S` over the leaf orders of `t` that start at `i` and end at `j` (`⊥` if none).
* `optScore_ne_bot`: an optimal leaf order exists.
* `optScore_eq_sup_bestEnds`: the optimal leaf-ordering score is the maximum of `bestEnds`
  over end pairs.

Leaf labels need not be distinct: the statements are about the orders produced by flipping,
whatever the labels. The running-time analysis of the paper (`O(n⁴)` for the plain recursion,
`O(n³)` with their pruning) is not formalized.

## References

* Z. Bar-Joseph, D. K. Gifford and T. S. Jaakkola, "Fast optimal leaf ordering for
  hierarchical clustering", *Bioinformatics* 17 (Suppl. 1) (2001), S22–S29.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Clustering.OptimalLeafOrdering

/-- A rooted binary tree whose leaves are labeled by `α`: the shape of a dendrogram
(merge heights are irrelevant for leaf ordering). -/
inductive Dendrogram (α : Type*) where
  /-- A single object. -/
  | leaf : α → Dendrogram α
  /-- The merge of two clusters. -/
  | node : Dendrogram α → Dendrogram α → Dendrogram α

namespace Dendrogram

variable {α : Type*}

/-- The leaves of a dendrogram, left to right. -/
def leaves : Dendrogram α → List α
  | leaf a => [a]
  | node l r => leaves l ++ leaves r

/-- The number of internal (merge) nodes. -/
def numInternal : Dendrogram α → ℕ
  | leaf _ => 0
  | node l r => numInternal l + numInternal r + 1

/-- The leaf orders obtained by choosing, at each internal node, which child is drawn first.
Each choice pattern contributes one entry, so the list has `2 ^ numInternal t` entries. -/
def orderings : Dendrogram α → List (List α)
  | leaf a => [[a]]
  | node l r =>
      (orderings l).flatMap (fun u => (orderings r).map (u ++ ·)) ++
        (orderings r).flatMap (fun v => (orderings l).map (v ++ ·))

end Dendrogram

open Dendrogram

variable {α : Type*}

/-- The score of a leaf order: the sum of the similarities of adjacent leaves. -/
def adjScore (S : α → α → ℝ) : List α → ℝ
  | a :: b :: t => S a b + adjScore S (b :: t)
  | _ => 0

/-- The best score among the leaf orders of `t` (never `⊥`: `optScore_ne_bot`). -/
noncomputable def optScore (S : α → α → ℝ) (t : Dendrogram α) : WithBot ℝ :=
  ((orderings t).map (adjScore S)).maximum

/-- The best score among the leaf orders of `t` that start with `i` and end with `j`
(`⊥` if there is none). -/
noncomputable def optEnds [DecidableEq α] (S : α → α → ℝ) (t : Dendrogram α) (i j : α) :
    WithBot ℝ :=
  (((orderings t).filter (fun o => o.head? = some i ∧ o.getLast? = some j)).map
    (adjScore S)).maximum

/-- One side of the recursion: the left part ranges over orders of a subtree with leaves `Ll`
and best-score table `Ml`, the right part over a subtree with leaves `Lr` and table `Mr`; the
two are joined at the adjacent pair `(k, l)`. -/
noncomputable def joinEnds (S : α → α → ℝ) (Ml Mr : α → α → WithBot ℝ) (Ll Lr : List α)
    (i j : α) : WithBot ℝ :=
  (Ll.flatMap fun k => Lr.map fun l => Ml i k + ((S k l : ℝ) : WithBot ℝ) + Mr l j).foldr
    max ⊥

/-- The dynamic program of Bar-Joseph, Gifford and Jaakkola: `bestEnds S t i j` is computed
from the tables of the two children, trying both child orders. -/
noncomputable def bestEnds [DecidableEq α] (S : α → α → ℝ) : Dendrogram α → α → α → WithBot ℝ
  | leaf a, i, j => if i = a ∧ j = a then 0 else ⊥
  | node l r, i, j =>
      max (joinEnds S (bestEnds S l) (bestEnds S r) (leaves l) (leaves r) i j)
        (joinEnds S (bestEnds S r) (bestEnds S l) (leaves r) (leaves l) i j)

/-- A dendrogram with `m` internal nodes has `2 ^ m` leaf orders (one per flip pattern). -/
theorem length_orderings (t : Dendrogram α) : (orderings t).length = 2 ^ numInternal t := by
  induction t with
  | leaf a => simp [orderings, numInternal]
  | node l r hl hr =>
      simp [orderings, numInternal, List.length_flatMap, hl, hr, pow_add, pow_succ]
      ring

/-- Every leaf order of `t` is a permutation of its leaves. -/
theorem perm_of_mem_orderings {t : Dendrogram α} {o : List α} (h : o ∈ orderings t) :
    o.Perm (leaves t) := by
  induction t generalizing o with
  | leaf a =>
      simp only [orderings, List.mem_singleton] at h
      subst o
      exact List.Perm.refl _
  | node l r hl hr =>
      simp only [orderings, List.mem_append, List.mem_flatMap, List.mem_map] at h
      rcases h with ⟨u, hu, v, hv, rfl⟩ | ⟨v, hv, u, hu, rfl⟩
      · exact (hl hu).append (hr hv)
      · exact ((hr hv).append (hl hu)).trans List.perm_append_comm

private theorem fold_max_le (L : List (WithBot ℝ)) (c : WithBot ℝ) :
    L.foldr max ⊥ ≤ c ↔ ∀ x ∈ L, x ≤ c := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

private theorem le_fold_max (L : List (WithBot ℝ)) (x : WithBot ℝ) (h : x ∈ L) :
    x ≤ L.foldr max ⊥ :=
  (fold_max_le L _).mp le_rfl x h

private theorem maximum_map_le (O : List (List α)) (f : List α → ℝ) (c : WithBot ℝ) :
    (O.map f).maximum ≤ c ↔ ∀ o ∈ O, (f o : WithBot ℝ) ≤ c := by
  constructor
  · intro h o ho
    exact (List.le_maximum_of_mem' (List.mem_map.mpr ⟨o, ho, rfl⟩)).trans h
  · intro h
    apply List.maximum_le_of_forall_le
    rintro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    exact h o ho

private theorem leaves_ne_nil (t : Dendrogram α) : leaves t ≠ [] := by
  induction t with
  | leaf a => simp [leaves]
  | node l r hl hr => simp [leaves, hl]

private theorem ordering_ne_nil (t : Dendrogram α) (o : List α) (h : o ∈ orderings t) :
    o ≠ [] := by
  intro he
  have hp := perm_of_mem_orderings h
  rw [he] at hp
  exact leaves_ne_nil t (List.Perm.nil_eq hp).symm

private theorem ordering_ends (t : Dendrogram α) (o : List α) (h : o ∈ orderings t) :
    ∃ i j, o.head? = some i ∧ o.getLast? = some j ∧ i ∈ leaves t ∧ j ∈ leaves t := by
  have hn := ordering_ne_nil t o h
  have hp := perm_of_mem_orderings h
  refine ⟨o.head hn, o.getLast hn, List.head?_eq_some_head hn,
    List.getLast?_eq_some_getLast hn,
    ?_, ?_⟩
  · exact hp.mem_iff.mp (List.mem_of_head? (List.head?_eq_some_head hn))
  · exact hp.mem_iff.mp (List.mem_of_getLast? (List.getLast?_eq_some_getLast hn))

private theorem score_append (S : α → α → ℝ) (u v : List α) (k l : α)
    (hk : u.getLast? = some k) (hl : v.head? = some l) :
    adjScore S (u ++ v) = adjScore S u + S k l + adjScore S v := by
  induction u with
  | nil => simp at hk
  | cons a u ih =>
      cases u with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hk
          obtain ⟨v, rfl⟩ := List.head?_eq_some_iff.mp hl
          subst k
          simp [adjScore]
      | cons b u =>
          simp only [List.getLast?_cons_cons] at hk
          change S a b + adjScore S ((b :: u) ++ v) = _
          rw [ih hk]
          simp only [adjScore]
          ring

private theorem optEnds_le [DecidableEq α] (S : α → α → ℝ) (t : Dendrogram α)
    (i j : α) (c : WithBot ℝ) :
    optEnds S t i j ≤ c ↔
      ∀ o ∈ orderings t, o.head? = some i → o.getLast? = some j →
        (adjScore S o : WithBot ℝ) ≤ c := by
  rw [optEnds, maximum_map_le]
  simp only [List.mem_filter, decide_eq_true_eq, and_imp]

private theorem score_le_optEnds [DecidableEq α] (S : α → α → ℝ) (t : Dendrogram α)
    (o : List α) (i j : α) (ho : o ∈ orderings t)
    (hi : o.head? = some i) (hj : o.getLast? = some j) :
    (adjScore S o : WithBot ℝ) ≤ optEnds S t i j :=
  (optEnds_le S t i j _).mp le_rfl o ho hi hj

private theorem optEnds_cases [DecidableEq α] (S : α → α → ℝ) (t : Dendrogram α)
    (i j : α) :
    optEnds S t i j = ⊥ ∨
      ∃ o ∈ orderings t, o.head? = some i ∧ o.getLast? = some j ∧
        optEnds S t i j = (adjScore S o : WithBot ℝ) := by
  cases he : optEnds S t i j with
  | bot => exact Or.inl rfl
  | coe s =>
      have hs := (List.maximum_eq_coe_iff.mp he).1
      obtain ⟨o, ho, hscore⟩ := List.mem_map.mp hs
      have hf : o ∈ orderings t ∧ o.head? = some i ∧ o.getLast? = some j := by
        simpa only [List.mem_filter, decide_eq_true_eq] using ho
      obtain ⟨ho, hi, hj⟩ := hf
      refine Or.inr ⟨o, ho, hi, hj, ?_⟩
      exact congrArg (fun s : ℝ => (s : WithBot ℝ)) hscore.symm

private theorem join_le [DecidableEq α] (S : α → α → ℝ) (l r : Dendrogram α)
    (i j : α) (c : WithBot ℝ)
    (h : ∀ u ∈ orderings l, ∀ v ∈ orderings r,
      u.head? = some i → v.getLast? = some j → (adjScore S (u ++ v) : WithBot ℝ) ≤ c) :
    joinEnds S (optEnds S l) (optEnds S r) (leaves l) (leaves r) i j ≤ c := by
  unfold joinEnds
  apply (fold_max_le _ c).mpr
  intro z hz
  obtain ⟨k, hk, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  rcases optEnds_cases S l i k with hb | ⟨u, hu, hui, huk, hus⟩
  · simp [hb]
  rcases optEnds_cases S r a j with hb | ⟨v, hv, hva, hvj, hvs⟩
  · simp [hb]
  rw [hus, hvs, ← WithBot.coe_add, ← WithBot.coe_add,
    ← score_append S u v k a huk hva]
  exact h u hu v hv hui hvj

private theorem score_le_join [DecidableEq α] (S : α → α → ℝ) (l r : Dendrogram α)
    (u v : List α) (i j : α) (hu : u ∈ orderings l) (hv : v ∈ orderings r)
    (hi : u.head? = some i) (hj : v.getLast? = some j) :
    (adjScore S (u ++ v) : WithBot ℝ) ≤
      joinEnds S (optEnds S l) (optEnds S r) (leaves l) (leaves r) i j := by
  obtain ⟨a, k, _, huk, _, hk⟩ := ordering_ends l u hu
  obtain ⟨b, d, hvb, _, hb, _⟩ := ordering_ends r v hv
  calc
    (adjScore S (u ++ v) : WithBot ℝ) =
        (adjScore S u : WithBot ℝ) + (S k b : WithBot ℝ) + (adjScore S v : WithBot ℝ) := by
          rw [score_append S u v k b huk hvb]
          simp only [WithBot.coe_add]
    _ ≤ optEnds S l i k + (S k b : WithBot ℝ) + optEnds S r b j :=
      add_le_add (add_le_add (score_le_optEnds S l u i k hu hi huk) le_rfl)
        (score_le_optEnds S r v b j hv hvb hj)
    _ ≤ joinEnds S (optEnds S l) (optEnds S r) (leaves l) (leaves r) i j := by
      apply le_fold_max
      exact List.mem_flatMap.mpr ⟨k, hk, List.mem_map.mpr ⟨b, hb, rfl⟩⟩

/-- **Correctness of the optimal leaf ordering recursion** (Bar-Joseph, Gifford and
Jaakkola 2001): the dynamic program computes, for every end pair `(i, j)`, the best score of
a leaf order of `t` starting at `i` and ending at `j`. -/
theorem bestEnds_eq_optEnds [DecidableEq α] (S : α → α → ℝ) (t : Dendrogram α) (i j : α) :
    bestEnds S t i j = optEnds S t i j := by
  induction t generalizing i j with
  | leaf a =>
      by_cases hi : i = a <;> by_cases hj : j = a
      · subst i
        subst j
        simp [bestEnds, optEnds, orderings, adjScore]
      · simp [bestEnds, optEnds, orderings, hi, hj, Ne.symm hj]
      · simp [bestEnds, optEnds, orderings, hi, hj, Ne.symm hi]
      · simp [bestEnds, optEnds, orderings, hi, hj, Ne.symm hi]
  | node l r hl hr =>
      have hlt : bestEnds S l = optEnds S l := funext fun i => funext fun j => hl i j
      have hrt : bestEnds S r = optEnds S r := funext fun i => funext fun j => hr i j
      rw [bestEnds, hlt, hrt]
      apply le_antisymm
      · apply max_le
        · apply join_le
          intro u hu v hv hi hj
          apply score_le_optEnds S (node l r) (u ++ v) i j
          · exact List.mem_append.mpr (Or.inl
              (List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨v, hv, rfl⟩⟩))
          · rw [List.head?_append_of_ne_nil u (ordering_ne_nil l u hu)]
            exact hi
          · rw [List.getLast?_append_of_ne_nil u (ordering_ne_nil r v hv)]
            exact hj
        · apply join_le
          intro v hv u hu hi hj
          apply score_le_optEnds S (node l r) (v ++ u) i j
          · exact List.mem_append.mpr (Or.inr
              (List.mem_flatMap.mpr ⟨v, hv, List.mem_map.mpr ⟨u, hu, rfl⟩⟩))
          · rw [List.head?_append_of_ne_nil v (ordering_ne_nil r v hv)]
            exact hi
          · rw [List.getLast?_append_of_ne_nil v (ordering_ne_nil l u hu)]
            exact hj
      · apply (optEnds_le S (node l r) i j _).mpr
        intro o ho hi hj
        simp only [orderings, List.mem_append, List.mem_flatMap, List.mem_map] at ho
        rcases ho with ⟨u, hu, v, hv, rfl⟩ | ⟨v, hv, u, hu, rfl⟩
        · rw [List.head?_append_of_ne_nil u (ordering_ne_nil l u hu)] at hi
          rw [List.getLast?_append_of_ne_nil u (ordering_ne_nil r v hv)] at hj
          exact (score_le_join S l r u v i j hu hv hi hj).trans (le_max_left _ _)
        · rw [List.head?_append_of_ne_nil v (ordering_ne_nil r v hv)] at hi
          rw [List.getLast?_append_of_ne_nil v (ordering_ne_nil l u hu)] at hj
          exact (score_le_join S r l v u i j hv hu hi hj).trans (le_max_right _ _)

/-- The optimal leaf-ordering score is the best `bestEnds` value over end pairs of leaves. -/
theorem optScore_eq_sup_bestEnds [DecidableEq α] (S : α → α → ℝ) (t : Dendrogram α) :
    optScore S t =
      ((leaves t).flatMap fun i => (leaves t).map fun j => bestEnds S t i j).foldr max ⊥ := by
  simp only [bestEnds_eq_optEnds]
  apply le_antisymm
  · apply (maximum_map_le (orderings t) (adjScore S) _).mpr
    intro o ho
    obtain ⟨i, j, hi, hj, hil, hjl⟩ := ordering_ends t o ho
    apply (score_le_optEnds S t o i j ho hi hj).trans
    apply le_fold_max
    exact List.mem_flatMap.mpr ⟨i, hil, List.mem_map.mpr ⟨j, hjl, rfl⟩⟩
  · apply (fold_max_le _ _).mpr
    intro x hx
    obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    apply (optEnds_le S t i j _).mpr
    intro o ho _ _
    exact List.le_maximum_of_mem' (List.mem_map.mpr ⟨o, ho, rfl⟩)

/-- Every dendrogram has a leaf order, so the optimal score is a real number. -/
theorem optScore_ne_bot (S : α → α → ℝ) (t : Dendrogram α) : optScore S t ≠ ⊥ := by
  rw [optScore, Ne, List.maximum_eq_bot, List.map_eq_nil_iff, ← List.length_eq_zero_iff,
    length_orderings]
  exact (pow_pos two_pos _).ne'

end Cslib.Bioinformatics.Clustering.OptimalLeafOrdering
