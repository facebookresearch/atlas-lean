/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Data.UnionFind.Lemmas
public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Union
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Function.Iterate

import all Batteries.Data.UnionFind.Basic

/-!
# Rank bounds for union by rank with path compression

Tarjan and van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984)
245–281, §2. For the canonical Batteries union-find (`Batteries.UnionFind`: linking by rank,
`find` with path compression), every structure built from the empty one by `push` (make-set),
`find` and `union`:

* `two_pow_rank_le_classSize`: every root `r` satisfies `2 ^ rank r ≤ |class of r|`, the class
  being the set of nodes whose root is `r` (Lemma 2 of Tarjan–van Leeuwen, linking by rank,
  for the roots: compression changes neither ranks nor classes);
* `rank_le_log`: every rank is at most `⌊log₂ n⌋`, where `n` is the number of nodes;
* `iterate_parent_log`: following `⌊log₂ n⌋` parent pointers from any node reaches its root, so
  no find path has more than `⌊log₂ n⌋` edges (Corollary 2 of Tarjan–van Leeuwen).

In Tarjan–van Leeuwen, `rank` is the height in the forest without compression; in Batteries
it is the stored rank, which is the same number since compression never updates ranks (their
§3), and the proofs here use only the stored ranks.
-/

open Batteries

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionByRank

/-- **Class size in a union-find structure.** The number of nodes `i < n` whose root is `r`,
where `n` is the number of nodes of the structure. -/
def classSize (uf : UnionFind) (r : ℕ) : ℕ :=
  ((Finset.range uf.size).filter (fun i => uf.rootD i = r)).card

/-- **Union-find structures built by make-set, find and union.** The structures obtained from
the empty structure by `push` (make-set), `find` (with path compression) and `union` (two finds
and a link by rank), as in the operation sequences analysed by Tarjan and van Leeuwen,
*Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984), §1. -/
inductive Reachable : UnionFind → Prop
  | empty : Reachable UnionFind.empty
  | push {uf : UnionFind} : Reachable uf → Reachable uf.push
  | find {uf : UnionFind} (x : Fin uf.size) : Reachable uf → Reachable (uf.find x).1
  | union {uf : UnionFind} (x y : Fin uf.size) : Reachable uf → Reachable (uf.union x y)

/-- **Rank invariant of linking by rank.** Every root `r` of the structure has at least
`2 ^ rank r` nodes in its class. -/
def RankBounded (uf : UnionFind) : Prop :=
  ∀ r, r < uf.size → uf.parent r = r → 2 ^ uf.rank r ≤ classSize uf r

theorem classSize_le_size (uf : UnionFind) (r : ℕ) : classSize uf r ≤ uf.size := by
  unfold classSize
  exact (Finset.card_filter_le _ _).trans (by simp)

private theorem rootD_of_not_lt {uf : UnionFind} {i : ℕ} (h : ¬ i < uf.size) :
    uf.rootD i = i := by
  simp [UnionFind.rootD, h]

private theorem rank_of_not_lt {uf : UnionFind} {i : ℕ} (h : ¬ i < uf.size) :
    uf.rank i = 0 := by
  simp [UnionFind.rank, UnionFind.rankD, h]

theorem size_push (uf : UnionFind) : uf.push.size = uf.size + 1 := by
  simp [UnionFind.size, UnionFind.push]

theorem rank_find (uf : UnionFind) (x : Fin uf.size) (i : ℕ) :
    (uf.find x).1.rank i = uf.rank i :=
  UnionFind.rankD_findAux

theorem size_union (uf : UnionFind) (x y : Fin uf.size) :
    (uf.union x y).size = uf.size := by
  simp only [UnionFind.union]
  simp [UnionFind.size, UnionFind.link]

private theorem rootD_union (uf : UnionFind) (x y : Fin uf.size) (i : ℕ) :
    (uf.union x y).rootD i =
      if uf.rootD i = uf.rootD x ∨ uf.rootD i = uf.rootD y then
        (if uf.rank (uf.rootD y) < uf.rank (uf.rootD x) then uf.rootD x else uf.rootD y)
      else uf.rootD i := by
  simp only [UnionFind.union]
  rw [UnionFind.rootD_link_eq_ite]
  · simp only [UnionFind.find_root_1, UnionFind.find_root_2, rank_find]
  · rw [← UnionFind.rootD_eq_self]
    simp only [UnionFind.find_root_1, UnionFind.find_root_2, UnionFind.rootD_rootD]

private theorem card_filter_or {s : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ} (hab : a ≠ b) :
    (s.filter (fun i => f i = a ∨ f i = b)).card =
      (s.filter (fun i => f i = a)).card + (s.filter (fun i => f i = b)).card := by
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro i _ h1 h2
  exact hab (h1.symm.trans h2)

theorem rankBounded_empty : RankBounded UnionFind.empty := by
  intro r hr
  simp [UnionFind.empty, UnionFind.mkEmpty, UnionFind.size] at hr

theorem rankBounded_push {uf : UnionFind} (h : RankBounded uf) : RankBounded uf.push := by
  intro r hr hroot
  rw [size_push] at hr
  have hrank : uf.push.rank r = uf.rank r := UnionFind.rank_push
  have hpar : uf.push.parent r = uf.parent r := UnionFind.parent_push
  have hcls : classSize uf.push r =
      ((insert uf.size (Finset.range uf.size)).filter (fun i => uf.rootD i = r)).card := by
    simp only [classSize, size_push, UnionFind.root_push, Finset.range_add_one]
  rw [hrank, hcls, Finset.filter_insert, rootD_of_not_lt (lt_irrefl _)]
  by_cases hrn : r = uf.size
  · subst hrn
    rw [ite_eq_left rfl, rank_of_not_lt (lt_irrefl _), pow_zero, Nat.one_le_iff_ne_zero]
    simp
  · rw [ite_eq_right (Ne.symm hrn)]
    exact h r (by omega) (hpar ▸ hroot)

theorem rankBounded_find {uf : UnionFind} (h : RankBounded uf) (x : Fin uf.size) :
    RankBounded (uf.find x).1 := by
  intro r hr hroot
  rw [UnionFind.find_size] at hr
  have hroot' : uf.parent r = r := by
    rw [← UnionFind.rootD_eq_self] at hroot ⊢
    rwa [UnionFind.find_root_1] at hroot
  have hcls : classSize (uf.find x).1 r = classSize uf r := by
    simp only [classSize, UnionFind.find_size, UnionFind.find_root_1]
  rw [rank_find, hcls]
  exact h r hr hroot'

theorem rankBounded_union {uf : UnionFind} (h : RankBounded uf) (x y : Fin uf.size) :
    RankBounded (uf.union x y) := by
  intro r hr hroot
  rw [size_union] at hr
  have hr' : (uf.union x y).rootD r = r := UnionFind.rootD_eq_self.2 hroot
  have ha : uf.rootD x < uf.size := UnionFind.rootD_lt.2 x.2
  have hb : uf.rootD y < uf.size := UnionFind.rootD_lt.2 y.2
  have haroot : uf.parent (uf.rootD x) = uf.rootD x :=
    UnionFind.rootD_eq_self.1 UnionFind.rootD_rootD
  have hbroot : uf.parent (uf.rootD y) = uf.rootD y :=
    UnionFind.rootD_eq_self.1 UnionFind.rootD_rootD
  have hcls : classSize (uf.union x y) r =
      ((Finset.range uf.size).filter (fun i =>
        (if uf.rootD i = uf.rootD x ∨ uf.rootD i = uf.rootD y then
          (if uf.rank (uf.rootD y) < uf.rank (uf.rootD x) then uf.rootD x else uf.rootD y)
        else uf.rootD i) = r)).card := by
    simp only [classSize, size_union, rootD_union]
  rw [hcls, Batteries.UnionFind.rank_union]
  rw [rootD_union] at hr'
  set a := uf.rootD x with ha_def
  set b := uf.rootD y with hb_def
  have hca := h a ha haroot
  have hcb := h b hb hbroot
  set w := (if uf.rank b < uf.rank a then a else b) with hw_def
  have hw : w = a ∨ w = b := by
    by_cases hlt : uf.rank b < uf.rank a
    · exact Or.inl (ite_eq_left hlt)
    · exact Or.inr (ite_eq_right hlt)
  by_cases hab : uf.rootD r = a ∨ uf.rootD r = b
  · rw [ite_eq_left hab] at hr'
    subst hr'
    by_cases heq : a = b
    · have hwa : w = a := by rcases hw with hw | hw <;> [exact hw; exact hw.trans heq.symm]
      have hfil : (Finset.range uf.size).filter (fun i =>
          (if uf.rootD i = a ∨ uf.rootD i = b then w else uf.rootD i) = w) =
          (Finset.range uf.size).filter (fun i => uf.rootD i = a) := by
        apply Finset.filter_congr
        intro i _
        by_cases h1 : uf.rootD i = a ∨ uf.rootD i = b
        · rw [ite_eq_left h1, hwa]
          simp only [true_iff]
          rcases h1 with h1 | h1 <;> [exact h1; exact h1.trans heq.symm]
        · rw [ite_eq_right h1, hwa]
      rw [hfil, ite_eq_right (fun hc => hc.1 heq), hwa]
      exact hca
    · have hfil : (Finset.range uf.size).filter (fun i =>
          (if uf.rootD i = a ∨ uf.rootD i = b then w else uf.rootD i) = w) =
          (Finset.range uf.size).filter (fun i => uf.rootD i = a ∨ uf.rootD i = b) := by
        apply Finset.filter_congr
        intro i _
        by_cases h1 : uf.rootD i = a ∨ uf.rootD i = b
        · rw [ite_eq_left h1]
          simp only [true_iff]
          exact h1
        · rw [ite_eq_right h1]
          constructor
          · intro h2
            exact absurd (h2 ▸ hw) h1
          · intro h2
            exact absurd h2 h1
      rw [hfil, card_filter_or heq]
      change _ ≤ classSize uf a + classSize uf b
      by_cases hrk : uf.rank a = uf.rank b
      · have hwb : w = b := ite_eq_right (by omega)
        rw [ite_eq_left ⟨heq, hrk, hwb.symm⟩, pow_succ]
        rw [hrk] at hca
        omega
      · rw [ite_eq_right (fun hc => hrk hc.2.1)]
        rcases hw with hw | hw
        · rw [hw]; omega
        · rw [hw]; omega
  · rw [ite_eq_right hab] at hr'
    have hpar : uf.parent r = r := UnionFind.rootD_eq_self.1 hr'
    have hra : r ≠ a := fun h' => hab (Or.inl (hr'.trans h'))
    have hrb : r ≠ b := fun h' => hab (Or.inr (hr'.trans h'))
    have hfil : (Finset.range uf.size).filter (fun i =>
        (if uf.rootD i = a ∨ uf.rootD i = b then w else uf.rootD i) = r) =
        (Finset.range uf.size).filter (fun i => uf.rootD i = r) := by
      apply Finset.filter_congr
      intro i _
      by_cases h1 : uf.rootD i = a ∨ uf.rootD i = b
      · rw [ite_eq_left h1]
        constructor
        · intro h2
          rcases hw with hw | hw
          · exact absurd (h2.symm.trans hw) hra
          · exact absurd (h2.symm.trans hw) hrb
        · intro h2
          rcases h1 with h1 | h1
          · exact absurd (h2.symm.trans h1) hra
          · exact absurd (h2.symm.trans h1) hrb
      · rw [ite_eq_right h1]
    rw [hfil, ite_eq_right (fun hc => hrb hc.2.2.symm)]
    exact h r hr hpar

theorem rankBounded_of_reachable {uf : UnionFind} (h : Reachable uf) : RankBounded uf := by
  induction h with
  | empty => exact rankBounded_empty
  | push _ ih => exact rankBounded_push ih
  | find x _ ih => exact rankBounded_find ih x
  | union x y _ ih => exact rankBounded_union ih x y

/-- **Rank lemma for linking by rank (roots).** In every union-find structure built from the
empty one by make-set, find with path compression and union by rank, every root `r` has at
least `2 ^ rank r` nodes in its class (Tarjan and van Leeuwen, *Worst-case analysis of set union
algorithms*, J. ACM 31(2) (1984), §2, Lemma 2, "size(x) ≥ 2^rank(x)", here for the roots, whose
subtrees are their classes; path compression changes neither ranks nor classes). -/
theorem two_pow_rank_le_classSize {uf : UnionFind} (h : Reachable uf) {r : ℕ}
    (hr : r < uf.size) (hroot : uf.parent r = r) : 2 ^ uf.rank r ≤ classSize uf r :=
  rankBounded_of_reachable h r hr hroot

/-- **Ranks are at most `log₂ n`.** In every union-find structure with `n` nodes built from the
empty one by make-set, find with path compression and union by rank, every node has rank at most
`⌊log₂ n⌋` (Tarjan and van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
(1984), §2, consequence of Lemma 2; compare Corollary 1 with `i` above `log₂ n`). -/
theorem rank_le_log {uf : UnionFind} (h : Reachable uf) (i : ℕ) :
    uf.rank i ≤ Nat.log 2 uf.size := by
  by_cases hi : i < uf.size
  · have hr : uf.rootD i < uf.size := UnionFind.rootD_lt.2 hi
    have hroot : uf.parent (uf.rootD i) = uf.rootD i :=
      UnionFind.rootD_eq_self.1 UnionFind.rootD_rootD
    have hpow := (two_pow_rank_le_classSize h hr hroot).trans (classSize_le_size uf _)
    exact UnionFind.le_rank_root.trans (Nat.le_log_of_pow_le Nat.one_lt_two hpow)
  · rw [rank_of_not_lt hi]
    exact Nat.zero_le _

private theorem iterate_parent_root_or_le (uf : UnionFind) (i : ℕ) (k : ℕ) :
    uf.parent (uf.parent^[k] i) = uf.parent^[k] i ∨ k ≤ uf.rank (uf.parent^[k] i) := by
  induction k with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      by_cases hk : uf.parent (uf.parent^[k] i) = uf.parent^[k] i
      · left
        rw [hk, hk]
      · right
        have hlt := UnionFind.rank_lt hk
        rcases ih with ih | ih
        · exact absurd ih hk
        · omega

private theorem rootD_iterate_parent (uf : UnionFind) (i : ℕ) :
    ∀ k, uf.rootD (uf.parent^[k] i) = uf.rootD i
  | 0 => rfl
  | k + 1 => by
      rw [Function.iterate_succ_apply', UnionFind.rootD_parent, rootD_iterate_parent uf i k]

/-- **Find paths have at most `log₂ n` edges.** In every union-find structure with `n` nodes
built from the empty one by make-set, find with path compression and union by rank, following
`⌊log₂ n⌋` parent pointers from any node `i` reaches the root of `i` (Tarjan and van Leeuwen,
*Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984), §2, Corollary 2, "no path
has length exceeding log n", here for the compressed structure; ranks strictly increase along
parent pointers and are at most `log₂ n`). -/
theorem iterate_parent_log {uf : UnionFind} (h : Reachable uf) (i : ℕ) :
    uf.parent^[Nat.log 2 uf.size] i = uf.rootD i := by
  have hroot : uf.parent (uf.parent^[Nat.log 2 uf.size] i) =
      uf.parent^[Nat.log 2 uf.size] i := by
    rcases iterate_parent_root_or_le uf i (Nat.log 2 uf.size) with hk | hk
    · exact hk
    · by_contra hne
      have h1 := UnionFind.lt_rank_root.2 hne
      have h2 := rank_le_log h (uf.rootD (uf.parent^[Nat.log 2 uf.size] i))
      omega
  rw [← rootD_iterate_parent uf i (Nat.log 2 uf.size)]
  exact (UnionFind.rootD_eq_self.2 hroot).symm

end Cslib.Algorithms.Lean.UnionByRank
