/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Infix
public import Mathlib.Order.WithBot

/-!
# The Burrows–Wheeler transform, its inversion, and FM-index backward search

The Burrows–Wheeler transform (Burrows and Wheeler 1994) of a text `t` over a linearly ordered
alphabet appends a unique sentinel smaller than every letter (here `⊥ : WithBot α`, giving
`withSentinel t` of length `|t| + 1`), sorts the `|t| + 1` rotations of the result
lexicographically (the rows of the *Burrows–Wheeler matrix*, `sortedRotations t`), and outputs
the last column (`bwt t`). The transform is a permutation of `withSentinel t` that tends to group
equal letters, and it is invertible from the last column alone.

The *LF-mapping* sends row `r` to the row holding the rotation of row `r` rotated right by one
position (the rotation starting one position earlier in the text). It is computable from the
last column `L`: `lf L r = C[L[r]] + rank_{L[r]}(L, r)`, where `C[c]` (`countLess`) is the number
of letters smaller than `c` and `rank_c(L, r)` (`rank`) is the number of occurrences of `c` before
row `r`. Inversion (`invert`) starts at row `0`, whose rotation starts with the sentinel, and
walks the LF-mapping, reading the text backwards.

*Backward search* (Ferragina and Manzini 2000) counts the occurrences of a pattern `P` from the
last column alone. The rows whose rotation starts with a given word form an interval of rows,
because the rows are sorted; backward search maintains that interval `[sp, ep)` for longer and
longer suffixes of `P`, starting from all rows `[0, |t| + 1)` for the empty suffix and mapping
`[sp, ep)` to `[C[c] + rank_c(L, sp), C[c] + rank_c(L, ep))` when the letter `c` is prepended.

## Main results

* `sortedRotations_getD_lf`: **the LF-mapping property**.
* `invert_bwt`: **inversion returns the original text**: `invert (bwt t) = t.map (↑)`.
* `backwardSearch_spec`: **after processing `P`, `[sp, ep)` is exactly the set of rows whose
  rotation starts with `P`**.
* `backwardSearch_bounds`: `sp ≤ ep ≤ |L|` for every list `L` and pattern.
* `backwardSearch_count`: `ep - sp` **is the number of occurrences of `P` in `t`** (positions
  `i ≤ |t|` with `P` a prefix of `t.drop i`; the empty pattern occurs at all `|t| + 1` positions).

## Cost model

`sortedRotations` sorts with `List.mergeSort` and compares whole rotations, so the definition
makes no complexity claim (suffix-array construction is linear in principle). Given the last
column, `lf` evaluated directly scans `L` (`O(n)` per step, `O(n²)` for `invert`); with the
`C` table and rank directories precomputed, each LF step is `O(1)` and inversion is `O(n)`.
Backward search does two rank queries and two `C` lookups per letter of `P`; with the same
directories (the FM-index) counting takes `O(|P|)` time, independently of `|t|`.

## References

* M. Burrows and D. J. Wheeler, *A block-sorting lossless data compression algorithm*, Digital
  Systems Research Center Research Report 124, 1994.
* P. Ferragina and G. Manzini, *Opportunistic data structures with applications*, Proc. 41st
  IEEE Symposium on Foundations of Computer Science (FOCS 2000), 390–398.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Indexing.BWT

/-- The text `t` with the sentinel `⊥` appended: `t.map (↑) ++ [⊥]`. The sentinel is the unique
occurrence of `⊥` and is smaller than every letter. -/
def withSentinel {α : Type*} (t : List α) : List (WithBot α) := t.map (↑) ++ [⊥]

/-- The starting positions `0, …, |t|` of the rotations of `withSentinel t`, sorted by their
rotations in lexicographic order: row `r` of the Burrows–Wheeler matrix is
`(withSentinel t).rotate ((sortedRotations t)[r])`. -/
def sortedRotations {α : Type*} [LinearOrder α] (t : List α) : List ℕ :=
  (List.range (t.length + 1)).mergeSort
    (fun i j => decide ((withSentinel t).rotate i ≤ (withSentinel t).rotate j))

/-- The Burrows–Wheeler transform: the last column of the sorted rotation matrix. -/
def bwt {α : Type*} [LinearOrder α] (t : List α) : List (WithBot α) :=
  (sortedRotations t).map fun i => ((withSentinel t).rotate i).getLastD ⊥

/-- `C[c]`: the number of letters of `L` smaller than `c`. -/
def countLess {α : Type*} [LinearOrder α] (L : List (WithBot α)) (c : WithBot α) : ℕ :=
  L.countP (· < c)

/-- `rank_c(L, r)`: the number of occurrences of `c` among the first `r` letters of `L`. -/
def rank {α : Type*} [LinearOrder α] (L : List (WithBot α)) (c : WithBot α) (r : ℕ) : ℕ :=
  (L.take r).count c

/-- The LF-mapping computed from the last column alone: `LF(r) = C[L[r]] + rank_{L[r]}(L, r)`. -/
def lf {α : Type*} [LinearOrder α] (L : List (WithBot α)) (r : ℕ) : ℕ :=
  countLess L (L.getD r ⊥) + rank L (L.getD r ⊥) r

/-- `k` steps of the inversion walk from row `r`: the letters `L[r], L[LF r], …`. -/
def invertAux {α : Type*} [LinearOrder α] (L : List (WithBot α)) : ℕ → ℕ → List (WithBot α)
  | 0, _ => []
  | k + 1, r => L.getD r ⊥ :: invertAux L k (lf L r)

/-- Inversion of the Burrows–Wheeler transform: walk the LF-mapping `|L| - 1` times from row `0`
(the rotation that starts with the sentinel) and reverse the letters read. -/
def invert {α : Type*} [LinearOrder α] (L : List (WithBot α)) : List (WithBot α) :=
  (invertAux L (L.length - 1) 0).reverse

private theorem sortedRotations_perm {α : Type*} [LinearOrder α] (t : List α) :
    (sortedRotations t).Perm (List.range (t.length + 1)) :=
  List.mergeSort_perm _ _

private theorem sortedRotations_length {α : Type*} [LinearOrder α] (t : List α) :
    (sortedRotations t).length = t.length + 1 := by
  simpa using (sortedRotations_perm t).length_eq

private theorem bwt_length {α : Type*} [LinearOrder α] (t : List α) :
    (bwt t).length = t.length + 1 := by
  simp [bwt, sortedRotations_length]

private theorem sortedRotations_bound {α : Type*} [LinearOrder α] (t : List α)
    (r : ℕ) (hr : r < t.length + 1) :
    (sortedRotations t).getD r 0 < t.length + 1 := by
  have h : r < (sortedRotations t).length := by rwa [sortedRotations_length]
  apply List.mem_range.mp
  apply (sortedRotations_perm t).mem_iff.mp
  simp [List.getD, List.getElem?_eq_getElem h]

private theorem countLess_add_count_le {α : Type*} [LinearOrder α]
    (L : List (WithBot α)) (c : WithBot α) : countLess L c + L.count c ≤ L.length := by
  induction L with
  | nil => simp [countLess]
  | cons a L ih =>
    simp only [countLess, List.countP_cons, List.count_cons, List.length_cons] at *
    by_cases h : a < c
    · have hn : a ≠ c := ne_of_lt h
      simp [h, hn] at *
      omega
    · simp [h] at *
      split <;> omega

private theorem lf_bound {α : Type*} [LinearOrder α] (L : List (WithBot α))
    (r : ℕ) (hr : r < L.length) : lf L r < L.length := by
  have h := countLess_add_count_le L (L.getD r ⊥)
  have hc : (L.take r).count (L.getD r ⊥) < L.count (L.getD r ⊥) := by
    have he := List.take_append_drop r L
    have hd : 0 < (L.drop r).count (L.getD r ⊥) := by
      apply List.count_pos_iff.mpr
      simp only [List.getD, List.getElem?_eq_getElem hr, Option.getD_some]
      have hh : 0 < (L.drop r).length := by simp; omega
      simpa using (List.getElem_mem (n := 0) hh)
    have hh := congrArg (List.count (L.getD r ⊥)) he
    simp only [List.count_append] at hh
    omega
  unfold lf rank
  omega

private theorem prefix_before_sentinel {α : Type*} (P u : List α)
    (v : List (WithBot α)) :
    P.map (↑) <+: u.map (↑) ++ ⊥ :: v ↔ P <+: u := by
  induction u generalizing P with
  | nil =>
    cases P <;> simp
  | cons a u ih =>
    cases P with
    | nil => simp
    | cons c P => simpa using and_congr Iff.rfl (ih P)

private theorem prefix_rotation {α : Type*} (t P : List α) (i : ℕ)
    (hi : i ≤ t.length) :
    P.map (↑) <+: (withSentinel t).rotate i ↔ P <+: t.drop i := by
  rw [List.rotate_eq_drop_append_take (by simp [withSentinel]; omega)]
  unfold withSentinel
  have hm : i ≤ (t.map (WithBot.some)).length := by simpa using hi
  rw [List.drop_append_of_le_length hm, List.take_append_of_le_length hm]
  simp only [← List.map_drop, List.append_assoc, List.singleton_append]
  exact prefix_before_sentinel P (t.drop i) ((t.map (↑)).take i)

private theorem rotation_normal {α : Type*} (t : List α) (i : ℕ) (hi : i ≤ t.length) :
    (withSentinel t).rotate i = (t.drop i).map (↑) ++ ⊥ :: (t.take i).map (↑) := by
  rw [List.rotate_eq_drop_append_take (by simp [withSentinel]; omega)]
  unfold withSentinel
  have hm : i ≤ (t.map (WithBot.some)).length := by simpa using hi
  rw [List.drop_append_of_le_length hm, List.take_append_of_le_length hm]
  simp only [← List.map_drop, ← List.map_take, List.append_assoc, List.singleton_append]

private theorem sentinel_rotation_lt {α : Type*} [LinearOrder α] (t : List α)
    (i : ℕ) (hi : i < t.length) :
    (withSentinel t).rotate t.length < (withSentinel t).rotate i := by
  rw [rotation_normal t t.length (by omega), rotation_normal t i (by omega)]
  simp only [List.drop_length, List.map_nil, List.nil_append, List.take_length]
  have hn : t.drop i ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_drop, List.length_nil] at this
    omega
  obtain ⟨a, u, he⟩ := List.exists_cons_of_ne_nil hn
  rw [he]
  exact List.Lex.rel (WithBot.bot_lt_coe a)

private theorem sortedRotations_pairwise {α : Type*} [LinearOrder α] (t : List α) :
    (sortedRotations t).Pairwise
      (fun i j => (withSentinel t).rotate i ≤ (withSentinel t).rotate j) := by
  unfold sortedRotations
  have h := List.pairwise_mergeSort
    (le := fun i j => decide ((withSentinel t).rotate i ≤ (withSentinel t).rotate j))
    (fun i j k hij hjk => by
      simpa only [decide_eq_true_eq] using
        le_trans (of_decide_eq_true hij) (of_decide_eq_true hjk))
    (fun i j => by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using
        le_total ((withSentinel t).rotate i) ((withSentinel t).rotate j))
    (List.range (t.length + 1))
  simpa only [decide_eq_true_eq] using h

private theorem sortedRotations_zero {α : Type*} [LinearOrder α] (t : List α) :
    (sortedRotations t).getD 0 0 = t.length := by
  have hp := sortedRotations_pairwise t
  have hm : t.length ∈ sortedRotations t :=
    (sortedRotations_perm t).mem_iff.mpr (by simp)
  have hb : ∀ i ∈ sortedRotations t, i < t.length + 1 := by
    intro i hi
    exact List.mem_range.mp ((sortedRotations_perm t).mem_iff.mp hi)
  cases he : sortedRotations t with
  | nil => simp [he] at hm
  | cons a S =>
    simp only [he, List.pairwise_cons, List.mem_cons] at hp hm hb
    have ha : a = t.length := by
      rcases hm with h | h
      · exact h.symm
      · have hle := hp.1 t.length h
        by_contra hne
        have hai : a < t.length := by have := hb a (Or.inl rfl); omega
        exact (not_le_of_gt (sentinel_rotation_lt t a hai)) hle
    simp [ha, List.getD]

private theorem bwt_getD {α : Type*} [LinearOrder α] (t : List α) (r : ℕ)
    (hr : r < t.length + 1) :
    (bwt t).getD r ⊥ =
      ((withSentinel t).rotate ((sortedRotations t).getD r 0)).getLastD ⊥ := by
  have hs : r < (sortedRotations t).length := by rwa [sortedRotations_length]
  simp [bwt, List.getD, hs]

private theorem rotation_last_succ {α : Type*} (t : List α) (i : ℕ)
    (hi : i < t.length) :
    ((withSentinel t).rotate (i + 1)).getLastD ⊥ = (t[i] : WithBot α) := by
  rw [rotation_normal t (i + 1) (by omega), List.take_succ_eq_append_getElem hi]
  simp only [List.map_append, List.map_singleton]
  rw [← List.cons_append, ← List.append_assoc, List.getLastD_concat]

private theorem rotation_injective {α : Type*} [LinearOrder α] (t : List α)
    (i j : ℕ) (hi : i ≤ t.length) (hj : j ≤ t.length)
    (h : (withSentinel t).rotate i = (withSentinel t).rotate j) : i = j := by
  have hs : ∀ k ≤ t.length, ((withSentinel t).rotate k).idxOf ⊥ = t.length - k := by
    intro k hk
    rw [rotation_normal t k hk, List.idxOf_append_of_notMem (by
      intro hm
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
      exact WithBot.coe_ne_bot ha)]
    simp
  have he := congrArg (List.idxOf ⊥) h
  rw [hs i hi, hs j hj] at he
  omega

private theorem append_lt_append_same_length {α : Type*} [LinearOrder α]
    (u v : List α) (c : α) (huv : u.length = v.length) :
    u ++ [c] < v ++ [c] ↔ u < v := by
  induction u generalizing v with
  | nil => have : v = [] := List.length_eq_zero_iff.mp huv.symm; subst v; simp
  | cons a u ih =>
    cases v with
    | nil => simp at huv
    | cons b v =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at huv
      simp only [List.cons_append, List.cons_lt_cons_iff, ih v huv]

private theorem rotate_right {α : Type*} (u : List α) (d : α) (hu : u ≠ []) :
    u.rotate (u.length - 1) = u.getLastD d :: u.dropLast := by
  induction u using List.reverseRecOn with
  | nil => contradiction
  | append_singleton a u ih =>
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
      List.rotate_append_length_eq, List.singleton_append, List.getLastD_concat,
      List.dropLast_concat]

private theorem predecessor_rotation {α : Type*} (t : List α) (i : ℕ) :
    (withSentinel t).rotate ((i + t.length) % (t.length + 1)) =
      ((withSentinel t).rotate i).getLastD ⊥ :: ((withSentinel t).rotate i).dropLast := by
  have hn : (withSentinel t).rotate i ≠ [] := by simp [withSentinel]
  have hl : ((withSentinel t).rotate i).length = t.length + 1 := by simp [withSentinel]
  rw [← hl] at ⊢
  rw [List.length_rotate, List.rotate_mod, ← List.rotate_rotate]
  rw [← Nat.add_sub_cancel t.length 1, ← hl]
  exact rotate_right _ _ hn

private theorem predecessor_lt {α : Type*} [LinearOrder α] (t : List α) (i j : ℕ) :
    (withSentinel t).rotate ((j + t.length) % (t.length + 1)) <
        (withSentinel t).rotate ((i + t.length) % (t.length + 1)) ↔
      ((withSentinel t).rotate j).getLastD ⊥ < ((withSentinel t).rotate i).getLastD ⊥ ∨
        ((withSentinel t).rotate j).getLastD ⊥ =
          ((withSentinel t).rotate i).getLastD ⊥ ∧
            (withSentinel t).rotate j < (withSentinel t).rotate i := by
  rw [predecessor_rotation, predecessor_rotation, List.cons_lt_cons_iff]
  apply or_congr Iff.rfl
  apply and_congr_right
  intro he
  have hn : ∀ k, (withSentinel t).rotate k ≠ [] := by intro k; simp [withSentinel]
  have hh : ∀ k, (withSentinel t).rotate k =
      ((withSentinel t).rotate k).dropLast ++ [((withSentinel t).rotate k).getLastD ⊥] := by
    intro k
    have hne := hn k
    generalize (withSentinel t).rotate k = u at *
    induction u using List.reverseRecOn with
    | nil => contradiction
    | append_singleton a u ih => simp
  conv_rhs => rw [hh j, hh i, he]
  exact (append_lt_append_same_length _ _ _ (by simp [withSentinel])).symm

private theorem sortedRotations_strict {α : Type*} [LinearOrder α] (t : List α) :
    (sortedRotations t).Pairwise
      (fun i j => (withSentinel t).rotate i < (withSentinel t).rotate j) := by
  have hp := sortedRotations_pairwise t
  have hn := (sortedRotations_perm t).nodup_iff.mpr List.nodup_range
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hle := hp.rel_getElem_of_lt hi hj hij
  apply lt_of_le_of_ne hle
  intro he
  have hb : ∀ k ∈ sortedRotations t, k ≤ t.length := by
    intro k hk
    exact Nat.le_of_lt_succ (List.mem_range.mp ((sortedRotations_perm t).mem_iff.mp hk))
  have heq := rotation_injective t _ _ (hb _ (List.getElem_mem hi))
    (hb _ (List.getElem_mem hj)) he
  have heij := hn.getElem_inj_iff.mp heq
  omega

private theorem count_before {α β : Type*} [LinearOrder β] (L : List α) (d : α)
    (f : α → β) (p : α → Bool) (hL : L.Pairwise (fun a b => f a < f b))
    (r : ℕ) (hr : r < L.length) :
    L.countP (fun a => p a && decide (f a < f (L.getD r d))) = (L.take r).countP p := by
  induction L generalizing r with
  | nil => simp at hr
  | cons a L ih =>
    have hp := List.pairwise_cons.mp hL
    cases r with
    | zero =>
      simp only [List.getD, List.getElem?_cons_zero, Option.getD_some, List.take_zero,
        List.countP_nil]
      apply List.countP_eq_zero.mpr
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · simp
      · have := hp.1 b hb
        simp only [Bool.and_eq_true]
        exact fun h => (not_lt_of_gt this) (of_decide_eq_true h.2)
    | succ r =>
      have hr' : r < L.length := by simpa using hr
      have hm : L.getD r d ∈ L := by simp [List.getD, hr']
      have ha := hp.1 _ hm
      simp only [List.getD, List.getElem?_cons_succ, List.take_succ_cons]
      change (a :: L).countP (fun b => p b && decide (f b < f (L.getD r d))) =
        (a :: L.take r).countP p
      rw [List.countP_cons, List.countP_cons, ih hp.2 r hr']
      change f a < f (L[r]?.getD d) at ha
      simp [ha]

private theorem predecessor_perm (n : ℕ) :
    ((List.range (n + 1)).map (fun i => (i + n) % (n + 1))).Perm (List.range (n + 1)) := by
  have he : (List.range (n + 1)).map (fun i => (i + n) % (n + 1)) =
      (List.range (n + 1)).rotate n := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  rw [he]
  exact List.rotate_perm _ _

private theorem countP_or_disjoint {α : Type*} (L : List α) (p q : α → Bool)
    (hd : ∀ a ∈ L, ¬(p a ∧ q a)) :
    L.countP (fun a => p a || q a) = L.countP p + L.countP q := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := hd a (by simp)
    have ht : ∀ a ∈ L, ¬(p a ∧ q a) := fun b hb => hd b (by simp [hb])
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih ht]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

private theorem count_interval (n sp ep : ℕ) (hsp : sp ≤ ep) (hep : ep ≤ n) :
    (List.range n).countP (fun r => sp ≤ r ∧ r < ep) = ep - sp := by
  induction n generalizing ep sp with
  | zero =>
    have : ep = 0 := by omega
    subst ep
    simp
  | succ n ih =>
    by_cases he : ep ≤ n
    · rw [List.range_succ, List.countP_append, ih sp ep hsp he]
      simp only [List.countP_singleton]
      have hn : ¬(sp ≤ n ∧ n < ep) := by omega
      simp [hn]
    · have heq : ep = n + 1 := by omega
      subst ep
      by_cases hs : sp ≤ n
      · rw [List.range_succ, List.countP_append]
        have hc : (List.range n).countP (fun r => sp ≤ r ∧ r < n + 1) =
            (List.range n).countP (fun r => sp ≤ r ∧ r < n) := by
          apply List.countP_congr
          intro r hr
          have := List.mem_range.mp hr
          simp only [decide_eq_true_eq]
          omega
        rw [hc, ih sp n hs (by omega)]
        simp [hs]
        omega
      · have : sp = n + 1 := by omega
        subst sp
        rw [List.countP_eq_zero.mpr]
        · simp
        · intro r hr
          have := List.mem_range.mp hr
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          omega

private theorem map_range_getD {α : Type*} (L : List α) (d : α) :
    (List.range L.length).map (fun r => L.getD r d) = L := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [List.getD, List.getElem?_eq_getElem hi']

private theorem lf_count {α : Type*} [LinearOrder α] (t : List α) (r : ℕ)
    (hr : r < t.length + 1) :
    lf (bwt t) r = (sortedRotations t).countP (fun j =>
      (withSentinel t).rotate j < (withSentinel t).rotate
        (((sortedRotations t).getD r 0 + t.length) % (t.length + 1))) := by
  let S := sortedRotations t
  let rot := (withSentinel t).rotate
  let last := fun i => (rot i).getLastD ⊥
  let prev := fun i => (i + t.length) % (t.length + 1)
  let i := S.getD r 0
  let c := last i
  have hs : r < S.length := by simpa [S, sortedRotations_length] using hr
  have hp : (S.map prev).Perm S :=
    ((sortedRotations_perm t).map prev).trans
      ((predecessor_perm t.length).trans (sortedRotations_perm t).symm)
  have hc : (bwt t).getD r ⊥ = c := bwt_getD t r hr
  have he : S.countP (fun j => rot j < rot (prev i)) =
      S.countP (fun j => last j < c ∨ last j = c ∧ rot j < rot i) := by
    rw [← hp.countP_eq (fun j => rot j < rot (prev i)), List.countP_map]
    apply List.countP_congr
    intro j hj
    simpa only [decide_eq_true_eq, Function.comp_def] using predecessor_lt t i j
  have hd : S.countP (fun j => last j < c ∨ last j = c ∧ rot j < rot i) =
      S.countP (fun j => last j < c) +
        S.countP (fun j => decide (last j = c) && decide (rot j < rot i)) := by
    simpa only [Bool.decide_or, Bool.decide_and] using countP_or_disjoint S
      (fun j => decide (last j < c))
      (fun j => decide (last j = c) && decide (rot j < rot i)) (by
        intro j hj
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rintro ⟨h, he, _⟩
        exact (ne_of_lt h) he)
  have hl : S.countP (fun j => last j < c) = countLess (bwt t) c := by
    simp only [countLess, bwt, List.countP_map]
    rfl
  have hb : S.countP (fun j => decide (last j = c) && decide (rot j < rot i)) =
      rank (bwt t) c r := by
    have hb' : S.countP (fun j => decide (last j = c) && decide (rot j < rot i)) =
        (S.take r).countP (fun j => decide (last j = c)) := by
      convert count_before S 0 rot (fun j => decide (last j = c))
        (sortedRotations_strict t) r hs using 1
      apply List.countP_congr
      intro j hj
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rfl
    rw [hb']
    unfold rank bwt
    rw [← List.map_take, List.count_eq_countP, List.countP_map]
    apply List.countP_congr
    intro j hj
    simp only [Function.comp_def, beq_iff_eq, decide_eq_true_eq]
    rfl
  change lf (bwt t) r = S.countP (fun j => rot j < rot (prev i))
  rw [he, hd, hl, hb]
  unfold lf
  rw [hc]

/-- **The LF-mapping property**: for every row `r`, row `lf (bwt t) r` holds the rotation of
row `r` rotated right by one position, i.e. starting one position earlier in the text. -/
theorem sortedRotations_getD_lf {α : Type*} [LinearOrder α] (t : List α) (r : ℕ)
    (hr : r < t.length + 1) :
    lf (bwt t) r < t.length + 1 ∧
      (sortedRotations t).getD (lf (bwt t) r) 0 =
        ((sortedRotations t).getD r 0 + t.length) % (t.length + 1) := by
  constructor
  · simpa [bwt_length] using lf_bound (bwt t) r (by simpa [bwt_length] using hr)
  · let j := ((sortedRotations t).getD r 0 + t.length) % (t.length + 1)
    have hj : j < t.length + 1 := Nat.mod_lt _ (by omega)
    have hm : j ∈ sortedRotations t :=
      (sortedRotations_perm t).mem_iff.mpr (List.mem_range.mpr hj)
    obtain ⟨s, hs, hes⟩ := List.mem_iff_getElem.mp hm
    have he : (sortedRotations t).getD s 0 = j := by
      simpa only [List.getD, List.getElem?_eq_getElem hs, Option.getD_some] using hes
    have hk := count_before (sortedRotations t) 0 ((withSentinel t).rotate)
      (fun _ => true) (sortedRotations_strict t) s hs
    simp only [Bool.true_and, List.countP_true, List.length_take,
      Nat.min_eq_left hs.le, he] at hk
    have hlf : lf (bwt t) r = s := (lf_count t r hr).trans hk
    rw [hlf]
    exact he

private theorem invertAux_row {α : Type*} [LinearOrder α] (t : List α) (i : ℕ)
    (hi : i ≤ t.length) (r : ℕ) (hr : r < t.length + 1)
    (hri : (sortedRotations t).getD r 0 = i) :
    invertAux (bwt t) i r = ((t.take i).map (↑)).reverse := by
  induction i generalizing r with
  | zero => simp [invertAux]
  | succ i ih =>
    have hi' : i < t.length := by omega
    have hl := sortedRotations_getD_lf t r hr
    have hm : (i + 1 + t.length) % (t.length + 1) = i := by
      rw [show i + 1 + t.length = (t.length + 1) + i by omega]
      simp [Nat.mod_eq_of_lt (by omega : i < t.length + 1)]
    have hs : (sortedRotations t).getD (lf (bwt t) r) 0 = i := by
      rw [hl.2, hri, hm]
    rw [invertAux, bwt_getD t r hr, hri, rotation_last_succ t i hi',
      ih (by omega) _ hl.1 hs, List.take_succ_eq_append_getElem hi']
    simp only [List.map_append, List.map_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append]

/-- **Inversion**: the Burrows–Wheeler transform is inverted by the LF-mapping walk. -/
theorem invert_bwt {α : Type*} [LinearOrder α] (t : List α) : invert (bwt t) = t.map (↑) := by
  unfold invert
  rw [bwt_length, Nat.add_sub_cancel, invertAux_row t t.length (by omega) 0
    (by omega) (sortedRotations_zero t)]
  simp

/-- FM-index backward search: the half-open row interval `[sp, ep)` for a pattern, computed from
the last column alone, processing the pattern from its last letter to its first. -/
def backwardSearch {α : Type*} [LinearOrder α] (L : List (WithBot α)) : List α → ℕ × ℕ
  | [] => (0, L.length)
  | c :: P =>
      (countLess L c + rank L c (backwardSearch L P).1,
        countLess L c + rank L c (backwardSearch L P).2)

private theorem sortedRotations_getD_injective {α : Type*} [LinearOrder α]
    (t : List α) (r s : ℕ) (hr : r < t.length + 1) (hs : s < t.length + 1)
    (h : (sortedRotations t).getD r 0 = (sortedRotations t).getD s 0) : r = s := by
  have hr' : r < (sortedRotations t).length := by rwa [sortedRotations_length]
  have hs' : s < (sortedRotations t).length := by rwa [sortedRotations_length]
  have hn := (sortedRotations_perm t).nodup_iff.mpr List.nodup_range
  simp only [List.getD, List.getElem?_eq_getElem hr', List.getElem?_eq_getElem hs',
    Option.getD_some] at h
  exact hn.getElem_inj_iff.mp h

private theorem lf_surjective {α : Type*} [LinearOrder α] (t : List α) (s : ℕ)
    (hs : s < t.length + 1) : ∃ r < t.length + 1, lf (bwt t) r = s := by
  let i := (sortedRotations t).getD s 0
  let j := (i + 1) % (t.length + 1)
  have hi : i < t.length + 1 := sortedRotations_bound t s hs
  have hj : j < t.length + 1 := Nat.mod_lt _ (by omega)
  have hm : j ∈ sortedRotations t :=
    (sortedRotations_perm t).mem_iff.mpr (List.mem_range.mpr hj)
  obtain ⟨r, hr, he⟩ := List.mem_iff_getElem.mp hm
  have hr' : r < t.length + 1 := by rwa [sortedRotations_length] at hr
  have he' : (sortedRotations t).getD r 0 = j := by
    simpa only [List.getD, List.getElem?_eq_getElem hr, Option.getD_some] using he
  have hl := sortedRotations_getD_lf t r hr'
  have hp : (j + t.length) % (t.length + 1) = i := by
    dsimp only [j]
    rw [Nat.mod_add_mod, show i + 1 + t.length = (t.length + 1) + i by omega]
    simp [Nat.mod_eq_of_lt hi]
  refine ⟨r, hr', sortedRotations_getD_injective t _ _ hl.1 hs ?_⟩
  rw [hl.2, he', hp]

private theorem rank_mono {α : Type*} [LinearOrder α] (L : List (WithBot α))
    (c : WithBot α) (r s : ℕ) (hrs : r ≤ s) : rank L c r ≤ rank L c s := by
  exact (List.take_prefix_take_left (l := L) hrs).count_le c

private theorem rank_strict {α : Type*} [LinearOrder α] (L : List (WithBot α))
    (c : WithBot α) (r s : ℕ) (hr : r < L.length) (hrs : r < s)
    (hc : L.getD r ⊥ = c) : rank L c r < rank L c s := by
  have hm := rank_mono L c (r + 1) s (by omega)
  have he : rank L c (r + 1) = rank L c r + 1 := by
    unfold rank
    rw [List.take_succ_eq_append_getElem hr, List.count_append]
    have hh : L[r] = c := by rwa [List.getElem_eq_getD ⊥]
    simp [hh]
  omega

private theorem countLess_mono_block {α : Type*} [LinearOrder α]
    (L : List (WithBot α)) (a b : WithBot α) (hab : a < b) :
    countLess L a + L.count a ≤ countLess L b := by
  induction L with
  | nil => simp [countLess]
  | cons c L ih =>
    simp only [countLess, List.countP_cons, List.count_cons] at *
    by_cases hca : c < a
    · have hcb : c < b := lt_trans hca hab
      have hne : c ≠ a := ne_of_lt hca
      simp [hca, hcb, hne] at *
      omega
    · by_cases he : c = a
      · subst c
        simp [hab] at *
        omega
      · simp [hca, he] at *
        split <;> omega

private theorem lf_interval {α : Type*} [LinearOrder α] (L : List (WithBot α))
    (r : ℕ) (hr : r < L.length) (c : WithBot α) (sp ep : ℕ) :
    countLess L c + rank L c sp ≤ lf L r ∧ lf L r < countLess L c + rank L c ep ↔
      L.getD r ⊥ = c ∧ sp ≤ r ∧ r < ep := by
  have hrank : ∀ a s, rank L a s ≤ L.count a := by
    intro a s
    exact (List.take_prefix s L).count_le a
  have hchar : countLess L c + rank L c sp ≤ lf L r ∧
      lf L r < countLess L c + rank L c ep → L.getD r ⊥ = c := by
    intro h
    rcases lt_trichotomy (L.getD r ⊥) c with hd | he | hd
    · have hb := countLess_mono_block L _ _ hd
      have hs := rank_strict L (L.getD r ⊥) r L.length hr hr rfl
      have hl := hrank (L.getD r ⊥) L.length
      unfold lf at h
      omega
    · exact he
    · have hb := countLess_mono_block L _ _ hd
      have he := hrank c ep
      unfold lf at h
      omega
  constructor
  · intro h
    have hc := hchar h
    refine ⟨hc, ?_, ?_⟩
    · by_contra hn
      have hh := rank_strict L c r sp hr (by omega) hc
      unfold lf at h
      rw [hc] at h
      omega
    · by_contra hn
      have hh := rank_mono L c ep r (by omega)
      unfold lf at h
      rw [hc] at h
      omega
  · rintro ⟨hc, hs, he⟩
    have hsp := rank_mono L c sp r hs
    have hep := rank_strict L c r ep hr he hc
    unfold lf
    rw [hc]
    omega

private theorem prefix_dropLast_rotation {α : Type*} (t P : List α) (i : ℕ) :
    P.map (↑) <+: ((withSentinel t).rotate i).dropLast ↔
      P.map (↑) <+: (withSentinel t).rotate i := by
  constructor
  · intro h
    exact h.trans (List.dropLast_prefix _)
  · intro h
    have hb : (⊥ : WithBot α) ∈ (withSentinel t).rotate i := by simp [withSentinel]
    have hl : (P.map (WithBot.some)).length < ((withSentinel t).rotate i).length := by
      have hle := h.length_le
      by_contra hn
      have he := h.eq_of_length (by omega)
      rw [← he] at hb
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hb
      exact WithBot.coe_ne_bot ha
    apply List.prefix_of_prefix_length_le h (List.dropLast_prefix _)
    simp only [List.length_dropLast]
    omega

/-- Backward search always returns a genuine interval of rows, `sp ≤ ep ≤ |L|`, on any list `L`
(so the difference in `backwardSearch_count` involves no truncated subtraction). -/
theorem backwardSearch_bounds {α : Type*} [LinearOrder α]
    (L : List (WithBot α)) (P : List α) :
    (backwardSearch L P).1 ≤ (backwardSearch L P).2 ∧
      (backwardSearch L P).2 ≤ L.length := by
  induction P with
  | nil => simp [backwardSearch]
  | cons c P ih =>
    constructor
    · exact Nat.add_le_add_left (rank_mono L c _ _ ih.1) _
    · have h := countLess_add_count_le L c
      have hr := (List.take_prefix (backwardSearch L P).2 L).count_le (c : WithBot α)
      change countLess L c + rank L c (backwardSearch L P).2 ≤ L.length
      unfold rank
      omega

/-- **Backward search is correct**: after processing `P`, the interval `[sp, ep)` is exactly the
set of rows whose rotation starts with `P`. -/
theorem backwardSearch_spec {α : Type*} [LinearOrder α] (t P : List α) (r : ℕ)
    (hr : r < t.length + 1) :
    (backwardSearch (bwt t) P).1 ≤ r ∧ r < (backwardSearch (bwt t) P).2 ↔
      P.map (↑) <+: (withSentinel t).rotate ((sortedRotations t).getD r 0) := by
  induction P generalizing r with
  | nil => simp [backwardSearch, bwt_length, hr]
  | cons c P ih =>
    obtain ⟨q, hq, hlf⟩ := lf_surjective t r hr
    have hl := sortedRotations_getD_lf t q hq
    have he : (withSentinel t).rotate ((sortedRotations t).getD r 0) =
        (bwt t).getD q ⊥ ::
          ((withSentinel t).rotate ((sortedRotations t).getD q 0)).dropLast := by
      have hs : (sortedRotations t).getD r 0 =
          ((sortedRotations t).getD q 0 + t.length) % (t.length + 1) := by
        simpa only [hlf] using hl.2
      rw [hs, predecessor_rotation, bwt_getD t q hq]
    simp only [backwardSearch, List.map_cons]
    rw [he, List.cons_prefix_cons, ← hlf,
      lf_interval (bwt t) q (by simpa [bwt_length] using hq)]
    rw [prefix_dropLast_rotation, ← ih q hq]
    simp only [eq_comm]

/-- **Counting occurrences**: `ep - sp` is the number of positions `i ≤ |t|` at which `P`
occurs in `t`. -/
theorem backwardSearch_count {α : Type*} [LinearOrder α] (t P : List α) :
    (backwardSearch (bwt t) P).2 - (backwardSearch (bwt t) P).1 =
      (List.range (t.length + 1)).countP (fun i => P <+: t.drop i) := by
  classical
  let sp := (backwardSearch (bwt t) P).1
  let ep := (backwardSearch (bwt t) P).2
  have hb := backwardSearch_bounds (bwt t) P
  have hi := count_interval (t.length + 1) sp ep hb.1 (by simpa [bwt_length] using hb.2)
  have hc : (List.range (t.length + 1)).countP (fun r => sp ≤ r ∧ r < ep) =
      (List.range (t.length + 1)).countP
        (fun r => P <+: t.drop ((sortedRotations t).getD r 0)) := by
    apply List.countP_congr
    intro r hr
    simp only [decide_eq_true_eq]
    have hr' := List.mem_range.mp hr
    exact (backwardSearch_spec t P r hr').trans
      (prefix_rotation t P _ (Nat.le_of_lt_succ (sortedRotations_bound t r hr')))
  have hm := map_range_getD (sortedRotations t) 0
  rw [sortedRotations_length] at hm
  have hp := (sortedRotations_perm t).countP_eq (fun i => P <+: t.drop i)
  have he : (List.range (t.length + 1)).countP
      (fun r => P <+: t.drop ((sortedRotations t).getD r 0)) =
      (List.range (t.length + 1)).countP (fun i => P <+: t.drop i) := by
    simpa only [List.countP_map, Function.comp_def] using
      (congrArg (List.countP (fun i => P <+: t.drop i)) hm).trans hp
  exact hi.symm.trans (hc.trans he)

end Cslib.Bioinformatics.Indexing.BWT

