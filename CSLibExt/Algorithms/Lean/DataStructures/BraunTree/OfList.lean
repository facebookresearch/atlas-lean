/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Splice
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Array
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Order.MinMax
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Converting a list into a Braun tree (linear time)

`take_nths` (every-nth-sublists, (11.7)–(11.14)), `braun_list`
(Lemma 11.4 and its converse), `nodes` ((11.15)), `nth_nodes`
((11.16)), `brauns` ((11.17), the book's level-by-level recursion
through `nodes`) with Theorem 11.5 and Corollary 11.6 (`brauns1`),
and the running time of `brauns` (Lemma 11.7 via `Tbrauns_le`).

## Cost model

`Ttake` / `Tdrop` are `min n |xs| + 1`: one unit per element
traversed, plus one for the call. `Tnodes` is `|xs| + 1` (11.18).
`Tbrauns` is the book's recurrence with a trailing `+ 1` for the
dispatch itself. The counters measure calls of these functions,
not allocation, traversal, or total runtime.

## Deviations

All `min … (2 ^ k)` bounds are written with explicit parentheses:
`min xs.length 2 ^ k` would parse as `(min xs.length 2) ^ k`.

## Provenance

A Lean formalisation of the Chapter 11 Isabelle development in the
Isabelle distribution's `HOL-Data_Structures` theory
(`Braun_Tree.thy`). The book is Tobias Nipkow (ed.), *Functional
Data Structures and Algorithms* (ACM Books, 2025; text version of
July 27, 2026), Chapter 11, §11.5.3 and §11.5.3.2.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace BraunTree

variable {α : Type u}

/-- `take_nths i k xs`: the elements of `xs` at positions `i`, `i + 2^k`,
`i + 2 * 2^k`, … (book §11.5.3). -/
def take_nths : ℕ → ℕ → List α → List α
  | _, _, [] => []
  | 0, k, x :: xs => x :: take_nths (2 ^ k - 1) k xs
  | (i + 1), k, _ :: xs => take_nths i k xs

/-- Taking from a cons with index 0. -/
theorem take_nths_0_cons (x : α) (xs : List α) (k : ℕ) :
    take_nths 0 k (x :: xs) = x :: take_nths (2 ^ k - 1) k xs := rfl

/-- Taking from a cons with a successor index. -/
theorem take_nths_succ_cons (i : ℕ) (x : α) (xs : List α) (k : ℕ) :
    take_nths (i + 1) k (x :: xs) = take_nths i k xs := rfl

/-- Taking the evens from a two-element cons. -/
theorem take_nths_0_cons_cons (x y : α) (xs : List α) :
    take_nths 0 1 (x :: y :: xs) = x :: take_nths 0 1 xs := rfl

/-- Taking the odds from a two-element cons. -/
theorem take_nths_1_cons_cons (x y : α) (xs : List α) :
    take_nths 1 1 (x :: y :: xs) = y :: take_nths 1 1 xs := rfl

/-- Taking the odds from a cons. -/
theorem take_nths_1_cons (x : α) (xs : List α) :
    take_nths 1 1 (x :: xs) = take_nths 0 1 xs := rfl

/-- Taking from a cons with index 2. -/
theorem take_nths_2_cons (x : α) (xs : List α) :
    take_nths 2 1 (x :: xs) = take_nths 1 1 xs := rfl

/-- (11.7) `take_nths_drop`. -/
theorem take_nths_drop (i k : ℕ) : ∀ (j : ℕ) (xs : List α),
    take_nths i k (xs.drop j) = take_nths (i + j) k xs := by
  intro j
  induction j with
  | zero => intro xs; simp
  | succ j ih =>
    intro xs
    cases xs with
    | nil => simp [take_nths]
    | cons x xs =>
      have e1 : (x :: xs).drop (j + 1) = xs.drop j := rfl
      have e2 : i + (j + 1) = (i + j) + 1 := by omega
      rw [e1, e2, take_nths_succ_cons, ih xs]

/-- (11.8) `take_nths_00`. -/
theorem take_nths_00 (xs : List α) : take_nths 0 0 xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show x :: take_nths (2 ^ 0 - 1) 0 xs = x :: xs
    rw [show (2 : ℕ) ^ 0 - 1 = 0 from by norm_num, ih]

/-- (11.9) `take_nths_01_splice`. -/
theorem take_nths_01_splice (xs : List α) :
    splice (take_nths 0 1 xs) (take_nths 1 1 xs) = xs := by
  have key : ∀ (n : ℕ) (xs : List α), xs.length = n →
      splice (take_nths 0 1 xs) (take_nths 1 1 xs) = xs := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro xs hlen
      cases xs with
      | nil => simp [take_nths, splice]
      | cons x xs' =>
        cases xs' with
        | nil => simp [take_nths, splice]
        | cons y xs'' =>
          have h := ih xs''.length (by simp only [List.length_cons] at hlen; omega) xs'' rfl
          rw [take_nths_0_cons_cons, take_nths_1_cons_cons]
          simp only [splice]
          rw [h]
  exact key _ xs rfl

/-- `take_nths` of a non-empty block is non-empty. -/
theorem take_nths_ne_nil {i k : ℕ} {xs : List α} (h : i < xs.length) :
    take_nths i k xs ≠ [] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [take_nths]
    | succ j =>
      have hj : j < xs.length := by
        have hlen : (x :: xs).length = xs.length + 1 := rfl; omega
      have h' := ih (i := j) hj
      rw [take_nths_succ_cons]
      exact h'

/-- `take_nths` past the end of the list is empty. -/
theorem take_nths_eq_nil {i k : ℕ} {xs : List α} (h : xs.length ≤ i) :
    take_nths i k xs = [] := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => simp at h
    | succ j =>
      have hj : xs.length ≤ j := by
        have hlen : (x :: xs).length = xs.length + 1 := rfl; omega
      rw [take_nths_succ_cons]
      exact ih (i := j) hj

/-- (11.11) `take_nths_empty`. -/
theorem take_nths_empty (i k : ℕ) (xs : List α) :
    take_nths i k xs = [] ↔ xs.length ≤ i := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact take_nths_ne_nil hcon h
  · intro h
    exact take_nths_eq_nil h

/-- (11.14) `length_take_nths_00`: the two halves differ by at most one. -/
theorem length_take_nths (xs : List α) :
    (take_nths 0 1 xs).length = (take_nths 1 1 xs).length ∨
    (take_nths 0 1 xs).length = (take_nths 1 1 xs).length + 1 := by
  have key : ∀ (n : ℕ) (xs : List α), xs.length = n →
      (take_nths 0 1 xs).length = (take_nths 1 1 xs).length ∨
      (take_nths 0 1 xs).length = (take_nths 1 1 xs).length + 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro xs hlen
      cases xs with
      | nil => left; rfl
      | cons x xs' =>
        cases xs' with
        | nil =>
          right
          show (take_nths 0 1 [x]).length = (take_nths 1 1 [x]).length + 1
          simp [take_nths]
        | cons y xs'' =>
          have h := ih xs''.length (by simp only [List.length_cons] at hlen; omega) xs'' rfl
          rw [take_nths_0_cons_cons, take_nths_1_cons_cons]
          simp only [List.length_cons]
          omega
  exact key _ xs rfl

/-- (11.10) `take_nths_take_nths`. -/
theorem take_nths_take_nths (i m j n : ℕ) (xs : List α) :
    take_nths i m (take_nths j n xs) = take_nths (i * 2 ^ n + j) (m + n) xs := by
  have hp : (2 : ℕ) ^ m * 2 ^ n = 2 ^ (m + n) := (pow_add 2 m n).symm
  have hm : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hn : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hge : 2 ^ n ≤ 2 ^ (m + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hge2 : 2 ^ m ≤ 2 ^ (m + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  induction xs generalizing i j with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero =>
        rw [show 0 * 2 ^ n + 0 = 0 from by omega]
        show x :: take_nths (2 ^ m - 1) m (take_nths (2 ^ n - 1) n xs)
          = x :: take_nths (2 ^ (m + n) - 1) (m + n) xs
        rw [ih (2 ^ m - 1) (2 ^ n - 1)]
        congr 1
        have h1 : (2 ^ m - 1) * 2 ^ n = 2 ^ m * 2 ^ n - 2 ^ n := by
          rw [Nat.sub_mul, one_mul]
        congr 1
        omega
      | succ j' =>
        show take_nths 0 m (take_nths j' n xs)
          = take_nths ((0 * 2 ^ n + (j' + 1)) - 1) (m + n) xs
        rw [show 0 * 2 ^ n + (j' + 1) - 1 = j' from by omega]
        have h0 := ih 0 j'
        -- h0 : take_nths 0 m (take_nths j' n xs) = take_nths (0 * 2 ^ n + j') (m + n) xs
        rw [h0]
        congr 1
        omega
    | succ i' =>
      cases j with
      | zero =>
        have hA : 0 < (i' + 1) * 2 ^ n := Nat.mul_pos (by omega) hn
        rw [show (i' + 1) * 2 ^ n + 0 = ((i' + 1) * 2 ^ n - 1) + 1 from by omega]
        show take_nths i' m (take_nths (2 ^ n - 1) n xs)
          = take_nths (((i' + 1) * 2 ^ n) - 1) (m + n) xs
        rw [ih i' (2 ^ n - 1)]
        congr 1
        have h2 : (i' + 1) * 2 ^ n = i' * 2 ^ n + 2 ^ n := by ring
        omega
      | succ j' =>
        show take_nths (i' + 1) m (take_nths j' n xs)
          = take_nths ((i' + 1) * 2 ^ n + (j' + 1) - 1) (m + n) xs
        rw [show (i' + 1) * 2 ^ n + (j' + 1) - 1 = (i' + 1) * 2 ^ n + j' from by omega]
        exact ih (i' + 1) j'

/-- (11.13) `take_nths_01_splice`: `take_nths` inverts `splice`
(for the length condition of Braun siblings). -/
theorem take_nths_01_splice' {xs ys : List α}
    (h : xs.length = ys.length ∨ xs.length = ys.length + 1) :
    take_nths 0 1 (splice xs ys) = xs ∧ take_nths 1 1 (splice xs ys) = ys := by
  refine splice_ind (P := fun xs ys =>
    (xs.length = ys.length ∨ xs.length = ys.length + 1) →
    take_nths 0 1 (splice xs ys) = xs ∧ take_nths 1 1 (splice xs ys) = ys) ?_ ?_ xs ys h
  · intro ys h
    have hy : ys = [] := by
      have hnil : ([ ] : List α).length = 0 := rfl
      rcases h with h | h
      · exact List.eq_nil_of_length_eq_zero (by omega)
      · omega
    subst hy; simp [splice, take_nths]
  · intro a xs ys ih h
    have h' : ys.length = xs.length ∨ ys.length = xs.length + 1 := by
      have hlen : (a :: xs).length = xs.length + 1 := rfl; omega
    obtain ⟨h1, h2⟩ := ih h'
    constructor
    · simp only [splice]
      rw [take_nths_0_cons]
      rw [show (2 : ℕ) ^ 1 - 1 = 1 from by norm_num, h2]
    · simp only [splice]
      rw [take_nths_1_cons, h1]

/-- `braun_list t xs`: `t` is the Braun tree with list `xs`
(book §11.5.3). -/
def braun_list : Tree α → List α → Prop
  | .Leaf, xs => xs = []
  | .Node l x r, xs =>
      xs ≠ [] ∧ xs.head? = some x ∧ braun_list l (take_nths 1 1 xs)
        ∧ braun_list r (take_nths 2 1 xs)

/-- The `braun_list` relation at a leaf. -/
theorem braun_list_leaf {xs : List α} : braun_list (Tree.Leaf : Tree α) xs ↔ xs = [] :=
  Iff.rfl

/-- **Lemma 11.4.** `braun_list t xs ⟹ braun t ∧ xs = list t`
(`braun_list_eq` in `Array_Braun.thy`). -/
theorem braun_list_eq {t : Tree α} {xs : List α} (h : braun_list t xs) :
    braun t ∧ xs = list t := by
  induction t generalizing xs with
  | Leaf =>
    refine ⟨braun_leaf, ?_⟩
    have h' : xs = [] := h
    exact h'.trans rfl
  | Node l a r ihl ihr =>
    obtain ⟨hne, hhead, hbl, hbr⟩ := h
    obtain ⟨hb1, hl1⟩ := ihl hbl
    obtain ⟨hb2, hl2⟩ := ihr hbr
    have hxs : xs = a :: xs.tail := by
      cases xs with
      | nil => exact absurd rfl hne
      | cons y ys =>
        have : y = a := by
          have := hhead
          simp only [List.head?_cons] at this
          exact Option.some.inj this
        subst this; rfl
    have htake1 : take_nths 1 1 xs = take_nths 0 1 xs.tail := by
      conv_lhs => rw [hxs, take_nths_1_cons]
    have htake2 : take_nths 2 1 xs = take_nths 1 1 xs.tail := by
      conv_lhs => rw [hxs, take_nths_2_cons]
    have hlen : (take_nths 0 1 xs.tail).length = (take_nths 1 1 xs.tail).length ∨
        (take_nths 0 1 xs.tail).length = (take_nths 1 1 xs.tail).length + 1 :=
      length_take_nths xs.tail
    refine ⟨?_, ?_⟩
    · exact braun_node.mpr ⟨by
        rw [← list_length, ← list_length, ← hl1, ← hl2, htake1, htake2]
        exact hlen, hb1, hb2⟩
    · show xs = a :: splice (list l) (list r)
      rw [hxs, ← hl1, ← hl2, htake1, htake2, take_nths_01_splice]

/-- Converse of Lemma 11.4: a Braun tree with list `xs` satisfies
`braun_list`. -/
theorem braun_list_of_braun {t : Tree α} (h : braun t) {ys : List α}
    (hys : list t = ys) : braun_list t ys := by
  induction t generalizing ys with
  | Leaf =>
    simp [braun_list]
    rw [← hys]; rfl
  | Node l a r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    have hcond : (list l).length = (list r).length ∨ (list l).length = (list r).length + 1 := by
      rw [list_length, list_length]; exact hsz
    obtain ⟨h1, h2⟩ := take_nths_01_splice' hcond
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hys'; rw [← hys] at hys'; simp [list] at hys'
    · have e : ys = a :: splice (list l) (list r) := by rw [← hys]; rfl
      rw [e]; simp [List.head?_cons]
    · apply ihl hbl
      -- list l = take_nths 1 1 ys
      have e : ys = a :: splice (list l) (list r) := by rw [← hys]; rfl
      rw [e, take_nths_1_cons]
      exact h1.symm
    · apply ihr hbr
      have e : ys = a :: splice (list l) (list r) := by rw [← hys]; rfl
      rw [e, take_nths_2_cons]
      exact h2.symm

/-- `nodes ls xs rs`: the list of trees obtained by zipping `ls`, `xs`,
`rs` (book §11.5.3). -/
def nodes : List (Tree α) → List α → List (Tree α) → List (Tree α)
  | _, [], _ => []
  | ls, x :: xs, rs =>
      .Node (ls.head?.getD .Leaf) x (rs.head?.getD .Leaf) :: nodes ls.tail xs rs.tail

/-- (11.15) `length_nodes`. -/
theorem length_nodes (ls : List (Tree α)) (xs : List α) (rs : List (Tree α)) :
    (nodes ls xs rs).length = xs.length := by
  induction xs generalizing ls rs with
  | nil => rfl
  | cons x xs ih =>
    show (nodes ls.tail xs rs.tail).length + 1 = xs.length + 1
    rw [ih]

/-- `nthOrLeaf ts i`: the `i`-th tree of `ts`, or `Leaf` if out of range. -/
def nthOrLeaf (ts : List (Tree α)) (i : ℕ) : Tree α := (ts[i]?).getD .Leaf

/-- (11.16) `nth_nodes`. The book/Isabelle statement uses `xs ! i` (total `nth`,
no `Inhabited` needed); the Lean statement is therefore given with `getElem?`
and `Option.map` instead of `getElem!`, so it needs neither `[Inhabited α]`
nor the `i < |xs|` hypothesis (both sides are `none` when `i ≥ |xs|`). -/
theorem nth_nodes (ls : List (Tree α)) (xs : List α) (rs : List (Tree α)) (i : ℕ) :
    (nodes ls xs rs)[i]?
      = (xs[i]?).map (fun x => Tree.Node (nthOrLeaf ls i) x (nthOrLeaf rs i)) := by
  induction xs generalizing ls rs i with
  | nil => simp [nodes]
  | cons x xs ih =>
    cases i with
    | zero =>
      have hls : ls.head? = ls[0]? := by cases ls <;> rfl
      have hrs : rs.head? = rs[0]? := by cases rs <;> rfl
      simp [nodes, nthOrLeaf, hls, hrs]
    | succ j =>
      have hA : nthOrLeaf ls.tail j = nthOrLeaf ls (j + 1) := by
        show ((ls.tail)[j]?).getD .Leaf = ((ls[j + 1]?).getD .Leaf)
        cases ls with
        | nil => rfl
        | cons y ls' => simp [List.getElem?_cons_succ]
      have hB : nthOrLeaf rs.tail j = nthOrLeaf rs (j + 1) := by
        show ((rs.tail)[j]?).getD .Leaf = ((rs[j + 1]?).getD .Leaf)
        cases rs with
        | nil => rfl
        | cons y rs' => simp [List.getElem?_cons_succ]
      have h1 : (nodes ls (x :: xs) rs)[j + 1]? = (nodes ls.tail xs rs.tail)[j]? := by
        simp [nodes, List.getElem?_cons_succ]
      rw [h1, ih, List.getElem?_cons_succ, hA, hB]

/-- `brauns k xs`: the Braun trees on level `k` (book §11.5.3). Chops off
a chunk `ys` of size `2^k` from the input list, recursively converts the
remainder `zs` into the list `ts` of trees on level `k+1`, and combines
them with `ys` via `nodes` (the first `2^k` trees of `ts` become left
children, the rest right children). The recursive result `ts` is bound
once with `let` and reused, so each level makes a single recursive call
(the cost model `Tbrauns` counts one recursive call per level). -/
def brauns : ℕ → List α → List (Tree α)
  | _, [] => []
  | k, x :: xs' =>
      let ts := brauns (k + 1) ((x :: xs').drop (2 ^ k))
      nodes ts ((x :: xs').take (2 ^ k)) (ts.drop (2 ^ k))
termination_by _k xs => xs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  omega

/-- (11.17) `length_brauns`. -/
theorem brauns_length (k : ℕ) (xs : List α) :
    (brauns k xs).length = min xs.length (2 ^ k) := by
  have key : ∀ (n : ℕ) {k : ℕ} {xs : List α}, xs.length = n →
      (brauns k xs).length = min xs.length (2 ^ k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k xs hxs
      cases xs with
      | nil =>
        simp only [brauns, List.length_nil, Nat.min_eq_left (Nat.zero_le _)]
      | cons x xs' =>
        have hdrop : ((x :: xs').drop (2 ^ k)).length < n := by
          rw [← hxs, List.length_drop]
          have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
          simp only [List.length_cons]
          omega
        have h1 := ih _ hdrop (k := k + 1) (xs := (x :: xs').drop (2 ^ k)) rfl
        simp only [brauns, length_nodes, List.length_take]
        rcases le_total (2 ^ k) (x :: xs').length with hle | hle
        · rw [Nat.min_eq_left hle, Nat.min_eq_right hle]
        · rw [Nat.min_eq_right hle, Nat.min_eq_left hle]
  exact key xs.length rfl

/-- (11.12) `hd_take_nths`: the head of the `i`-th block is `xs[i]` (needed
for Theorem 11.5 below, so it is proved here rather than in §11.5.4). -/
theorem head_take_nths {i k : ℕ} {xs : List α} (h : i < xs.length) :
    (take_nths i k xs).head? = xs[i]? := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [take_nths]
    | succ j =>
      have hj : j < xs.length := by
        have hlen : (x :: xs).length = xs.length + 1 := rfl; omega
      have h' := ih (i := j) hj
      show (take_nths j k xs).head? = (x :: xs)[j + 1]?
      rw [h', List.getElem?_cons_succ]

/-- **Theorem 11.5** (`brauns_correct` in `Array_Braun.thy`), by the book's
induction on `|xs|` (using (11.10), (11.11), (11.12), (11.16), (11.17)):
for `i < 2^k`, the `i`-th tree of `nodes ts ys (drop 2^k ts)` has root
`xs[i]` and children `ts[i]` / `ts[i + 2^k]` (or `Leaf` when the index is
out of range), and the induction hypothesis gives the `braun_list`
statements for them. -/
theorem brauns_correct_aux : ∀ (n : ℕ) {k : ℕ} {xs : List α}, xs.length = n →
    ∀ {i : ℕ}, i < min xs.length (2 ^ k) →
    ∃ t, (brauns k xs)[i]? = some t ∧ braun_list t (take_nths i k xs) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k xs hxs i hi
    cases xs with
    | nil =>
      have h0 : min ([] : List α).length (2 ^ k) = 0 := by
        simp only [List.length_nil, Nat.min_eq_left (Nat.zero_le _)]
      rw [h0] at hi
      omega
    | cons x xs' =>
      have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
      have hi2 : i < 2 ^ k := (lt_min_iff.mp hi).2
      have hix : i < (x :: xs').length := (lt_min_iff.mp hi).1
      have hzs : ((x :: xs').drop (2 ^ k)).length < n := by
        rw [← hxs, List.length_drop]
        simp only [List.length_cons]
        omega
      have hts_len : (brauns (k + 1) ((x :: xs').drop (2 ^ k))).length
          = min ((x :: xs').drop (2 ^ k)).length (2 ^ (k + 1)) := brauns_length _ _
      have hnod : (brauns k (x :: xs'))[i]?
          = (((x :: xs').take (2 ^ k))[i]?).map (fun y =>
              Tree.Node
                (nthOrLeaf (brauns (k + 1) ((x :: xs').drop (2 ^ k))) i) y
                (nthOrLeaf ((brauns (k + 1) ((x :: xs').drop (2 ^ k))).drop (2 ^ k)) i)) := by
        simp only [brauns]
        exact nth_nodes _ _ _ _
      have hys_take : ((x :: xs').take (2 ^ k))[i]? = (x :: xs')[i]? := by
        simp only [List.getElem?_take, ite_eq_left hi2]
      have hnode : (brauns k (x :: xs'))[i]?
          = some (Tree.Node
              (nthOrLeaf (brauns (k + 1) ((x :: xs').drop (2 ^ k))) i) (x :: xs')[i]
              (nthOrLeaf ((brauns (k + 1) ((x :: xs').drop (2 ^ k))).drop (2 ^ k)) i)) := by
        rw [hnod, hys_take, List.getElem?_eq_getElem hix]
        rfl
      refine ⟨Tree.Node
        (nthOrLeaf (brauns (k + 1) ((x :: xs').drop (2 ^ k))) i) (x :: xs')[i]
        (nthOrLeaf ((brauns (k + 1) ((x :: xs').drop (2 ^ k))).drop (2 ^ k)) i),
        hnode, ?_⟩
      have hhead : (take_nths i k (x :: xs')).head? = some (x :: xs')[i] := by
        rw [head_take_nths hix, List.getElem?_eq_getElem hix]
      have hne : take_nths i k (x :: xs') ≠ [] := take_nths_ne_nil hix
      have hblock1 : take_nths 1 1 (take_nths i k (x :: xs'))
          = take_nths (i + 2 ^ k) (k + 1) (x :: xs') := by
        rw [take_nths_take_nths]
        congr 1 <;> omega
      have hblock2 : take_nths 2 1 (take_nths i k (x :: xs'))
          = take_nths (i + 2 * 2 ^ k) (k + 1) (x :: xs') := by
        rw [take_nths_take_nths]
        congr 1 <;> omega
      refine ⟨hne, hhead, ?_, ?_⟩
      · -- Left child: `ts[i]`, or `Leaf` when `i` is out of range.
        rw [hblock1]
        by_cases hlt : i < (brauns (k + 1) ((x :: xs').drop (2 ^ k))).length
        · have hlt' : i < min ((x :: xs').drop (2 ^ k)).length (2 ^ (k + 1)) := by
            rw [← hts_len]; exact hlt
          obtain ⟨t, ht, hbl⟩ := ih _ hzs (k := k + 1)
            (xs := (x :: xs').drop (2 ^ k)) rfl hlt'
          have hnth : nthOrLeaf (brauns (k + 1) ((x :: xs').drop (2 ^ k))) i = t := by
            show ((brauns (k + 1) ((x :: xs').drop (2 ^ k)))[i]?).getD .Leaf = t
            rw [ht]
            rfl
          rw [hnth]
          have hdrop : take_nths i (k + 1) ((x :: xs').drop (2 ^ k))
              = take_nths (i + 2 ^ k) (k + 1) (x :: xs') :=
            take_nths_drop i (k + 1) (2 ^ k) (x :: xs')
          rw [← hdrop]
          exact hbl
        · have hleaf : nthOrLeaf (brauns (k + 1) ((x :: xs').drop (2 ^ k))) i
              = .Leaf := by
            show ((brauns (k + 1) ((x :: xs').drop (2 ^ k)))[i]?).getD .Leaf = .Leaf
            rw [List.getElem?_eq_none_iff.mpr
              (by omega : (brauns (k + 1) ((x :: xs').drop (2 ^ k))).length ≤ i)]
            rfl
          rw [hleaf]
          have hempty : take_nths (i + 2 ^ k) (k + 1) (x :: xs') = [] := by
            apply (take_nths_empty _ _ _).mpr
            have hge : ((x :: xs').drop (2 ^ k)).length ≤ i := by
              by_contra hc
              push Not at hc
              have hlt2 : i < 2 ^ (k + 1) := by
                have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
                omega
              have h1 : i < min ((x :: xs').drop (2 ^ k)).length (2 ^ (k + 1)) :=
                lt_min_iff.mpr ⟨hc, hlt2⟩
              rw [← hts_len] at h1
              omega
            have hzd : ((x :: xs').drop (2 ^ k)).length
                = (x :: xs').length - 2 ^ k := by
              rw [List.length_drop]
            omega
          rw [hempty]
          exact braun_list_leaf.mpr rfl
      · -- Right child: `ts[i + 2^k]`, or `Leaf` when out of range.
        rw [hblock2]
        have hdrop_nth : nthOrLeaf
            ((brauns (k + 1) ((x :: xs').drop (2 ^ k))).drop (2 ^ k)) i
            = nthOrLeaf (brauns (k + 1) ((x :: xs').drop (2 ^ k))) (2 ^ k + i) := by
          show (((brauns (k + 1) ((x :: xs').drop (2 ^ k))).drop (2 ^ k))[i]?).getD .Leaf
              = ((brauns (k + 1) ((x :: xs').drop (2 ^ k)))[2 ^ k + i]?).getD .Leaf
          rw [List.getElem?_drop]
        rw [hdrop_nth]
        by_cases hlt : 2 ^ k + i < (brauns (k + 1) ((x :: xs').drop (2 ^ k))).length
        · have hlt' : 2 ^ k + i < min ((x :: xs').drop (2 ^ k)).length (2 ^ (k + 1)) := by
            rw [← hts_len]; exact hlt
          obtain ⟨t, ht, hbl⟩ := ih _ hzs (k := k + 1)
            (xs := (x :: xs').drop (2 ^ k)) rfl hlt'
          have hnth : nthOrLeaf (brauns (k + 1) ((x :: xs').drop (2 ^ k))) (2 ^ k + i)
              = t := by
            show ((brauns (k + 1) ((x :: xs').drop (2 ^ k)))[2 ^ k + i]?).getD .Leaf = t
            rw [ht]
            rfl
          rw [hnth]
          have hdrop : take_nths (2 ^ k + i) (k + 1) ((x :: xs').drop (2 ^ k))
              = take_nths (i + 2 * 2 ^ k) (k + 1) (x :: xs') := by
            have h0 := take_nths_drop (2 ^ k + i) (k + 1) (2 ^ k) (x :: xs')
            rw [show (2 ^ k + i) + 2 ^ k = i + 2 * 2 ^ k from by omega] at h0
            exact h0
          rw [← hdrop]
          exact hbl
        · have hleaf : nthOrLeaf (brauns (k + 1) ((x :: xs').drop (2 ^ k))) (2 ^ k + i)
              = .Leaf := by
            show ((brauns (k + 1) ((x :: xs').drop (2 ^ k)))[2 ^ k + i]?).getD .Leaf
                = .Leaf
            rw [List.getElem?_eq_none_iff.mpr
              (by omega : (brauns (k + 1) ((x :: xs').drop (2 ^ k))).length ≤ 2 ^ k + i)]
            rfl
          rw [hleaf]
          have hempty : take_nths (i + 2 * 2 ^ k) (k + 1) (x :: xs') = [] := by
            apply (take_nths_empty _ _ _).mpr
            have hge : ((x :: xs').drop (2 ^ k)).length ≤ 2 ^ k + i := by
              by_contra hc
              push Not at hc
              have hlt2 : 2 ^ k + i < 2 ^ (k + 1) := by
                by_contra hc2
                push Not at hc2
                have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
                omega
              have h1 : 2 ^ k + i < min ((x :: xs').drop (2 ^ k)).length (2 ^ (k + 1)) :=
                lt_min_iff.mpr ⟨hc, hlt2⟩
              rw [← hts_len] at h1
              omega
            have hzd : ((x :: xs').drop (2 ^ k)).length
                = (x :: xs').length - 2 ^ k := by
              rw [List.length_drop]
            omega
          rw [hempty]
          exact braun_list_leaf.mpr rfl

/-- **Theorem 11.5.** `i < min |xs| 2^k ⟹ ∃ t, (brauns k xs)[i]? = some t ∧
braun_list t (take_nths i k xs)` (`brauns_correct` in `Array_Braun.thy`). -/
theorem brauns_correct {xs : List α} {k : ℕ} {i : ℕ}
    (hi : i < min xs.length (2 ^ k)) :
    ∃ t, (brauns k xs)[i]? = some t ∧ braun_list t (take_nths i k xs) :=
  brauns_correct_aux xs.length rfl hi

/-- `brauns1 xs`: the Braun tree with list `xs`
(called `brauns1` in the book). -/
def brauns1 (xs : List α) : Tree α := (brauns 0 xs).head?.getD .Leaf

/-- **Corollary 11.6.** `braun (brauns1 xs) ∧ list (brauns1 xs) = xs`
(from Theorem 11.5 with `i = k = 0`, Lemma 11.4, and (11.8)). -/
theorem brauns1_correct (xs : List α) :
    braun (brauns1 xs) ∧ list (brauns1 xs) = xs := by
  cases xs with
  | nil =>
    have h0 : brauns 0 ([] : List α) = [] := by simp [brauns]
    refine ⟨?_, ?_⟩
    · show braun ((brauns 0 ([] : List α)).head?.getD .Leaf)
      rw [h0]
      exact braun_leaf
    · show list ((brauns 0 ([] : List α)).head?.getD .Leaf) = []
      rw [h0]
      rfl
  | cons x xs' =>
    have h0 : (0 : ℕ) < min (x :: xs').length (2 ^ 0) := by
      have hlen : (x :: xs').length = xs'.length + 1 := rfl
      simp
    obtain ⟨t, ht, hbl⟩ := brauns_correct (xs := x :: xs') (k := 0) (i := 0) h0
    have hbl' : braun_list t (x :: xs') := by
      rw [take_nths_00] at hbl
      exact hbl
    obtain ⟨hb, hl⟩ := braun_list_eq hbl'
    have hhead : (brauns 0 (x :: xs')).head?.getD .Leaf = t := by
      have h0 : (brauns 0 (x :: xs')).head? = (brauns 0 (x :: xs'))[0]? := by
        cases l : brauns 0 (x :: xs') with
        | nil => rfl
        | cons y ys => rfl
      rw [h0, ht]
      rfl
    refine ⟨?_, ?_⟩
    · show braun ((brauns 0 (x :: xs')).head?.getD .Leaf)
      rw [hhead]
      exact hb
    · show list ((brauns 0 (x :: xs')).head?.getD .Leaf) = (x :: xs')
      rw [hhead, ← hl]

/-- Running time of `List.take`: one unit per element traversed, plus one
for the call itself (the book's cost model, Appendix B.4). -/
def Ttake (n : ℕ) (xs : List α) : ℕ := min n xs.length + 1

/-- Running time of `List.drop`: as `Ttake`. -/
def Tdrop (n : ℕ) (xs : List α) : ℕ := min n xs.length + 1

/-- **(11.18)** `Tnodes ls xs rs = |xs| + 1`: running time of `nodes`. -/
def Tnodes (_ls : List (Tree α)) (xs : List α) (_rs : List (Tree α)) : ℕ :=
  xs.length + 1

/-- `Tbrauns k xs`: running time of `brauns k xs` (book §11.5.3.2). The
trailing `+ 1` is the cost of the dispatch itself. The recursive result
is bound once (as in `brauns`), so the recurrence counts a single
recursive call per level. -/
def Tbrauns : ℕ → List α → ℕ
  | _, [] => 1
  | k, x :: xs' =>
      let ts := brauns (k + 1) ((x :: xs').drop (2 ^ k))
      (Ttake (2 ^ k) (x :: xs') + Tdrop (2 ^ k) (x :: xs')
        + Tbrauns (k + 1) ((x :: xs').drop (2 ^ k))
        + Tdrop (2 ^ k) ts
        + Tnodes ts ((x :: xs').take (2 ^ k)) (ts.drop (2 ^ k))) + 1
termination_by _k xs => xs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  omega

/-- **Lemma 11.7.** `Tbrauns` is linear: `Tbrauns k xs ≤ 9 * (|xs| + 1)`.
Proof by induction on `|xs|`, using (11.17), (11.18), and `Ttake`/`Tdrop`.
Unfolding gives `3A + B + Tbrauns (k+1) zs + 5` with `A = min 2^k |xs|`
and `B = min 2^k |zs| ≤ A`; the cases `2^k ≤ |xs|` / `|xs| ≤ 2^k` then
close by arithmetic (`|zs| = |xs| - 2^k`, `|zs| = 0` respectively). -/
theorem Tbrauns_le (k : ℕ) (xs : List α) : Tbrauns k xs ≤ 9 * (xs.length + 1) := by
  have key : ∀ (n : ℕ) {k : ℕ} {xs : List α}, xs.length = n →
      Tbrauns k xs ≤ 9 * (xs.length + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k xs hxs
      cases xs with
      | nil => simp [Tbrauns]
      | cons x xs' =>
        have hzs : ((x :: xs').drop (2 ^ k)).length < n := by
          rw [← hxs, List.length_drop]
          simp only [List.length_cons]
          have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
          omega
        have hIH := ih _ hzs (k := k + 1) (xs := (x :: xs').drop (2 ^ k)) rfl
        have hZ : ((x :: xs').drop (2 ^ k)).length
            = (x :: xs').length - 2 ^ k := by rw [List.length_drop]
        have hX : 1 ≤ (x :: xs').length := by
          have hlen : (x :: xs').length = xs'.length + 1 := rfl; omega
        have hpow : 0 < 2 ^ k := pow_pos (by norm_num) k
        have hle : min (2 ^ k) ((x :: xs').drop (2 ^ k)).length ≤ 2 ^ (k + 1) := by
          calc min (2 ^ k) ((x :: xs').drop (2 ^ k)).length ≤ 2 ^ k :=
                Nat.min_le_left _ _
            _ ≤ 2 ^ (k + 1) := by
                rw [pow_succ']
                have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
                omega
        have hmin : min (2 ^ k)
            (min ((x :: xs').drop (2 ^ k)).length (2 ^ (k + 1)))
            = min (2 ^ k) ((x :: xs').drop (2 ^ k)).length := by
          rw [← min_assoc, Nat.min_eq_left hle]
        simp only [Tbrauns, Ttake, Tdrop, Tnodes, List.length_take, brauns_length, hmin]
        rcases le_total (2 ^ k) (x :: xs').length with hle | hle
        · rw [Nat.min_eq_left hle]
          have hB : min (2 ^ k) ((x :: xs').drop (2 ^ k)).length ≤ 2 ^ k :=
            Nat.min_le_left _ _
          omega
        · rw [Nat.min_eq_right hle]
          have hZ0 : ((x :: xs').drop (2 ^ k)).length = 0 := by omega
          have hB : min (2 ^ k) ((x :: xs').drop (2 ^ k)).length = 0 := by
            rw [hZ0]; exact Nat.min_eq_right (Nat.zero_le _)
          rw [hB]
          omega
  exact key xs.length rfl

end BraunTree
end Cslib.Algorithms.Lean
