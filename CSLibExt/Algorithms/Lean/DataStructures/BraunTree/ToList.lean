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
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.OfList
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Order.MinMax
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Converting a Braun tree into a list (linear time)

`list_fast_rec` / `list_fast` (breadth-first traversal, Theorem 11.8
and its corollary) and `Tlist_fast_rec` (Theorem 11.9).

## Deviations

`list_fast_rec` and `Tlist_fast_rec` use explicit-fuel structural
recursion (`list_fast_rec_go` / `Tlist_fast_rec_go`) with proved
one-step unfolding equations, rather than well-founded recursion on
the filtered child list: the book's recursion is on the filtered
child list, whose termination argument does not transfer directly.

## Cost model

`Tlist_fast_rec` follows the book's closed form: `|ts| + 1 +
5 * (|us| + 1) + Tlist_fast_rec children`, plus one for the call,
where `us` is the filtered (non-`Leaf`) child list. The counter
measures calls of this function, not allocation, traversal, or total
runtime.

The bound in `Tlist_fast_rec_le` is a bound on this modelled
traversal: it does not charge the initial `(ts.map size).sum` pass
that `list_fast_rec` / `Tlist_fast_rec` compute to obtain fuel, nor
the repeated `filter isNonLeaf` evaluations in the executable body
(each level evaluates the filter several times, while the counter
charges one filter pass per level). The end-to-end cost is still
linear in the same quantities (the extras are a constant factor),
but the stated `14 * (∑ |t|) + |ts| + 2` bound is for the modelled
traversal, not an end-to-end bound.

## Provenance

A Lean formalisation of the Chapter 11 Isabelle development in the
Isabelle distribution's `HOL-Data_Structures` theory
(`Braun_Tree.thy`). The book is Tobias Nipkow (ed.), *Functional
Data Structures and Algorithms* (ACM Books, 2025; text version of
July 27, 2026), Chapter 11, §11.5.4 and §11.5.4.2.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace BraunTree

variable {α : Type u}

/-- `bleft`/`bright`: children of a tree (`Leaf` for `Leaf`). -/
def bleft : Tree α → Tree α
  | .Leaf => .Leaf
  | .Node l _ _ => l

/-- The right child of a tree, or `Leaf`. -/
def bright : Tree α → Tree α
  | .Leaf => .Leaf
  | .Node _ _ r => r

/-- `bvalue t`: the root value of `t`, if any. -/
def bvalue : Tree α → Option α
  | .Leaf => none
  | .Node _ x _ => some x

/-- `isNonLeaf t`: whether `t` is not `Leaf` (a `Bool` predicate, so no
`DecidableEq` instance is needed for filtering). -/
def isNonLeaf : Tree α → Bool
  | .Leaf => false
  | .Node _ _ _ => true

/-- `isNonLeaf t = true ↔ t ≠ Leaf`. -/
theorem isNonLeaf_eq_true {t : Tree α} : isNonLeaf t = true ↔ t ≠ .Leaf := by
  cases t with
  | Leaf => simp [isNonLeaf]
  | Node l x r => simp [isNonLeaf]

/-- A nonempty list is not empty. -/
theorem isEmpty_ne_of_ne {l : List (Tree α)} (h : l ≠ []) : ¬ l.isEmpty = true := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l' => simp [List.isEmpty]

/-- Filtering out `Leaf`s does not change the total size (leaves have size 0). -/
theorem sum_size_filter_ne_leaf (ts : List (Tree α)) :
    ((ts.filter isNonLeaf).map size).sum = (ts.map size).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    cases t with
    | Leaf => simp [size, ih, isNonLeaf]
    | Node l x r => simp [List.filter_cons, size, ih, isNonLeaf]

/-- (11.19) `sum_tree_list_children`: the children of non-leaf trees have
total size `∑ |t| - |ts|`. -/
theorem sum_size_children {ts : List (Tree α)} (h : ∀ t ∈ ts, t ≠ .Leaf) :
    (ts.map size).sum = ((ts.map bleft ++ ts.map bright).map size).sum + ts.length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht : t ≠ .Leaf := h t (by simp)
    have hts : ∀ t' ∈ ts, t' ≠ .Leaf := fun t' ht' => h t' (by simp [ht'])
    cases t with
    | Leaf => exact absurd rfl ht
    | Node l x r =>
      have hih := ih hts
      rw [List.map_append, List.sum_append] at hih
      simp only [List.map_cons, List.map_append, List.sum_append, List.sum_cons,
        List.length_cons, size, bleft, bright]
      omega

/-- If the total size is 0, every tree is `Leaf`, so the filter is empty. -/
theorem filter_eq_nil_of_sum_zero {ts : List (Tree α)}
    (h : (ts.map size).sum = 0) : ts.filter isNonLeaf = [] := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have h1 : size t = 0 := by
      simp only [List.map_cons, List.sum_cons] at h
      omega
    have h2 : (List.map size ts).sum = 0 := by
      simp only [List.map_cons, List.sum_cons] at h
      omega
    have ht : t = .Leaf := size_eq_zero_iff.mp h1
    subst ht
    simp [isNonLeaf, ih h2]

/-- The children of the non-`Leaf` trees in `ts` have strictly smaller
total size (the termination argument for `list_fast_rec`). -/
theorem children_sum_lt {ts : List (Tree α)} (hne : ts.filter isNonLeaf ≠ []) :
    (((ts.filter isNonLeaf).map bleft ++ (ts.filter isNonLeaf).map bright).map
        size).sum < (ts.map size).sum := by
  have hmem : ∀ t ∈ ts.filter isNonLeaf, t ≠ .Leaf :=
    fun t ht => isNonLeaf_eq_true.mp (List.mem_filter.mp ht).2
  have hchildren := sum_size_children hmem
  have hsum := sum_size_filter_ne_leaf ts
  have hpos : 0 < (ts.filter isNonLeaf).length :=
    Nat.pos_of_ne_zero (fun hcon => hne (List.eq_nil_of_length_eq_zero hcon))
  omega

/-- `list_fast_rec_go fuel ts`: `list_fast_rec` with an explicit fuel bound.
Structural recursion on `fuel`, so no well-founded recursion is needed. -/
def list_fast_rec_go : ℕ → List (Tree α) → List α
  | 0, _ => []
  | fuel + 1, ts =>
    if (ts.filter isNonLeaf).isEmpty then []
    else (ts.filter isNonLeaf).filterMap bvalue ++
      list_fast_rec_go fuel ((ts.filter isNonLeaf).map bleft ++
        (ts.filter isNonLeaf).map bright)

/-- `list_fast_rec ts`: breadth-first traversal of `ts`, ignoring `Leaf`s
(book §11.5.4). -/
def list_fast_rec (ts : List (Tree α)) : List α :=
  list_fast_rec_go ((ts.map size).sum) ts

/-- With enough fuel, the fuelled traversal agrees with `list_fast_rec`. -/
theorem list_fast_rec_go_correct : ∀ (fuel : ℕ) (ts : List (Tree α)),
    (ts.map size).sum ≤ fuel → list_fast_rec_go fuel ts = list_fast_rec ts := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro ts h
    cases fuel with
    | zero =>
      have hsum0 : (ts.map size).sum = 0 := by omega
      show list_fast_rec_go 0 ts = list_fast_rec_go ((ts.map size).sum) ts
      rw [hsum0]
    | succ m =>
      by_cases hfil : ts.filter isNonLeaf = []
      · have hsum0 : (ts.map size).sum = 0 := by
          have hsum := sum_size_filter_ne_leaf ts
          rw [hfil] at hsum
          simp at hsum
          omega
        show list_fast_rec_go (m + 1) ts = list_fast_rec_go ((ts.map size).sum) ts
        rw [hsum0]
        simp [list_fast_rec_go, hfil]
      · have hne : ts.filter isNonLeaf ≠ [] := hfil
        have hchild_lt := children_sum_lt hne
        obtain ⟨s, hs⟩ :=
          Nat.exists_eq_succ_of_ne_zero (by
            intro h0
            exact hne (filter_eq_nil_of_sum_zero h0))
        have hchild_le_m : (((ts.filter isNonLeaf).map bleft ++
            (ts.filter isNonLeaf).map bright).map size).sum ≤ m := by omega
        have hchild_le_s : (((ts.filter isNonLeaf).map bleft ++
            (ts.filter isNonLeaf).map bright).map size).sum ≤ s := by omega
        have hneg : ¬ (ts.filter isNonLeaf).isEmpty = true :=
          isEmpty_ne_of_ne hne
        show list_fast_rec_go (m + 1) ts = list_fast_rec_go ((ts.map size).sum) ts
        rw [hs]
        show (if (ts.filter isNonLeaf).isEmpty then []
            else (ts.filter isNonLeaf).filterMap bvalue ++
              list_fast_rec_go m ((ts.filter isNonLeaf).map bleft ++
                (ts.filter isNonLeaf).map bright))
          = (if (ts.filter isNonLeaf).isEmpty then []
            else (ts.filter isNonLeaf).filterMap bvalue ++
              list_fast_rec_go s ((ts.filter isNonLeaf).map bleft ++
                (ts.filter isNonLeaf).map bright))
        rw [ite_eq_right hneg, ite_eq_right hneg,
          ih m (by omega) _ hchild_le_m, ih s (by omega) _ hchild_le_s]

/-- The one-step unfolding equation for `list_fast_rec`. -/
theorem list_fast_rec_eq (ts : List (Tree α)) :
    list_fast_rec ts = if (ts.filter isNonLeaf).isEmpty then []
      else (ts.filter isNonLeaf).filterMap bvalue ++
        list_fast_rec ((ts.filter isNonLeaf).map bleft ++
          (ts.filter isNonLeaf).map bright) := by
  show list_fast_rec_go ((ts.map size).sum) ts = _
  by_cases hsum0 : (ts.map size).sum = 0
  · have hfil : ts.filter isNonLeaf = [] := filter_eq_nil_of_sum_zero hsum0
    rw [hsum0]
    simp [list_fast_rec_go, hfil]
  · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hsum0
    have hne : ts.filter isNonLeaf ≠ [] := by
      intro hcon
      exact hsum0 (by
        have hsum := sum_size_filter_ne_leaf ts
        rw [hcon] at hsum
        simp at hsum
        omega)
    have hchild_lt := children_sum_lt hne
    have hchild_le_s : (((ts.filter isNonLeaf).map bleft ++
        (ts.filter isNonLeaf).map bright).map size).sum ≤ s := by omega
    have hneg : ¬ (ts.filter isNonLeaf).isEmpty = true :=
      isEmpty_ne_of_ne hne
    rw [hs]
    show (if (ts.filter isNonLeaf).isEmpty then []
        else (ts.filter isNonLeaf).filterMap bvalue ++
          list_fast_rec_go s ((ts.filter isNonLeaf).map bleft ++
            (ts.filter isNonLeaf).map bright))
      = (if (ts.filter isNonLeaf).isEmpty then []
        else (ts.filter isNonLeaf).filterMap bvalue ++
          list_fast_rec ((ts.filter isNonLeaf).map bleft ++
            (ts.filter isNonLeaf).map bright))
    rw [ite_eq_right hneg, ite_eq_right hneg, list_fast_rec_go_correct s _ hchild_le_s]

/-- `list_fast_rec` of all-`Leaf` trees is `[]`. -/
theorem list_fast_rec_eq_nil_of_all_leaf {ts : List (Tree α)}
    (h : ∀ t ∈ ts, t = .Leaf) : list_fast_rec ts = [] := by
  have hfilter : ts.filter isNonLeaf = [] := by
    rw [List.filter_eq_nil_iff]
    intro t ht
    have htl : t = .Leaf := h t ht
    subst htl
    simp [isNonLeaf]
  rw [list_fast_rec_eq, hfilter]
  simp [List.isEmpty]

/-- If `ys` is shorter than `2^k`, its 0-th block is its first element. -/
theorem take_nths_0_cons_of_lt {k : ℕ} {y : α} {ys : List α}
    (h : (y :: ys).length < 2 ^ k) : take_nths 0 k (y :: ys) = [y] := by
  rw [take_nths_0_cons]
  have h2 : take_nths (2 ^ k - 1) k ys = [] := by
    apply (take_nths_empty _ _ _).mpr
    have hlen : (y :: ys).length = ys.length + 1 := rfl
    have hk : 0 < 2 ^ k := pow_pos (by norm_num) k
    omega
  rw [h2]

/-- If `i < |xs| < 2^k`, the `i`-th block of `xs` is the singleton `[xs[i]]`. -/
theorem take_nths_singleton {i k : ℕ} {xs : List α} (hi : i < xs.length)
    (hlt : xs.length < 2 ^ k) : take_nths i k xs = [xs[i]'hi] := by
  have h1 : take_nths i k xs = take_nths 0 k (xs.drop i) := by
    rw [take_nths_drop 0 k i xs, Nat.zero_add]
  rw [h1, List.drop_eq_getElem_cons hi]
  apply take_nths_0_cons_of_lt
  rw [show (xs[i]'hi :: xs.drop (i + 1)).length = (xs.drop i).length from by
    rw [← List.drop_eq_getElem_cons hi], List.length_drop]
  omega

/-- A `braun_list` tree for a singleton list is a single node over `Leaf`s. -/
theorem braun_list_singleton {t : Tree α} {y : α} (h : braun_list t [y]) :
    t = .Node .Leaf y .Leaf := by
  cases t with
  | Leaf => simp [braun_list] at h
  | Node l x r =>
    obtain ⟨hne, hhead, hbl, hbr⟩ := h
    have hx : x = y := by
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact hhead.symm
    have hl : l = .Leaf := by
      have e : take_nths 1 1 [y] = [] := (take_nths_empty 1 1 [y]).mpr (by simp)
      rw [e] at hbl
      cases l with
      | Leaf => rfl
      | Node l' x' r' =>
        obtain ⟨hne', _, _, _⟩ := hbl
        exact absurd rfl hne'
    have hr : r = .Leaf := by
      have e : take_nths 2 1 [y] = [] := (take_nths_empty 2 1 [y]).mpr (by simp)
      rw [e] at hbr
      cases r with
      | Leaf => rfl
      | Node l' x' r' =>
        obtain ⟨hne', _, _, _⟩ := hbr
        exact absurd rfl hne'
    rw [hl, hr, hx]

/-- A `braun_list` tree for `[]` is `Leaf`. -/
theorem braun_list_nil {t : Tree α} (h : braun_list t []) : t = .Leaf := by
  cases t with
  | Leaf => rfl
  | Node l x r =>
    obtain ⟨hne, _, _, _⟩ := h
    exact absurd rfl hne

/-- Filtering the singleton trees keeps them all. -/
theorem filter_ne_leaf_map {xs : List α} :
    ((xs.map fun x => Tree.Node .Leaf x .Leaf).filter isNonLeaf)
      = xs.map fun x => Tree.Node .Leaf x .Leaf := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.filter_cons, ih, isNonLeaf]

/-- Filtering a list of `Leaf`s gives `[]`. -/
theorem filter_ne_leaf_replicate (n : ℕ) :
    ((List.replicate n (Tree.Leaf : Tree α)).filter isNonLeaf) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, isNonLeaf]

/-- Reading the values of the singleton trees gives the list. -/
theorem filterMap_bvalue_map {xs : List α} :
    ((xs.map fun x => Tree.Node .Leaf x .Leaf).filterMap bvalue) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [bvalue, ih]

/-- `filterMap bvalue` of a tree list whose `i`-th tree has value `xs[i]`
is `take n xs`. -/
theorem filterMap_bvalue_eq_take {ts : List (Tree α)} {xs : List α} {n : ℕ}
    (hlen : ts.length = n) (hxs : n ≤ xs.length)
    (h : ∀ i, i < n → (ts[i]?).bind bvalue = xs[i]?) :
    ts.filterMap bvalue = List.take n xs := by
  induction ts generalizing xs n with
  | nil =>
    have hn0 : n = 0 := by simpa using hlen.symm
    rw [hn0]
    rfl
  | cons t ts ih =>
    have hn1 : 1 ≤ n := by
      have hlen' : (t :: ts).length = n := hlen
      simp only [List.length_cons] at hlen'
      omega
    cases xs with
    | nil =>
      simp at hxs
      omega
    | cons x xs' =>
      have hlen' : ts.length = n - 1 := by
        simp only [List.length_cons] at hlen
        omega
      have hxs' : n - 1 ≤ xs'.length := by
        simp only [List.length_cons] at hxs
        omega
      have h0 : bvalue t = some x := by
        have hh := h 0 (by omega)
        simp only [List.getElem?_cons_zero] at hh
        exact hh
      have h' : ∀ i, i < n - 1 → (ts[i]?).bind bvalue = (xs')[i]? := by
        intro i hi
        have hh := h (i + 1) (by omega)
        rwa [List.getElem?_cons_succ, List.getElem?_cons_succ] at hh
      rw [List.filterMap_cons, h0, ih hlen' hxs' h']
      have hn : n = (n - 1) + 1 := by omega
      conv_rhs => rw [hn, List.take_succ_cons]

/-- The book's `(*)` in the proof of Theorem 11.8: a non-empty `braun_list`
block's tree is a node whose value is `xs[i]` and whose children are the
`braun_list` trees for the two blocks at level `k + 1`. -/
theorem braun_list_node_of_ne {t : Tree α} {i k : ℕ} {xs : List α}
    (h : braun_list t (take_nths i k xs)) (hi : i < xs.length) :
    ∃ l x r, t = .Node l x r ∧ x = xs[i]'hi ∧
      braun_list l (take_nths (i + 2 ^ k) (k + 1) xs) ∧
      braun_list r (take_nths (i + 2 * 2 ^ k) (k + 1) xs) := by
  cases t with
  | Leaf => exact absurd h (take_nths_ne_nil hi)
  | Node l x r =>
    obtain ⟨hne, hhead, hbl, hbr⟩ := h
    refine ⟨l, x, r, rfl, ?_, ?_, ?_⟩
    · have hhd := head_take_nths (k := k) hi
      rw [hhead] at hhd
      rw [List.getElem?_eq_getElem hi] at hhd
      exact Option.some.inj hhd
    · have e : take_nths 1 1 (take_nths i k xs)
          = take_nths (i + 2 ^ k) (k + 1) xs := by
        rw [take_nths_take_nths]
        congr 1 <;> omega
      rw [e] at hbl
      exact hbl
    · have e : take_nths 2 1 (take_nths i k xs)
          = take_nths (i + 2 * 2 ^ k) (k + 1) xs := by
        rw [take_nths_take_nths]
        congr 1 <;> omega
      rw [e] at hbr
      exact hbr

/-- **Theorem 11.8** (`list_fast_rec_correct` in `Array_Braun.thy`),
by strong induction on `|xs|`. -/
theorem list_fast_rec_correct_aux : ∀ (n : ℕ) {k : ℕ} {xs : List α}
    {ts : List (Tree α)}, xs.length = n → ts.length = 2 ^ k →
    (∀ i (hi : i < ts.length), braun_list (ts[i]'hi) (take_nths i k xs)) →
    list_fast_rec ts = xs := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k xs ts hxs hlen h
    by_cases hcase : xs.length < 2 ^ k
    · -- Case `|xs| < 2^k`: every tree is a leaf or a single node.
      have hts : ts = (xs.map fun x => .Node .Leaf x .Leaf) ++
          List.replicate (2 ^ k - xs.length) .Leaf := by
        apply List.ext_getElem?
        intro i
        by_cases hi : i < xs.length
        · have hlen_i : i < ts.length := by rw [hlen]; omega
          have htake : take_nths i k xs = [xs[i]'hi] := take_nths_singleton hi hcase
          have hnode : ts[i]'hlen_i = .Node .Leaf (xs[i]'hi) .Leaf := by
            have hbi := h i hlen_i
            rw [htake] at hbi
            exact braun_list_singleton hbi
          rw [List.getElem?_eq_getElem hlen_i, hnode,
            List.getElem?_append_left (by rw [List.length_map]; exact hi),
            List.getElem?_map, List.getElem?_eq_getElem hi]
          rfl
        · by_cases hi2 : i < 2 ^ k
          · have hlen_i : i < ts.length := by rw [hlen]; exact hi2
            have htake : take_nths i k xs = [] :=
              (take_nths_empty i k xs).mpr (by omega)
            have hleaf : ts[i]'hlen_i = .Leaf := by
              have hbi := h i hlen_i
              rw [htake] at hbi
              exact braun_list_nil hbi
            rw [List.getElem?_eq_getElem hlen_i, hleaf,
              List.getElem?_append_right (by rw [List.length_map]; omega),
              List.length_map,
              List.getElem?_replicate, ite_eq_left (by omega : i - xs.length < 2 ^ k - xs.length)]
          · rw [List.getElem?_eq_none_iff.mpr (by rw [hlen]; omega),
              List.getElem?_eq_none_iff.mpr (by
                rw [List.length_append, List.length_map, List.length_replicate]
                omega)]
      rw [hts]
      have hfilter : (((xs.map fun x => Tree.Node Tree.Leaf x Tree.Leaf) ++
          List.replicate (2 ^ k - xs.length) Tree.Leaf).filter isNonLeaf)
          = xs.map fun x => Tree.Node Tree.Leaf x Tree.Leaf := by
        rw [List.filter_append, filter_ne_leaf_map, filter_ne_leaf_replicate,
          List.append_nil]
      rw [list_fast_rec_eq, hfilter]
      cases xs with
      | nil => simp [List.isEmpty]
      | cons x xs' =>
        rw [ite_eq_right (by simp [List.isEmpty]), filterMap_bvalue_map]
        have hchild : list_fast_rec ((((x :: xs').map fun x => .Node .Leaf x .Leaf).map
            bleft) ++ (((x :: xs').map fun x => .Node .Leaf x .Leaf).map bright)) = [] := by
          apply list_fast_rec_eq_nil_of_all_leaf
          intro t ht
          rw [List.mem_append] at ht
          rcases ht with ht | ht
          · rw [List.mem_map] at ht; obtain ⟨u, hu, rfl⟩ := ht
            rw [List.mem_map] at hu; obtain ⟨v, hv, rfl⟩ := hu
            rfl
          · rw [List.mem_map] at ht; obtain ⟨u, hu, rfl⟩ := ht
            rw [List.mem_map] at hu; obtain ⟨v, hv, rfl⟩ := hu
            rfl
        rw [hchild, List.append_nil]
    · -- Case `2^k ≤ |xs|`: use the roots, then recurse on the children.
      push Not at hcase
      have hk : 0 < 2 ^ k := pow_pos (by norm_num) k
      have hne_all : ∀ i (hi : i < ts.length), ts[i]'hi ≠ .Leaf := by
        intro i hi
        have htake : take_nths i k xs ≠ [] := by
          apply take_nths_ne_nil
          have hi2 : i < 2 ^ k := by rw [← hlen]; exact hi
          omega
        intro hcon
        have hbi := h i hi
        rw [hcon] at hbi
        exact htake hbi
      have hfilter : ts.filter isNonLeaf = ts := by
        rw [List.filter_eq_self]
        intro t ht
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
        exact isNonLeaf_eq_true.mpr (hne_all i hi)
      have hts_ne : ts ≠ [] := by
        intro hcon
        rw [hcon, List.length_nil] at hlen
        exact (pow_ne_zero k (by norm_num)) hlen.symm
      have hvalue : ts.filterMap bvalue = List.take (2 ^ k) xs := by
        apply filterMap_bvalue_eq_take (by rw [hlen]) hcase
        intro i hi
        have hi' : i < ts.length := by rw [hlen]; exact hi
        have hxi : i < xs.length := by omega
        obtain ⟨l, x, r, ht, hx, _, _⟩ := braun_list_node_of_ne (h i hi') hxi
        have hbind : (some (.Node l x r)).bind bvalue = some x := rfl
        rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hxi, ht, hbind, hx]
      have hchildren : list_fast_rec (ts.map bleft ++ ts.map bright)
          = List.drop (2 ^ k) xs := by
        refine ih _ ?_ rfl (k := k + 1) ?_ ?_
        · rw [← hxs, List.length_drop]
          omega
        · rw [List.length_append, List.length_map, List.length_map, hlen, pow_succ']
          omega
        · intro j hj
          have hlen' : (ts.map bleft ++ ts.map bright).length = 2 ^ (k + 1) := by
            rw [List.length_append, List.length_map, List.length_map, hlen, pow_succ']
            omega
          have hj' : j < 2 ^ (k + 1) := by omega
          have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
          by_cases hjk : j < 2 ^ k
          · have hj_ts : j < ts.length := by rw [hlen]; exact hjk
            obtain ⟨l, x, r, ht, hx, hbl, hbr⟩ :=
              braun_list_node_of_ne (h j hj_ts) (by omega : j < xs.length)
            have e1 : (ts.map bleft ++ ts.map bright)[j]'hj
                = bleft (ts[j]'hj_ts) := by
              rw [List.getElem_append_left (by rw [List.length_map]; exact hj_ts),
                List.getElem_map]
            have e2 : take_nths j (k + 1) (List.drop (2 ^ k) xs)
                = take_nths (j + 2 ^ k) (k + 1) xs :=
              take_nths_drop j (k + 1) (2 ^ k) xs
            rw [e1, e2, ht]
            exact hbl
          · have hi : j - 2 ^ k < 2 ^ k := by omega
            have hi_ts : j - 2 ^ k < ts.length := by rw [hlen]; exact hi
            obtain ⟨l, x, r, ht, hx, hbl, hbr⟩ :=
              braun_list_node_of_ne (h (j - 2 ^ k) hi_ts) (by omega : j - 2 ^ k < xs.length)
            have e1 : (ts.map bleft ++ ts.map bright)[j]'hj
                = bright (ts[j - 2 ^ k]'hi_ts) := by
              have hle : (ts.map bleft).length ≤ j := by
                rw [List.length_map, hlen]; omega
              have hget : (ts.map bleft ++ ts.map bright)[j]?
                  = some (bright (ts[j - 2 ^ k]'hi_ts)) := by
                rw [List.getElem?_append_right hle, List.getElem?_map,
                  List.length_map, hlen, List.getElem?_eq_getElem hi_ts]
                rfl
              have h1 := List.getElem?_eq_getElem hj
              rw [hget] at h1
              exact (Option.some.inj h1).symm
            have e2 : take_nths j (k + 1) (List.drop (2 ^ k) xs)
                = take_nths (j - 2 ^ k + 2 * 2 ^ k) (k + 1) xs := by
              rw [take_nths_drop]
              congr 1
              omega
            rw [e1, e2, ht]
            exact hbr
      rw [list_fast_rec_eq, hfilter]
      cases ts with
      | nil => exact absurd rfl hts_ne
      | cons t ts' =>
        rw [ite_eq_right (by simp [List.isEmpty]), hvalue, hchildren,
          List.take_append_drop]

/-- **Theorem 11.8.** `|ts| = 2^k ∧ (∀ i < 2^k. braun_list (ts ! i)
(take_nths i k xs)) ⟹ list_fast_rec ts = xs`. -/
theorem list_fast_rec_correct {k : ℕ} {xs : List α} {ts : List (Tree α)}
    (hlen : ts.length = 2 ^ k)
    (h : ∀ i (hi : i < ts.length), braun_list (ts[i]'hi) (take_nths i k xs)) :
    list_fast_rec ts = xs :=
  list_fast_rec_correct_aux xs.length rfl hlen h

/-- `list_fast t`: the list of a single Braun tree, in linear time as
counted by `Tlist_fast_rec` (see the Cost model note in the module
header). -/
def list_fast (t : Tree α) : List α := list_fast_rec [t]

/-- Corollary of Theorem 11.8: `list_fast t = list t` for Braun `t`. -/
theorem list_fast_correct {t : Tree α} (h : braun t) : list_fast t = list t := by
  have h0 : [t].length = 2 ^ 0 := by simp
  have h1 : ∀ i (hi : i < [t].length),
      braun_list ([t][i]'hi) (take_nths i 0 (list t)) := by
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    show braun_list t (take_nths 0 0 (list t))
    rw [take_nths_00]
    exact braun_list_of_braun h rfl
  exact list_fast_rec_correct h0 h1

/-- The total size is at least the number of non-`Leaf` trees (each
non-`Leaf` tree contributes at least 1). -/
theorem filter_length_le_sum (ts : List (Tree α)) :
    (ts.filter isNonLeaf).length ≤ (ts.map size).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    cases t with
    | Leaf =>
      have e1 : ((Tree.Leaf : Tree α) :: ts).filter isNonLeaf
          = ts.filter isNonLeaf := by
        simp [isNonLeaf]
      have e2 : (((Tree.Leaf : Tree α) :: ts).map size).sum
          = (ts.map size).sum := by
        simp [size]
      rw [e1, e2]
      exact ih
    | Node l x r =>
      have e1 : ((Tree.Node l x r : Tree α) :: ts).filter isNonLeaf
          = (Tree.Node l x r : Tree α) :: ts.filter isNonLeaf := by
        simp [List.filter_cons, isNonLeaf]
      have e2 : (((Tree.Node l x r : Tree α) :: ts).map size).sum
          = size l + size r + 1 + (ts.map size).sum := by
        simp [size]
      rw [e1, e2]
      simp only [List.length_cons]
      omega

/-- `Tlist_fast_rec_go fuel ts`: `Tlist_fast_rec` with an explicit fuel bound
(structural recursion on `fuel`, as for `list_fast_rec_go`). The formula is
the book's: `|ts| + 1` for the `filter`/`length` work, plus `5 * (|us| + 1)`
for the `map`/`append` work when `us ≠ []`, plus `1` for the dispatch. -/
def Tlist_fast_rec_go : ℕ → List (Tree α) → ℕ
  | 0, _ => 0
  | fuel + 1, ts =>
      (ts.length + 1 + (if (ts.filter isNonLeaf).isEmpty then 0
        else 5 * ((ts.filter isNonLeaf).length + 1) +
          Tlist_fast_rec_go fuel ((ts.filter isNonLeaf).map bleft
            ++ (ts.filter isNonLeaf).map bright))) + 1

/-- `Tlist_fast_rec ts`: the modelled running time of `list_fast_rec ts`
(book §11.5.4.2); see the Cost model note in the module header for
what the model does and does not charge. -/
def Tlist_fast_rec (ts : List (Tree α)) : ℕ :=
  Tlist_fast_rec_go ((ts.map size).sum + 2) ts

/-- With enough fuel, the fuelled running time agrees with `Tlist_fast_rec`. -/
theorem Tlist_fast_rec_go_correct : ∀ (fuel : ℕ) (ts : List (Tree α)),
    (ts.map size).sum + 2 ≤ fuel → Tlist_fast_rec_go fuel ts = Tlist_fast_rec ts := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro ts h
    cases fuel with
    | zero => omega
    | succ m =>
      by_cases hfil : ts.filter isNonLeaf = []
      · have hsum0 : (ts.map size).sum = 0 := by
          have hsum := sum_size_filter_ne_leaf ts
          rw [hfil] at hsum
          simp at hsum
          omega
        show Tlist_fast_rec_go (m + 1) ts
            = Tlist_fast_rec_go ((ts.map size).sum + 2) ts
        rw [hsum0]
        simp [Tlist_fast_rec_go, hfil]
      · have hne : ts.filter isNonLeaf ≠ [] := hfil
        have hchild_lt := children_sum_lt hne
        obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (by
          intro h0
          exact hne (filter_eq_nil_of_sum_zero h0))
        have hchild_m : (((ts.filter isNonLeaf).map bleft ++
            (ts.filter isNonLeaf).map bright).map size).sum + 2 ≤ m := by omega
        have hchild_s : (((ts.filter isNonLeaf).map bleft ++
            (ts.filter isNonLeaf).map bright).map size).sum + 2 ≤ s + 2 := by omega
        have hneg : ¬ (ts.filter isNonLeaf).isEmpty = true :=
          isEmpty_ne_of_ne hne
        show Tlist_fast_rec_go (m + 1) ts
            = Tlist_fast_rec_go ((ts.map size).sum + 2) ts
        rw [hs]
        show (ts.length + 1 + (if (ts.filter isNonLeaf).isEmpty then 0
            else 5 * ((ts.filter isNonLeaf).length + 1) +
              Tlist_fast_rec_go m ((ts.filter isNonLeaf).map bleft
                ++ (ts.filter isNonLeaf).map bright))) + 1
          = (ts.length + 1 + (if (ts.filter isNonLeaf).isEmpty then 0
            else 5 * ((ts.filter isNonLeaf).length + 1) +
              Tlist_fast_rec_go (s + 2) ((ts.filter isNonLeaf).map bleft
                ++ (ts.filter isNonLeaf).map bright))) + 1
        rw [ite_eq_right hneg, ite_eq_right hneg, ih m (by omega) _ hchild_m,
          ih (s + 2) (by omega) _ hchild_s]

/-- The one-step unfolding equation for `Tlist_fast_rec`. -/
theorem Tlist_fast_rec_eq (ts : List (Tree α)) :
    Tlist_fast_rec ts = (ts.length + 1 + (if (ts.filter isNonLeaf).isEmpty then 0
      else 5 * ((ts.filter isNonLeaf).length + 1) +
        Tlist_fast_rec ((ts.filter isNonLeaf).map bleft
          ++ (ts.filter isNonLeaf).map bright))) + 1 := by
  show Tlist_fast_rec_go ((ts.map size).sum + 2) ts = _
  by_cases hsum0 : (ts.map size).sum = 0
  · have hfil : ts.filter isNonLeaf = [] := filter_eq_nil_of_sum_zero hsum0
    rw [hsum0]
    simp [Tlist_fast_rec_go, hfil]
  · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hsum0
    have hne : ts.filter isNonLeaf ≠ [] := by
      intro hcon
      exact hsum0 (by
        have hsum := sum_size_filter_ne_leaf ts
        rw [hcon] at hsum
        simp at hsum
        omega)
    have hchild_lt := children_sum_lt hne
    have hneg : ¬ (ts.filter isNonLeaf).isEmpty = true := isEmpty_ne_of_ne hne
    have hfuel : (ts.map size).sum + 2 = (s + 2) + 1 := by omega
    rw [hfuel]
    show (ts.length + 1 + (if (ts.filter isNonLeaf).isEmpty then 0
        else 5 * ((ts.filter isNonLeaf).length + 1) +
          Tlist_fast_rec_go (s + 2) ((ts.filter isNonLeaf).map bleft
            ++ (ts.filter isNonLeaf).map bright))) + 1 = _
    rw [ite_eq_right hneg, ite_eq_right hneg,
      Tlist_fast_rec_go_correct (s + 2) _
        (by omega : (((ts.filter isNonLeaf).map bleft
          ++ (ts.filter isNonLeaf).map bright).map size).sum + 2 ≤ s + 2)]

/-- **Theorem 11.9.** `Tlist_fast_rec` is linear:
`Tlist_fast_rec ts ≤ 14 * (∑_{t ∈ ts} |t|) + |ts| + 2`. Proof by induction
on the size of `ts` (which decreases with each recursive call, (11.19)):
if `us = []` the cost is `|ts| + 2`; otherwise the book's equation
`Tlist_fast_rec ts = Tlist_fast_rec children + 5|us| + |ts| + 7`, the
induction hypothesis, and (11.19) give the bound (using `|us| ≥ 1`).
This is a bound on the modelled traversal (`Tlist_fast_rec`); it
does not include the initial size-sum pass or the repeated filter
evaluations in the executable body (see the Cost model note in the
module header). -/
theorem Tlist_fast_rec_le (ts : List (Tree α)) :
    Tlist_fast_rec ts ≤ 14 * (ts.map size).sum + ts.length + 2 := by
  have key : ∀ (n : ℕ) {ts : List (Tree α)}, (ts.map size).sum = n →
      Tlist_fast_rec ts ≤ 14 * (ts.map size).sum + ts.length + 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro ts hsum
      rw [Tlist_fast_rec_eq]
      by_cases hfil : ts.filter isNonLeaf = []
      · have his : (ts.filter isNonLeaf).isEmpty = true := by simp [hfil]
        rw [ite_eq_left his]
        omega
      · have hne : ts.filter isNonLeaf ≠ [] := hfil
        have hchild_lt := children_sum_lt hne
        have hneg : ¬ (ts.filter isNonLeaf).isEmpty = true := isEmpty_ne_of_ne hne
        rw [ite_eq_right hneg]
        have hsum_child : (((ts.filter isNonLeaf).map bleft
              ++ (ts.filter isNonLeaf).map bright).map size).sum
            = (ts.map size).sum - (ts.filter isNonLeaf).length := by
          have h1 := sum_size_children (ts := ts.filter isNonLeaf)
            (fun t ht => isNonLeaf_eq_true.mp (List.mem_filter.mp ht).2)
          have h2 := sum_size_filter_ne_leaf ts
          omega
        have hlen_child : ((ts.filter isNonLeaf).map bleft
              ++ (ts.filter isNonLeaf).map bright).length
            = 2 * (ts.filter isNonLeaf).length := by
          rw [List.length_append, List.length_map, List.length_map]
          omega
        have hF : 0 < (ts.filter isNonLeaf).length :=
          Nat.pos_of_ne_zero (fun hcon => hne (List.eq_nil_of_length_eq_zero hcon))
        have hSF : (ts.filter isNonLeaf).length ≤ (ts.map size).sum :=
          filter_length_le_sum ts
        have hIH := ih _ (by omega : (((ts.filter isNonLeaf).map bleft
            ++ (ts.filter isNonLeaf).map bright).map size).sum < n) rfl
        omega
  exact key _ rfl

end BraunTree
end Cslib.Algorithms.Lean
