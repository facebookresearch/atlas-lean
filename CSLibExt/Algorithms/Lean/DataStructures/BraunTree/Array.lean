/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Splice
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Order.MinMax
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Arrays via Braun trees

The array implementation on Braun trees: `list` (index order),
1-based `lookup1` / `update1`, `adds`, `add_hi`, `ofList` /
`ofListAux`, the `Array` ADT (a `Tree` plus its cached size, with the
invariant `braun tree ∧ n = size tree`), tries as Braun trees
(Exercise 11.5), the Braun-indices characterisation
(`braun_iff_indices`, #10), and the running-time bounds for the
§11.3.2 sketches (`Tlookup1`, `Tupdate1`, `Tlist`, `Tadds`).

## Deviations

`lookup1` returns `Option α` (`none` outside the range) whereas the
book / Isabelle version is total (arbitrary outside the range);
(11.1) / (11.2) are therefore stated with `some` on the Lean side.
`update1` takes a value (not a function) and its `Leaf` case creates a
`Node`, which is what `add_hi` / `adds` need. `log2_mono` /
`log2_succ_le` are general `Nat.log2` lemmas, kept in this module
rather than moved to `MathlibExt`.

## Cost model

`Tlookup1` / `Tupdate1` count one unit per call and descend along a
single branch, so they are logarithmic on Braun trees
(`Tlookup1_le_braun` / `Tupdate1_le_braun`). `Tlist` counts one unit
per call plus the `splice` cost. `Tadds` counts one unit per call
plus the `update1` cost; building an array from a list is O(n lg n)
(`Tadds_le_array`). The counters measure calls of these functions,
not allocation, traversal, or total runtime.

## Provenance

A Lean formalisation of the Chapter 11 Isabelle development in the
Isabelle distribution's `HOL-Data_Structures` theories
(`Braun_Tree.thy`, `Array_Braun.thy`, `Array_Specs.thy`). The book is
Tobias Nipkow (ed.), *Functional Data Structures and Algorithms*
(ACM Books, 2025; text version of July 27, 2026), Chapter 11, §11.3,
§11.3.2, and Exercise 11.5.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace BraunTree

variable {α : Type u}

/-- `list t` = the elements of `t` in index order (book §11.3). -/
def list : Tree α → List α
  | .Leaf => []
  | .Node l x r => x :: splice (list l) (list r)

/-- `(list t).length = size t`. -/
theorem list_length {t : Tree α} : (list t).length = size t := by
  induction t with
  | Leaf => rfl
  | Node l x r ihl ihr =>
    simp only [list, size_node, List.length_cons, splice_length, ihl, ihr]

/-- `lookup1 i t`: element at 1-based index `i` (root = 1, left child
holds even indices, right child odd ones). Argument order `(i, t)`
differs from the book/Isabelle `(t, i)`. Returns `Option α` (`none`
outside range); the book/Isabelle version returns `'a` (total, arbitrary
outside range) — see `list_eq_map_lookup1` for the (11.2) rendering. -/
def lookup1 : ℕ → Tree α → Option α
  | _, .Leaf => none
  | i, .Node l x r =>
      if i = 1 then some x
      else if i % 2 = 0 then lookup1 (i / 2) l
      else lookup1 (i / 2) r

/-- `update1 x i t`: replace the element at 1-based index `i` by `x`; if
`i = |t| + 1`, append `x` (11.5); the `Leaf` case creates the new node.
Argument order `(x, i, t)` differs from the book/Isabelle `(i, x, t)`. -/
def update1 : α → ℕ → Tree α → Tree α
  | x, _, .Leaf => .Node .Leaf x .Leaf
  | x, i, .Node l a r =>
      if i = 1 then .Node l x r
      else if i % 2 = 0 then .Node (update1 x (i / 2) l) a r
      else .Node l a (update1 x (i / 2) r)

/-- (19) `div2_in_bounds`: for a Braun node and `n ∈ {2, …, |Node|}`, the
recursive index `n / 2` lies in range for the child that `n` descends to. -/
theorem div2_in_bounds_even {l r : Tree α} {x : α} {n : ℕ}
    (h : braun (Tree.Node l x r))
    (hn : 1 ≤ n) (hn2 : n ≤ size (Tree.Node l x r)) (_hn1 : n ≠ 1) (hpar : n % 2 = 0) :
    1 ≤ n / 2 ∧ n / 2 ≤ size l := by
  obtain ⟨hsz, -, -⟩ := braun_node.mp h
  have h1 : size (Tree.Node l x r) = size l + size r + 1 := rfl
  omega

/-- (19) `div2_in_bounds_odd`: for a Braun node and an odd `n ∈ {2, …, |Node|}`, the recursive index `n / 2` lies in range for the right child. -/
theorem div2_in_bounds_odd {l r : Tree α} {x : α} {n : ℕ}
    (h : braun (Tree.Node l x r))
    (hn : 1 ≤ n) (hn2 : n ≤ size (Tree.Node l x r)) (hn1 : n ≠ 1) (hpar : n % 2 ≠ 0) :
    1 ≤ n / 2 ∧ n / 2 ≤ size r := by
  obtain ⟨hsz, -, -⟩ := braun_node.mp h
  have h1 : size (Tree.Node l x r) = size l + size r + 1 := rfl
  omega

/-- (23) `size_update1`: updating an in-range index preserves the size. -/
theorem size_update1 {t : Tree α} (h : braun t) {n : ℕ} (hn : 1 ≤ n) (hn2 : n ≤ size t)
    (x : α) : size (update1 x n t) = size t := by
  induction t generalizing n with
  | Leaf => have h0 : size (Tree.Leaf : Tree α) = 0 := rfl; omega
  | Node l a r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    by_cases hn1 : n = 1
    · subst hn1; simp [update1, size_node]
    · by_cases hpar : n % 2 = 0
      · have hd := div2_in_bounds_even h hn hn2 hn1 hpar
        have h1 := ihl hbl (n := n / 2) hd.1 hd.2
        have e : update1 x n (Tree.Node l a r)
            = Tree.Node (update1 x (n / 2) l) a r := by simp [update1, hn1, hpar]
        rw [e]; simp only [size_node]; omega
      · have hd := div2_in_bounds_odd h hn hn2 hn1 hpar
        have h1 := ihr hbr (n := n / 2) hd.1 hd.2
        have e : update1 x n (Tree.Node l a r)
            = Tree.Node l a (update1 x (n / 2) r) := by simp [update1, hn1, hpar]
        rw [e]; simp only [size_node]; omega

/-- (24) `braun_update1`: updating an in-range index preserves Braun-ness. -/
theorem braun_update1 {t : Tree α} (h : braun t) {n : ℕ} (hn : 1 ≤ n) (hn2 : n ≤ size t)
    (x : α) : braun (update1 x n t) := by
  induction t generalizing n with
  | Leaf => have h0 : size (Tree.Leaf : Tree α) = 0 := rfl; omega
  | Node l a r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    by_cases hn1 : n = 1
    · subst hn1
      rw [show update1 x 1 (Tree.Node l a r) = Tree.Node l x r from by simp [update1]]
      exact braun_node.mpr ⟨hsz, hbl, hbr⟩
    · by_cases hpar : n % 2 = 0
      · have hd := div2_in_bounds_even h hn hn2 hn1 hpar
        have hsz' : size (update1 x (n / 2) l) = size l :=
          size_update1 hbl hd.1 hd.2 x
        have hb' : braun (update1 x (n / 2) l) := ihl hbl (n := n / 2) hd.1 hd.2
        rw [show update1 x n (Tree.Node l a r)
            = Tree.Node (update1 x (n / 2) l) a r from by simp [update1, hn1, hpar]]
        exact braun_node.mpr ⟨by rw [hsz']; exact hsz, hb', hbr⟩
      · have hd := div2_in_bounds_odd h hn hn2 hn1 hpar
        have hsz' : size (update1 x (n / 2) r) = size r :=
          size_update1 hbr hd.1 hd.2 x
        have hb' : braun (update1 x (n / 2) r) := ihr hbr (n := n / 2) hd.1 hd.2
        rw [show update1 x n (Tree.Node l a r)
            = Tree.Node l a (update1 x (n / 2) r) from by simp [update1, hn1, hpar]]
        exact braun_node.mpr ⟨by rw [hsz']; exact hsz, hbl, hb'⟩

/-- (11.1) `nth_list_lookup1`: for Braun trees, `lookup1 i t` is the
`(i - 1)`-st element of `list t` (for `i ≥ 1`). -/
theorem lookup1_list {t : Tree α} (h : braun t) (i : ℕ) (hi : 1 ≤ i) :
    lookup1 i t = (list t)[i - 1]? := by
  induction t generalizing i with
  | Leaf => simp [lookup1, list]
  | Node l x r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    have hcond : (list r).length ≤ (list l).length
        ∧ (list l).length ≤ (list r).length + 1 := by
      rw [list_length, list_length]; omega
    by_cases hi1 : i = 1
    · subst hi1; simp [lookup1, list]
    · by_cases hpar : i % 2 = 0
      · have hi2 : 1 ≤ i / 2 := by omega
        have h1 := ihl hbl (i / 2) hi2
        have e1 : lookup1 i (Tree.Node l x r) = lookup1 (i / 2) l := by
          simp [lookup1, hi1, hpar]
        have hd : (i - 2) / 2 = i / 2 - 1 := by omega
        have e2 : (list (Tree.Node l x r))[i - 1]? = (list l)[(i - 2) / 2]? := by
          have hstep : i - 1 = (i - 2) + 1 := by omega
          simp only [list, hstep, List.getElem?_cons_succ]
          rw [splice_getElem? hcond (i - 2), ite_eq_left (by omega : (i - 2) % 2 = 0)]
        rw [e1, e2, h1, hd]
      · have hi2 : 1 ≤ i / 2 := by omega
        have h1 := ihr hbr (i / 2) hi2
        have e1 : lookup1 i (Tree.Node l x r) = lookup1 (i / 2) r := by
          simp [lookup1, hi1, hpar]
        have hd : (i - 2) / 2 = i / 2 - 1 := by omega
        have e2 : (list (Tree.Node l x r))[i - 1]? = (list r)[(i - 2) / 2]? := by
          have hstep : i - 1 = (i - 2) + 1 := by omega
          simp only [list, hstep, List.getElem?_cons_succ]
          rw [splice_getElem? hcond (i - 2), ite_eq_right (by omega : (i - 2) % 2 ≠ 0)]
        rw [e1, e2, h1, hd]

/-- If `lookup1 i t` succeeds for a Braun tree, `i` is in range. -/
theorem lookup1_some_range {t : Tree α} (h : braun t) {i : ℕ} {y : α}
    (hy : lookup1 i t = some y) : 1 ≤ i ∧ i ≤ size t := by
  induction t generalizing i with
  | Leaf => simp [lookup1] at hy
  | Node l a r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    by_cases hi1 : i = 1
    · subst hi1; have h1 : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
    · by_cases hpar : i % 2 = 0
      · have e : lookup1 (i / 2) l = some y := by
          have h1 : lookup1 i (Tree.Node l a r) = lookup1 (i / 2) l := by
            simp [lookup1, hi1, hpar]
          rw [h1] at hy; exact hy
        obtain ⟨h1, h2⟩ := ihl hbl e
        have h3 : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
      · have e : lookup1 (i / 2) r = some y := by
          have h1 : lookup1 i (Tree.Node l a r) = lookup1 (i / 2) r := by
            simp [lookup1, hi1, hpar]
          rw [h1] at hy; exact hy
        obtain ⟨h1, h2⟩ := ihr hbr e
        have h3 : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega

/-- Looking up an out-of-range index gives `none` (contrapositive of
`lookup1_some_range`). -/
theorem lookup1_eq_none {t : Tree α} (h : braun t) {i : ℕ} (hi : size t < i) :
    lookup1 i t = none := by
  cases hlookup : lookup1 i t with
  | none => rfl
  | some y =>
    exfalso
    obtain ⟨-, hle⟩ := lookup1_some_range h hlookup
    omega

/-- **(11.2)** `list_eq_map_lookup1`: the list of a Braun tree is the list of
its `1, …, |t|` lookups. The book/Isabelle `lookup1` returns `'a` (total,
arbitrary outside range); Lean's returns `Option α` (`none` outside range),
so the Lean statement maps `some` on the right-hand side. Proved from
(11.1) (`lookup1_list`) and `lookup1_eq_none` by extensionality. -/
theorem list_eq_map_lookup1 {t : Tree α} (h : braun t) :
    (List.range (size t)).map (fun i => lookup1 (i + 1) t) = (list t).map some := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < size t
  · have hli : i < (list t).length := by rw [list_length]; exact hi
    rw [List.getElem?_map, List.getElem?_range hi,
      List.getElem?_map, List.getElem?_eq_getElem hli]
    show some (lookup1 (i + 1) t) = some (some (list t)[i])
    rw [lookup1_list h (i + 1) (by omega), Nat.add_sub_cancel,
      List.getElem?_eq_getElem hli]
  · rw [List.getElem?_map,
      List.getElem?_eq_none_iff.mpr (by rw [List.length_range]; omega),
      List.getElem?_map, List.getElem?_eq_none_iff.mpr (by rw [list_length]; omega)]
    rfl

/-- (25) `lookup1_update1`: looking up after an update. -/
theorem lookup1_update1 {t : Tree α} (h : braun t) {n : ℕ} (hn : 1 ≤ n) (hn2 : n ≤ size t)
    (x : α) (m : ℕ) :
    lookup1 m (update1 x n t) = if n = m then some x else lookup1 m t := by
  induction t generalizing n m with
  | Leaf => have h0 : size (Tree.Leaf : Tree α) = 0 := rfl; omega
  | Node l a r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    by_cases hn1 : n = 1
    · rw [hn1]
      by_cases hm1 : m = 1
      · subst hm1; simp [lookup1, update1]
      · have h1m : (1 : ℕ) ≠ m := Ne.symm hm1
        rw [ite_eq_right h1m,
          show update1 x 1 (Tree.Node l a r) = Tree.Node l x r from by simp [update1]]
        by_cases hmp : m % 2 = 0 <;> simp [lookup1, hm1, hmp]
    · by_cases hnp : n % 2 = 0
      · have hd := div2_in_bounds_even h hn hn2 hn1 hnp
        by_cases hm1 : m = 1
        · subst hm1
          have e1 : update1 x n (Tree.Node l a r)
              = Tree.Node (update1 x (n / 2) l) a r := by simp [update1, hn1, hnp]
          rw [e1]; simp [lookup1, hn1]
        · by_cases hmp : m % 2 = 0
          · have h1 := ihl hbl (n := n / 2) hd.1 hd.2 (m / 2)
            have e1 : update1 x n (Tree.Node l a r)
                = Tree.Node (update1 x (n / 2) l) a r := by simp [update1, hn1, hnp]
            have e2 : lookup1 m (Tree.Node (update1 x (n / 2) l) a r)
                = lookup1 (m / 2) (update1 x (n / 2) l) := by simp [lookup1, hm1, hmp]
            have e3 : lookup1 m (Tree.Node l a r) = lookup1 (m / 2) l := by
              simp [lookup1, hm1, hmp]
            rw [e1, e2, e3, h1]
            by_cases hnm : n = m
            · subst hnm; simp
            · have hne : n / 2 ≠ m / 2 := by omega
              rw [ite_eq_right hnm, ite_eq_right hne]
          · have hne : n ≠ m := by omega
            have e1 : update1 x n (Tree.Node l a r)
                = Tree.Node (update1 x (n / 2) l) a r := by simp [update1, hn1, hnp]
            have e2 : lookup1 m (Tree.Node (update1 x (n / 2) l) a r)
                = lookup1 (m / 2) r := by simp [lookup1, hm1, hmp]
            have e3 : lookup1 m (Tree.Node l a r) = lookup1 (m / 2) r := by
              simp [lookup1, hm1, hmp]
            rw [e1, e2, e3, ite_eq_right hne]
      · have hd := div2_in_bounds_odd h hn hn2 hn1 hnp
        by_cases hm1 : m = 1
        · subst hm1
          have e1 : update1 x n (Tree.Node l a r)
              = Tree.Node l a (update1 x (n / 2) r) := by simp [update1, hn1, hnp]
          rw [e1]; simp [lookup1, hn1]
        · by_cases hmp : m % 2 = 0
          · have hne : n ≠ m := by omega
            have e1 : update1 x n (Tree.Node l a r)
                = Tree.Node l a (update1 x (n / 2) r) := by simp [update1, hn1, hnp]
            have e2 : lookup1 m (Tree.Node l a (update1 x (n / 2) r))
                = lookup1 (m / 2) l := by simp [lookup1, hm1, hmp]
            have e3 : lookup1 m (Tree.Node l a r) = lookup1 (m / 2) l := by
              simp [lookup1, hm1, hmp]
            rw [e1, e2, e3, ite_eq_right hne]
          · have h1 := ihr hbr (n := n / 2) hd.1 hd.2 (m / 2)
            have e1 : update1 x n (Tree.Node l a r)
                = Tree.Node l a (update1 x (n / 2) r) := by simp [update1, hn1, hnp]
            have e2 : lookup1 m (Tree.Node l a (update1 x (n / 2) r))
                = lookup1 (m / 2) (update1 x (n / 2) r) := by simp [lookup1, hm1, hmp]
            have e3 : lookup1 m (Tree.Node l a r) = lookup1 (m / 2) r := by
              simp [lookup1, hm1, hmp]
            rw [e1, e2, e3, h1]
            by_cases hnm : n = m
            · subst hnm; simp
            · have hne : n / 2 ≠ m / 2 := by omega
              rw [ite_eq_right hnm, ite_eq_right hne]

/-- (26) `list_update1`: the list of an updated tree. -/
theorem list_update1 {t : Tree α} (h : braun t) {n : ℕ} (hn : 1 ≤ n) (hn2 : n ≤ size t)
    (x : α) : list (update1 x n t) = (list t).set (n - 1) x := by
  apply List.ext_getElem?
  intro i
  have hb : braun (update1 x n t) := braun_update1 h hn hn2 x
  have hlen : (list t).length = size t := list_length
  have h1 : (list (update1 x n t))[i]? = lookup1 (i + 1) (update1 x n t) := by
    rw [lookup1_list hb (i + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
  rw [h1, lookup1_update1 h hn hn2 x (i + 1), List.getElem?_set,
    lookup1_list h (i + 1) (by omega)]
  by_cases hnm : n = i + 1
  · have hni : n - 1 = i := by omega
    rw [ite_eq_left hnm, ite_eq_left hni, ite_eq_left (by omega : n - 1 < (list t).length)]
  · have hni : n - 1 ≠ i := by omega
    rw [ite_eq_right hnm, ite_eq_right hni]
    simp only [Nat.add_sub_cancel]

/-- (11.3)–(11.5) `size_add_hi`, `braun_add_hi`, `list_add_hi`: updating
at index `|t| + 1` appends. Proved together by induction on `t`. -/
theorem add_hi_spec {t : Tree α} (h : braun t) (x : α) :
    size (update1 x (size t + 1) t) = size t + 1 ∧
    braun (update1 x (size t + 1) t) ∧
    list (update1 x (size t + 1) t) = list t ++ [x] := by
  induction t with
  | Leaf =>
    exact ⟨rfl, braun_node.mpr ⟨Or.inl rfl, braun_leaf, braun_leaf⟩,
      by simp [update1, list, splice]⟩
  | Node l a r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    by_cases hpar : (size (Tree.Node l a r) + 1) % 2 = 0
    · have hsl : size l = size r := by
        have h1 : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
      have hk : (size (Tree.Node l a r) + 1) / 2 = size l + 1 := by
        have h1 : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
      obtain ⟨hs1, hb1, hl1⟩ := ihl hbl
      have hN1 : size (Tree.Node l a r) + 1 ≠ 1 := by
        have h1 : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
      have e1 : update1 x (size (Tree.Node l a r) + 1) (Tree.Node l a r)
          = Tree.Node (update1 x (size l + 1) l) a r := by
        rw [show update1 x (size (Tree.Node l a r) + 1) (Tree.Node l a r)
            = Tree.Node (update1 x ((size (Tree.Node l a r) + 1) / 2) l) a r from by
          simp only [update1, ite_eq_right hN1, ite_eq_left hpar]]
        rw [hk]
      rw [e1]
      refine ⟨?_, ?_, ?_⟩
      · simp only [size_node]; omega
      · exact braun_node.mpr ⟨Or.inr (by omega), hb1, hbr⟩
      · show a :: splice (list (update1 x (size l + 1) l)) (list r)
            = list (Tree.Node l a r) ++ [x]
        rw [hl1, splice_append_left (by rw [list_length, list_length]; omega) x]
        rfl
    · have hsl : size l = size r + 1 := by
        have h1 : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
      have hk : (size (Tree.Node l a r) + 1) / 2 = size r + 1 := by
        have h1 : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
      obtain ⟨hs2, hb2, hl2⟩ := ihr hbr
      have hN1 : size (Tree.Node l a r) + 1 ≠ 1 := by
        have h1 : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
      have e1 : update1 x (size (Tree.Node l a r) + 1) (Tree.Node l a r)
          = Tree.Node l a (update1 x (size r + 1) r) := by
        rw [show update1 x (size (Tree.Node l a r) + 1) (Tree.Node l a r)
            = Tree.Node l a (update1 x ((size (Tree.Node l a r) + 1) / 2) r) from by
          simp only [update1, ite_eq_right hN1, ite_eq_right hpar]]
        rw [hk]
      rw [e1]
      refine ⟨?_, ?_, ?_⟩
      · simp only [size_node]; omega
      · exact braun_node.mpr ⟨Or.inl (by omega), hbl, hb2⟩
      · show a :: splice (list l) (list (update1 x (size r + 1) r))
            = list (Tree.Node l a r) ++ [x]
        rw [hl2, splice_append_right (by rw [list_length, list_length]; omega) x]
        rfl

/-- `size (update1 x (|t| + 1) t) = size t + 1`. -/
theorem size_add_hi {t : Tree α} (h : braun t) (x : α) :
    size (update1 x (size t + 1) t) = size t + 1 :=
  (add_hi_spec h x).1

/-- `braun (update1 x (|t| + 1) t)`. -/
theorem braun_add_hi {t : Tree α} (h : braun t) (x : α) :
    braun (update1 x (size t + 1) t) :=
  (add_hi_spec h x).2.1

/-- `list (update1 x (|t| + 1) t) = list t ++ [x]`. -/
theorem list_add_hi {t : Tree α} (h : braun t) (x : α) :
    list (update1 x (size t + 1) t) = list t ++ [x] :=
  (add_hi_spec h x).2.2

/-- Append a whole list, by repeated `update1`-appending (starting from the
leaf). `ofListAux_eq_adds` below shows this is `adds` starting from the
tree's own size. -/
def ofListAux : Tree α → List α → Tree α
  | t, [] => t
  | t, x :: xs => ofListAux (update1 x (size t + 1) t) xs

/-- `ofListAux` appends, preserving Braunness and size. -/
theorem ofListAux_spec {t : Tree α} (h : braun t) (xs : List α) :
    list (ofListAux t xs) = list t ++ xs ∧ braun (ofListAux t xs)
      ∧ size (ofListAux t xs) = size t + xs.length := by
  induction xs generalizing t with
  | nil => refine ⟨?_, h, ?_⟩ <;> simp [ofListAux]
  | cons x xs ih =>
    obtain ⟨hl, hb, hs⟩ := ih (t := update1 x (size t + 1) t) (braun_add_hi h x)
    refine ⟨?_, hb, ?_⟩
    · show list (ofListAux (update1 x (size t + 1) t) xs) = list t ++ (x :: xs)
      rw [hl, list_add_hi h x]
      simp [List.append_assoc]
    · show size (ofListAux (update1 x (size t + 1) t) xs)
        = size t + (x :: xs).length
      rw [hs, size_add_hi h x]
      simp [List.length_cons]; omega

/-- `ofList xs`: the Braun tree with list `xs`, built by repeated appending. -/
def ofList : List α → Tree α
  | xs => ofListAux .Leaf xs

/-- `list (ofList xs) = xs`. -/
theorem ofList_list (xs : List α) : list (ofList xs) = xs := by
  have h := (ofListAux_spec braun_leaf xs).1
  simpa [ofList, list] using h

/-- `braun (ofList xs)`. -/
theorem ofList_braun (xs : List α) : braun (ofList xs) :=
  (ofListAux_spec braun_leaf xs).2.1

/-- `size (ofList xs) = xs.length`. -/
theorem ofList_size (xs : List α) : size (ofList xs) = xs.length := by
  have h := (ofListAux_spec braun_leaf xs).2.2
  simpa [ofList, size] using h

/-- `adds xs n t`: append `xs` to the tree `t`, where `n` is the current
size of `t` (book §11.3; `adds` in `Array_Braun.thy`). The caller must
maintain `n = |t|`; each step appends one element with `update1 (n + 1)`
and bumps `n`. The book's `array xs` is `(adds xs 0 ⟨⟩, |xs|)`
(see `Array.ofList_eq_adds`). -/
def adds : List α → ℕ → Tree α → Tree α
  | [], _, t => t
  | x :: xs, n, t => adds xs (n + 1) (update1 x (n + 1) t)

/-- (30) `size_braun_adds` + (31) `list_adds`: appending with the correct
starting index `n = |t|`. The induction maintains `n = |t|` at each step
(via `size_add_hi`): the tree grows by one, and so does the index. -/
theorem adds_spec_gen (xs : List α) (t : Tree α) (h : braun t) (n : ℕ)
    (hn : n = size t) :
    list (adds xs n t) = list t ++ xs ∧ braun (adds xs n t)
      ∧ size (adds xs n t) = size t + xs.length := by
  induction xs generalizing t n with
  | nil => refine ⟨?_, h, ?_⟩ <;> simp [adds]
  | cons x xs ih =>
    have hb1 : braun (update1 x (n + 1) t) := by
      rw [hn]; exact braun_add_hi h x
    have hs1 : size (update1 x (n + 1) t) = size t + 1 := by
      rw [hn]; exact size_add_hi h x
    have hn' : n + 1 = size (update1 x (n + 1) t) := by omega
    obtain ⟨hl, hb, hs⟩ := ih (t := update1 x (n + 1) t) hb1 (n := n + 1) hn'
    refine ⟨?_, hb, ?_⟩
    · show list (adds xs (n + 1) (update1 x (n + 1) t)) = list t ++ (x :: xs)
      rw [hl]
      have hlist : list (update1 x (n + 1) t) = list t ++ [x] := by
        rw [hn]; exact list_add_hi h x
      rw [hlist]
      simp [List.append_assoc]
    · show size (adds xs (n + 1) (update1 x (n + 1) t)) = size t + (x :: xs).length
      rw [hs, hs1]
      simp [List.length_cons]; omega

/-- (31) `list_adds`. -/
theorem list_adds (xs : List α) {t : Tree α} (h : braun t) :
    list (adds xs (size t) t) = list t ++ xs :=
  (adds_spec_gen xs t h (size t) rfl).1

/-- (30) `braun_adds` (Braun part). -/
theorem braun_adds (xs : List α) {t : Tree α} (h : braun t) :
    braun (adds xs (size t) t) :=
  (adds_spec_gen xs t h (size t) rfl).2.1

/-- (30) `size_braun_adds` (size part). -/
theorem size_adds (xs : List α) {t : Tree α} (h : braun t) :
    size (adds xs (size t) t) = size t + xs.length :=
  (adds_spec_gen xs t h (size t) rfl).2.2

/-- `ofListAux` is `adds` starting from the tree's own size: for Braun `t`,
`ofListAux t xs = adds xs (size t) t` (the two repeated-appending loops
coincide, since `size_add_hi` keeps the index in step). -/
theorem ofListAux_eq_adds {t : Tree α} (h : braun t) (xs : List α) :
    ofListAux t xs = adds xs (size t) t := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    show ofListAux (update1 x (size t + 1) t) xs
        = adds xs (size t + 1) (update1 x (size t + 1) t)
    rw [ih (braun_add_hi h x), size_add_hi h x]

/-- `ofList xs = adds xs 0 ⟨⟩`: the book's `array xs`
(`adds xs 0 ⟨⟩, |xs|`). -/
theorem ofList_eq_adds (xs : List α) : ofList xs = adds xs 0 (.Leaf : Tree α) :=
  ofListAux_eq_adds braun_leaf xs

/-- The `Array` ADT (book Fig. 11.1): a Braun tree together with its size
(here kept as the tree itself; `n` is redundant but matches the book's
`(tree, size)` pair representation). -/
structure Array (α : Type u) where
  tree : Tree α
  n : ℕ

/-- `Array.ofList xs`: the array with list `xs`. -/
def Array.ofList (xs : List α) : Array α := ⟨BraunTree.ofList xs, xs.length⟩

/-- `Array.toList a`: the list of the array. -/
def Array.toList (a : Array α) : List α := list a.tree

/-- Lookup: 0-based index `i` is 1-based index `i + 1` in the tree. -/
def Array.lookup (a : Array α) (i : ℕ) : Option α := lookup1 (i + 1) a.tree

/-- Update at 0-based index `i`. Requires `i < a.n` to maintain the
invariant: `update1` at `i + 1` preserves the tree size in range
(`array_update_spec_invar`), but an out-of-range update (e.g. `i = 0`
on an empty array) creates a node via `update1`'s `Leaf` case while
leaving the cached size `a.n` unchanged, breaking `invar`. -/
def Array.update (a : Array α) (i : ℕ) (x : α) : Array α :=
  ⟨update1 x (i + 1) a.tree, a.n⟩

/-- The `Array` invariant (book §11.3): the tree is Braun and `n` is its
size. The ADT specifications in Figures 11.1 and 11.4 are universals over
arrays satisfying this invariant — not just over `Array.ofList`-built
ones — so the `*_invar` theorems below prove them in that generality. -/
def Array.invar (a : Array α) : Prop := braun a.tree ∧ a.n = size a.tree

/-- (array), (array-inv): the array built from a list satisfies the
invariant. -/
theorem Array.ofList_invar (xs : List α) : (Array.ofList xs).invar := by
  -- Bare `ofList` here would resolve to `Array.ofList`; qualify it.
  show braun (BraunTree.ofList xs) ∧ xs.length = size (BraunTree.ofList xs)
  exact ⟨ofList_braun xs, by rw [ofList_size]⟩

/-- (array): the list of the array built from a list is the list. -/
theorem Array.ofList_toList (xs : List α) : (Array.ofList xs).toList = xs := by
  show list (BraunTree.ofList xs) = xs
  exact ofList_list xs

/-- The book's `array xs = (adds xs 0 ⟨⟩, |xs|)` (Fig. 11.3). -/
theorem Array.ofList_eq_adds (xs : List α) :
    Array.ofList xs = ⟨adds xs 0 (.Leaf : Tree α), xs.length⟩ :=
  -- Bare `ofList_eq_adds` would resolve to this very theorem; qualify it.
  congrArg (fun t => (⟨t, xs.length⟩ : Array α)) (BraunTree.ofList_eq_adds xs)

/-- (len): for an invariant array, `n` is the length of the list. -/
theorem Array.invar_len {a : Array α} (h : a.invar) : a.n = (a.toList).length :=
  h.2.trans list_length.symm

/-- (lookup) for an arbitrary invariant array. -/
theorem array_lookup_spec_invar {a : Array α} (h : a.invar) (i : ℕ) :
    a.lookup i = (a.toList)[i]? := by
  show lookup1 (i + 1) a.tree = (list a.tree)[i]?
  rw [lookup1_list h.1 (i + 1) (by omega), Nat.add_sub_cancel]

/-- (update), (update-inv) for an arbitrary invariant array: updating
preserves the list-up-to-update and the invariant. -/
theorem array_update_spec_invar {a : Array α} (h : a.invar) (i : ℕ) (x : α)
    (hi : i < a.n) :
    ((a.update i x).toList = (a.toList).set i x) ∧ (a.update i x).invar := by
  obtain ⟨hb, hsz⟩ := h
  have hn2 : i + 1 ≤ size a.tree := by omega
  refine ⟨?_, ?_⟩
  · show list (update1 x (i + 1) a.tree) = (list a.tree).set i x
    rw [list_update1 hb (by omega) hn2 x]
    simp only [Nat.add_sub_cancel]
  · show braun (update1 x (i + 1) a.tree) ∧ a.n = size (update1 x (i + 1) a.tree)
    exact ⟨braun_update1 hb (by omega) hn2 x,
      by rw [size_update1 hb (by omega) hn2 x]; exact hsz⟩

/-- (lookup) The lookup specification for the array implementation. -/
theorem array_lookup_spec (xs : List α) (i : ℕ) :
    (Array.ofList xs).lookup i = xs[i]? := by
  show lookup1 (i + 1) (ofList xs) = xs[i]?
  rw [lookup1_list (ofList_braun xs) (i + 1) (by omega), ofList_list]
  simp only [Nat.add_sub_cancel]

/-- (update) The update specification for the array implementation
(for in-range indices). -/
theorem array_update_spec (xs : List α) (i : ℕ) (x : α) (hi : i < xs.length) :
    ((Array.ofList xs).update i x).toList = xs.set i x := by
  show list (update1 x (i + 1) (ofList xs)) = xs.set i x
  have hn2 : i + 1 ≤ size (ofList xs) := by rw [ofList_size]; omega
  rw [list_update1 (ofList_braun xs) (by omega) hn2 x, ofList_list]
  simp only [Nat.add_sub_cancel]

/-- `nat_of bs`: the 1-based index of the trie path `bs` (least significant
bit first): `nat_of [] = 1`, `nat_of (b :: bs) = 2 * nat_of bs + bit b`. -/
def nat_of : List Bool → ℕ
  | [] => 1
  | b :: bs => 2 * nat_of bs + (if b then 1 else 0)

/-- `0 < nat_of bs`. -/
theorem nat_of_pos (bs : List Bool) : 0 < nat_of bs := by
  induction bs with
  | nil => simp [nat_of]
  | cons b bs ih =>
    cases b <;> simp [nat_of]; omega

/-- `lookup_trie t bs`: look up the element at trie path `bs`. -/
def lookup_trie : Tree α → List Bool → Option α
  | .Leaf, _ => none
  | .Node _ x _, [] => some x
  | .Node l _ _, false :: bs => lookup_trie l bs
  | .Node _ _ r, true :: bs => lookup_trie r bs

/-- **Exercise 11.5.** Trie lookup is 1-based lookup at `nat_of bs`. -/
theorem lookup_trie_spec {t : Tree α} {bs : List Bool} (h : braun t)
    (h1 : 1 ≤ nat_of bs) (h2 : nat_of bs ≤ size t) :
    lookup_trie t bs = lookup1 (nat_of bs) t := by
  induction bs generalizing t with
  | nil =>
    cases t with
    | Leaf => have hz : size (Tree.Leaf : Tree α) = 0 := rfl; omega
    | Node l x r => rfl
  | cons b bs ih =>
    cases t with
    | Leaf => have hz : size (Tree.Leaf : Tree α) = 0 := rfl; omega
    | Node l x r =>
      obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
      have hsize : size (Tree.Node l x r) = size l + size r + 1 := rfl
      have hpos := nat_of_pos bs
      cases b with
      | false =>
        have hnat : nat_of (false :: bs) = 2 * nat_of bs := by simp [nat_of]
        have hne : nat_of (false :: bs) ≠ 1 := by omega
        have hpar : nat_of (false :: bs) % 2 = 0 := by omega
        have hdiv : nat_of (false :: bs) / 2 = nat_of bs := by omega
        have hb : nat_of bs ≤ size l := by omega
        have e : lookup1 (nat_of (false :: bs)) (Tree.Node l x r)
            = lookup1 (nat_of bs) l := by
          simp [lookup1, hne, hpar, hdiv]
        rw [show lookup_trie (.Node l x r) (false :: bs) = lookup_trie l bs from rfl, e]
        exact ih hbl (by omega) hb
      | true =>
        have hnat : nat_of (true :: bs) = 2 * nat_of bs + 1 := by simp [nat_of]
        have hne : nat_of (true :: bs) ≠ 1 := by omega
        have hpar : nat_of (true :: bs) % 2 ≠ 0 := by omega
        have hdiv : nat_of (true :: bs) / 2 = nat_of bs := by omega
        have hb : nat_of bs ≤ size r := by omega
        have e : lookup1 (nat_of (true :: bs)) (Tree.Node l x r)
            = lookup1 (nat_of bs) r := by
          simp [lookup1, hne, hpar, hdiv]
        rw [show lookup_trie (.Node l x r) (true :: bs) = lookup_trie r bs from rfl, e]
        exact ih hbr (by omega) hb

/-- `update_trie bs x t`: update the element at trie path `bs` to `x`. -/
def update_trie : List Bool → α → Tree α → Tree α
  | [], x, .Node l _ r => .Node l x r
  | [], _, .Leaf => .Leaf
  | false :: bs, x, .Node l y r => .Node (update_trie bs x l) y r
  | true :: bs, x, .Node l y r => .Node l y (update_trie bs x r)
  | _ :: _, _, .Leaf => .Leaf

/-- **Exercise 11.5.** Trie update is 1-based update at `nat_of bs`. -/
theorem update_trie_spec {t : Tree α} {bs : List Bool} (x : α) (h : braun t)
    (h1 : 1 ≤ nat_of bs) (h2 : nat_of bs ≤ size t) :
    update_trie bs x t = update1 x (nat_of bs) t := by
  induction bs generalizing t with
  | nil =>
    cases t with
    | Leaf => have hz : size (Tree.Leaf : Tree α) = 0 := rfl; omega
    | Node l y r => rfl
  | cons b bs ih =>
    cases t with
    | Leaf => have hz : size (Tree.Leaf : Tree α) = 0 := rfl; omega
    | Node l y r =>
      obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
      have hsize : size (Tree.Node l y r) = size l + size r + 1 := rfl
      have hpos := nat_of_pos bs
      cases b with
      | false =>
        have hnat : nat_of (false :: bs) = 2 * nat_of bs := by simp [nat_of]
        have hne : nat_of (false :: bs) ≠ 1 := by omega
        have hpar : nat_of (false :: bs) % 2 = 0 := by omega
        have hdiv : nat_of (false :: bs) / 2 = nat_of bs := by omega
        have hb : nat_of bs ≤ size l := by omega
        have e : update1 x (nat_of (false :: bs)) (Tree.Node l y r)
            = Tree.Node (update1 x (nat_of bs) l) y r := by
          simp [update1, hne, hpar, hdiv]
        rw [show update_trie (false :: bs) x (.Node l y r)
            = .Node (update_trie bs x l) y r from rfl, e,
          ih hbl (by omega) hb]
      | true =>
        have hnat : nat_of (true :: bs) = 2 * nat_of bs + 1 := by simp [nat_of]
        have hne : nat_of (true :: bs) ≠ 1 := by omega
        have hpar : nat_of (true :: bs) % 2 ≠ 0 := by omega
        have hdiv : nat_of (true :: bs) / 2 = nat_of bs := by omega
        have hb : nat_of bs ≤ size r := by omega
        have e : update1 x (nat_of (true :: bs)) (Tree.Node l y r)
            = Tree.Node l y (update1 x (nat_of bs) r) := by
          simp [update1, hne, hpar, hdiv]
        rw [show update_trie (true :: bs) x (.Node l y r)
            = .Node l y (update_trie bs x r) from rfl, e,
          ih hbr (by omega) hb]

/-- The set of Braun indices of a tree: `{i | lookup1 i t ≠ none}`. -/
def braun_indices (t : Tree α) : Set ℕ := {i | lookup1 i t ≠ none}

/-- Index `0` is never a Braun index (`lookup1` is 1-based). -/
theorem lookup1_zero (t : Tree α) : lookup1 0 t = none := by
  induction t with
  | Leaf => rfl
  | Node l x r ihl ihr =>
    have e : lookup1 0 (Tree.Node l x r) = lookup1 0 l := by simp [lookup1]
    rw [e]; exact ihl

/-- Even indices descend to the left child. -/
theorem lookup1_even {j : ℕ} (_hj : 1 ≤ j) {l r : Tree α} {x : α} :
    lookup1 (2 * j) (Tree.Node l x r) = lookup1 j l := by
  have h1 : 2 * j ≠ 1 := by omega
  have h2 : (2 * j) % 2 = 0 := by omega
  have h3 : (2 * j) / 2 = j := by omega
  show (if 2 * j = 1 then some x
      else if (2 * j) % 2 = 0 then lookup1 ((2 * j) / 2) l
      else lookup1 ((2 * j) / 2) r) = lookup1 j l
  rw [ite_eq_right h1, ite_eq_left h2, h3]

/-- Odd indices (other than `1`) descend to the right child. -/
theorem lookup1_odd {j : ℕ} (hj : 1 ≤ j) {l r : Tree α} {x : α} :
    lookup1 (2 * j + 1) (Tree.Node l x r) = lookup1 j r := by
  have h1 : 2 * j + 1 ≠ 1 := by omega
  have h2 : (2 * j + 1) % 2 ≠ 0 := by omega
  have h3 : (2 * j + 1) / 2 = j := by omega
  show (if 2 * j + 1 = 1 then some x
      else if (2 * j + 1) % 2 = 0 then lookup1 ((2 * j + 1) / 2) l
      else lookup1 ((2 * j + 1) / 2) r) = lookup1 j r
  rw [ite_eq_right h1, ite_eq_right h2, h3]

/-- **(#10)** A tree is Braun iff its set of Braun indices is
`{1, …, |t|}`. -/
theorem braun_iff_indices {t : Tree α} :
    braun t ↔ braun_indices t = Set.Icc 1 (size t) := by
  constructor
  · intro h
    ext i
    simp only [braun_indices, Set.mem_ofPred_eq, Set.mem_Icc]
    cases i with
    | zero => simp [lookup1_zero]
    | succ i' =>
      constructor
      · intro hne
        cases hlookup : lookup1 (i' + 1) t with
        | none => exact absurd hlookup hne
        | some y =>
          obtain ⟨h1, h2⟩ := lookup1_some_range h hlookup
          exact ⟨h1, h2⟩
      · intro ⟨h1, h2⟩
        have hli : i' < (list t).length := by rw [list_length]; omega
        rw [lookup1_list h (i' + 1) (by omega), Nat.add_sub_cancel,
          List.getElem?_eq_getElem hli]
        exact Option.some_ne_none _
  · intro h
    have key : ∀ (t : Tree α) (M : ℕ),
        braun_indices t = Set.Icc 1 M → braun t ∧ M = size t := by
      intro t
      induction t with
      | Leaf =>
        intro M hM
        have hM0 : M = 0 := by
          by_contra hne
          have h1mem : (1 : ℕ) ∈ Set.Icc 1 M := by
            simp only [Set.mem_Icc]; omega
          rw [← hM] at h1mem
          simp [braun_indices, lookup1] at h1mem
        subst hM0
        exact ⟨braun_leaf, rfl⟩
      | Node l x r ihl ihr =>
        intro M hM
        have hleft : braun_indices l = Set.Icc 1 (M / 2) := by
          ext j
          simp only [braun_indices, Set.mem_ofPred_eq, Set.mem_Icc]
          constructor
          · intro hj
            have hj0 : 1 ≤ j := by
              by_contra hj0
              push Not at hj0
              have hjz : j = 0 := by omega
              subst hjz
              rw [lookup1_zero] at hj
              exact hj rfl
            have h2j : (2 * j) ∈ Set.Icc 1 M := by
              rw [← hM]
              simp only [braun_indices, Set.mem_ofPred_eq]
              rw [lookup1_even hj0]
              exact hj
            simp only [Set.mem_Icc] at h2j
            exact ⟨hj0, by omega⟩
          · intro ⟨hj1, hj2⟩
            have h2j : (2 * j) ∈ Set.Icc 1 M := by
              simp only [Set.mem_Icc]
              constructor <;> omega
            rw [← hM] at h2j
            simp only [braun_indices, Set.mem_ofPred_eq] at h2j
            rw [lookup1_even hj1] at h2j
            exact h2j
        have hright : braun_indices r = Set.Icc 1 ((M - 1) / 2) := by
          ext j
          simp only [braun_indices, Set.mem_ofPred_eq, Set.mem_Icc]
          constructor
          · intro hj
            have hj0 : 1 ≤ j := by
              by_contra hj0
              push Not at hj0
              have hjz : j = 0 := by omega
              subst hjz
              rw [lookup1_zero] at hj
              exact hj rfl
            have h2j : (2 * j + 1) ∈ Set.Icc 1 M := by
              rw [← hM]
              simp only [braun_indices, Set.mem_ofPred_eq]
              rw [lookup1_odd hj0]
              exact hj
            simp only [Set.mem_Icc] at h2j
            exact ⟨hj0, by omega⟩
          · intro ⟨hj1, hj2⟩
            have h2j : (2 * j + 1) ∈ Set.Icc 1 M := by
              simp only [Set.mem_Icc]
              constructor <;> omega
            rw [← hM] at h2j
            simp only [braun_indices, Set.mem_ofPred_eq] at h2j
            rw [lookup1_odd hj1] at h2j
            exact h2j
        obtain ⟨hbl, hsl⟩ := ihl (M / 2) hleft
        obtain ⟨hbr, hsr⟩ := ihr ((M - 1) / 2) hright
        have hM1 : 1 ≤ M := by
          have h1mem : (1 : ℕ) ∈ braun_indices (Tree.Node l x r) := by
            simp [braun_indices, lookup1]
          rw [hM] at h1mem
          simp only [Set.mem_Icc] at h1mem
          exact h1mem.2
        have hsz : size (Tree.Node l x r) = size l + size r + 1 := rfl
        refine ⟨?_, ?_⟩
        · rw [braun_node]
          exact ⟨by omega, hbl, hbr⟩
        · omega
    exact (key t (size t) h).1

/-- `Tlookup1 i t`: running time of `lookup1 i t` (1 per call). -/
def Tlookup1 : ℕ → Tree α → ℕ
  | _, .Leaf => 1
  | i, .Node l _ r =>
    if i = 1 then 1
    else if i % 2 = 0 then 1 + Tlookup1 (i / 2) l
    else 1 + Tlookup1 (i / 2) r

/-- **(#33)** `lookup1` descends along one branch: `Tlookup1 i t ≤ h t + 1`. -/
theorem Tlookup1_le (i : ℕ) (t : Tree α) : Tlookup1 i t ≤ height t + 1 := by
  induction t generalizing i with
  | Leaf => simp [Tlookup1]
  | Node l x r ihl ihr =>
    by_cases hi1 : i = 1
    · subst hi1
      have e : Tlookup1 1 (Tree.Node l x r) = 1 := by simp [Tlookup1]
      rw [e]
      have hh : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
      omega
    · by_cases hpar : i % 2 = 0
      · have e : Tlookup1 i (Tree.Node l x r) = 1 + Tlookup1 (i / 2) l := by
          simp [Tlookup1, hi1, hpar]
        rw [e]
        have hih := ihl (i / 2)
        have hle : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
        have hh : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
        omega
      · have e : Tlookup1 i (Tree.Node l x r) = 1 + Tlookup1 (i / 2) r := by
          simp [Tlookup1, hi1, hpar]
        rw [e]
        have hih := ihr (i / 2)
        have hle : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
        have hh : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
        omega

/-- `Tupdate1 x i t`: running time of `update1 x i t` (1 per call). -/
def Tupdate1 : α → ℕ → Tree α → ℕ
  | _, _, .Leaf => 1
  | x, i, .Node l _ r =>
    if i = 1 then 1
    else if i % 2 = 0 then 1 + Tupdate1 x (i / 2) l
    else 1 + Tupdate1 x (i / 2) r

/-- **(#33)** `update1` descends along one branch: `Tupdate1 x i t ≤ h t + 1`. -/
theorem Tupdate1_le (x : α) (i : ℕ) (t : Tree α) : Tupdate1 x i t ≤ height t + 1 := by
  induction t generalizing i with
  | Leaf => simp [Tupdate1]
  | Node l x' r ihl ihr =>
    by_cases hi1 : i = 1
    · subst hi1
      have e : Tupdate1 x 1 (Tree.Node l x' r) = 1 := by simp [Tupdate1]
      rw [e]
      have hh : height (Tree.Node l x' r) = max (height l) (height r) + 1 := rfl
      omega
    · by_cases hpar : i % 2 = 0
      · have e : Tupdate1 x i (Tree.Node l x' r) = 1 + Tupdate1 x (i / 2) l := by
          simp [Tupdate1, hi1, hpar]
        rw [e]
        have hih := ihl (i / 2)
        have hle : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
        have hh : height (Tree.Node l x' r) = max (height l) (height r) + 1 := rfl
        omega
      · have e : Tupdate1 x i (Tree.Node l x' r) = 1 + Tupdate1 x (i / 2) r := by
          simp [Tupdate1, hi1, hpar]
        rw [e]
        have hih := ihr (i / 2)
        have hle : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
        have hh : height (Tree.Node l x' r) = max (height l) (height r) + 1 := rfl
        omega

/-- For a Braun tree, `h t + 1 ≤ ⌊log₂ |t|⌋ + 2` (Exercise 11.1's form):
the bridge from height bounds to logarithmic bounds. -/
theorem height_add_one_le_log2_add_two {t : Tree α} (h : braun t) :
    height t + 1 ≤ Nat.log2 (size t) + 2 := by
  by_cases hne : t = .Leaf
  · subst hne; simp [Nat.log2_zero]
  · have hh := braun_height_log h hne; omega

/-- **(#33)** `lookup1` is logarithmic on Braun trees. -/
theorem Tlookup1_le_braun {i : ℕ} {t : Tree α} (h : braun t) :
    Tlookup1 i t ≤ Nat.log2 (size t) + 2 := by
  have h1 := Tlookup1_le i t
  have h2 := height_add_one_le_log2_add_two h
  omega

/-- **(#33)** `update1` is logarithmic on Braun trees. -/
theorem Tupdate1_le_braun {x : α} {i : ℕ} {t : Tree α} (h : braun t) :
    Tupdate1 x i t ≤ Nat.log2 (size t) + 2 := by
  have h1 := Tupdate1_le x i t
  have h2 := height_add_one_le_log2_add_two h
  omega

/-- `Tlist t`: running time of `list t` (1 per call, plus the `splice`). -/
def Tlist : Tree α → ℕ
  | .Leaf => 1
  | .Node l _ r => 1 + Tlist l + Tlist r + Tsplice (list l) (list r)

/-- **(#34)** `list` costs `O(|t| · h t)`: `Tlist t ≤ (|t| + 1) · (h t + 1)`. -/
theorem Tlist_le (t : Tree α) : Tlist t ≤ (size t + 1) * (height t + 1) := by
  induction t with
  | Leaf => simp [Tlist]
  | Node l x r ihl ihr =>
    have hTs : Tsplice (list l) (list r) ≤ size l + size r + 1 := by
      have h := Tsplice_le (list l) (list r)
      rw [list_length, list_length] at h
      exact h
    have e1 : (size l + 1) * (height l + 1)
        ≤ (size l + 1) * (max (height l) (height r) + 1) :=
      Nat.mul_le_mul (le_refl _) (by
        have hle := Nat.le_max_left (height l) (height r)
        omega)
    have e2 : (size r + 1) * (height r + 1)
        ≤ (size r + 1) * (max (height l) (height r) + 1) :=
      Nat.mul_le_mul (le_refl _) (by
        have hle := Nat.le_max_right (height l) (height r)
        omega)
    have e3 : (size l + 1) * (max (height l) (height r) + 1)
        + (size r + 1) * (max (height l) (height r) + 1)
        = (size l + size r + 2) * (max (height l) (height r) + 1) := by ring
    have e4 : (size l + size r + 1 + 1) * (height (Tree.Node l x r) + 1)
        = (size l + size r + 2) * (max (height l) (height r) + 1)
          + (size l + size r + 2) := by
      have hH : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
      rw [hH]; ring
    have hsz : size (Tree.Node l x r) = size l + size r + 1 := rfl
    show 1 + Tlist l + Tlist r + Tsplice (list l) (list r)
        ≤ (size (Tree.Node l x r) + 1) * (height (Tree.Node l x r) + 1)
    rw [hsz, e4]
    omega

/-- **(#34)** `list` is O(n lg n) on Braun trees. -/
theorem Tlist_le_braun {t : Tree α} (h : braun t) :
    Tlist t ≤ (size t + 1) * (Nat.log2 (size t) + 2) := by
  by_cases hne : t = .Leaf
  · subst hne; simp [Tlist, Nat.log2_zero]
  · have hh := braun_height_log h hne
    have hle := Tlist_le t
    rw [hh] at hle
    exact hle

/-- `log2` is monotone. -/
theorem log2_mono {m n : ℕ} (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n := by
  by_cases hm0 : m = 0
  · subst hm0; simp [Nat.log2_zero]
  · by_cases hn0 : n = 0
    · subst hn0; omega
    · have h1 := (Nat.log2_eq_iff hm0).mp rfl
      have h2 := (Nat.log2_eq_iff hn0).mp rfl
      by_contra hgt
      push Not at hgt
      have hle : (2 : ℕ) ^ (Nat.log2 n + 1) ≤ 2 ^ Nat.log2 m :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- `log2 (n + 1) ≤ log2 n + 1`: the logarithm grows by at most one. -/
theorem log2_succ_le (n : ℕ) : Nat.log2 (n + 1) ≤ Nat.log2 n + 1 := by
  by_cases hn0 : n = 0
  · subst hn0
    have h1 : Nat.log2 1 = 0 := by
      rw [Nat.log2_eq_iff (by norm_num)]
      constructor <;> norm_num
    simp only [Nat.zero_add]
    rw [h1, Nat.log2_zero]
    omega
  · have hn1 : n + 1 ≠ 0 := by omega
    have hj := (Nat.log2_eq_iff hn0).mp rfl
    have hk := (Nat.log2_eq_iff hn1).mp rfl
    have hle : (2 : ℕ) ^ Nat.log2 (n + 1) ≤ 2 ^ (Nat.log2 n + 1) := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

/-- Appending or updating in range grows the height by at most one
(for a Braun tree, the height is determined by the size). -/
theorem height_update1_le (t : Tree α) (h : braun t) {n : ℕ} (hn : n ≤ size t) (x : α) :
    height (update1 x (n + 1) t) ≤ height t + 1 := by
  by_cases hle : n + 1 ≤ size t
  · have hsz := size_update1 h (by omega) hle x
    have hb := braun_update1 h (by omega) hle x
    by_cases hne : t = .Leaf
    · subst hne
      have hn0 : n = 0 := by
        have hsz0 : size (Tree.Leaf : Tree α) = 0 := rfl
        omega
      subst hn0
      simp [update1]
    · have hpos : size t ≠ 0 := by
        intro hz; exact hne (size_eq_zero_iff.mp hz)
      have hne2 : update1 x (n + 1) t ≠ .Leaf := by
        intro hc
        have hsz0 : size (update1 x (n + 1) t) = 0 := by rw [hc]; rfl
        omega
      have h1 := braun_height_log h hne
      have h2 := braun_height_log hb hne2
      rw [hsz] at h2
      omega
  · have happ : n + 1 = size t + 1 := by omega
    rw [happ]
    by_cases hne : t = .Leaf
    · subst hne; simp [update1]
    · have hsz := size_add_hi h x
      have hb := braun_add_hi h x
      have hne2 : update1 x (size t + 1) t ≠ .Leaf := by
        intro hc
        have hsz0 : size (update1 x (size t + 1) t) = 0 := by rw [hc]; rfl
        omega
      have h1 := braun_height_log h hne
      have h2 := braun_height_log hb hne2
      rw [hsz] at h2
      have hlog := log2_succ_le (size t)
      omega

/-- `Tadds xs n t`: running time of `adds xs n t` (1 per call, plus the
`update1` at each step). -/
def Tadds : List α → ℕ → Tree α → ℕ
  | [], _, _ => 1
  | x :: xs, n, t => 1 + Tupdate1 x (n + 1) t + Tadds xs (n + 1) (update1 x (n + 1) t)

/-- **(#34)** Building an array costs O(n lg n): with `n ≤ |t|` and `t`
Braun, `Tadds xs n t ≤ (|xs| + 1) · (⌊log₂ (|t| + |xs|)⌋ + 3)`. The
`+3` absorbs the per-call unit and the `+1` from the height bound; the
logarithm grows because the tree grows by at most one element per step
(`height_update1_le`) and `log2` is monotone. -/
theorem Tadds_le (xs : List α) (n : ℕ) (t : Tree α) (h : braun t) (hn : n ≤ size t) :
    Tadds xs n t ≤ (xs.length + 1) * (Nat.log2 (size t + xs.length) + 3) := by
  induction xs generalizing n t with
  | nil =>
    simp only [Tadds, List.length_nil, Nat.add_zero]
    omega
  | cons x xs' ih =>
    have hupd : Tupdate1 x (n + 1) t ≤ Nat.log2 (size t) + 2 := by
      by_cases hne : t = .Leaf
      · subst hne
        have hn0 : n = 0 := by
          have hsz0 : size (Tree.Leaf : Tree α) = 0 := rfl
          omega
        subst hn0
        simp [Tupdate1, Nat.log2_zero]
      · have h1 := Tupdate1_le x (n + 1) t
        have h2 := braun_height_log h hne
        omega
    have hb' : braun (update1 x (n + 1) t) := by
      by_cases hle : n + 1 ≤ size t
      · exact braun_update1 h (by omega) hle x
      · have happ : n + 1 = size t + 1 := by omega
        rw [happ]; exact braun_add_hi h x
    have hn' : n + 1 ≤ size (update1 x (n + 1) t) := by
      by_cases hle : n + 1 ≤ size t
      · rw [size_update1 h (by omega) hle x]; exact hle
      · have happ : n + 1 = size t + 1 := by omega
        rw [happ, size_add_hi h x]
    have hsz' : size (update1 x (n + 1) t) + xs'.length
        ≤ size t + (x :: xs').length := by
      have hsz2 : size (update1 x (n + 1) t) ≤ size t + 1 := by
        by_cases hle : n + 1 ≤ size t
        · rw [size_update1 h (by omega) hle x]; omega
        · have happ : n + 1 = size t + 1 := by omega
          rw [happ, size_add_hi h x]
      simp only [List.length_cons]
      omega
    have hlog : Nat.log2 (size (update1 x (n + 1) t) + xs'.length)
        ≤ Nat.log2 (size t + (x :: xs').length) := log2_mono hsz'
    have hIH := ih (n + 1) (update1 x (n + 1) t) hb' hn'
    have hIH2 : Tadds xs' (n + 1) (update1 x (n + 1) t)
        ≤ (xs'.length + 1) * (Nat.log2 (size t + (x :: xs').length) + 3) :=
      le_trans hIH (Nat.mul_le_mul (le_refl _) (by have hle := hlog; omega))
    have hL : Nat.log2 (size t) ≤ Nat.log2 (size t + (x :: xs').length) :=
      log2_mono (by simp only [List.length_cons]; omega)
    have hupd2 : Tupdate1 x (n + 1) t
        ≤ Nat.log2 (size t + (x :: xs').length) + 2 := by omega
    have e : ((x :: xs').length + 1) * (Nat.log2 (size t + (x :: xs').length) + 3)
        = (xs'.length + 1) * (Nat.log2 (size t + (x :: xs').length) + 3)
          + (Nat.log2 (size t + (x :: xs').length) + 3) := by
      simp only [List.length_cons]; ring
    show 1 + Tupdate1 x (n + 1) t + Tadds xs' (n + 1) (update1 x (n + 1) t)
        ≤ ((x :: xs').length + 1) * (Nat.log2 (size t + (x :: xs').length) + 3)
    rw [e]
    calc 1 + Tupdate1 x (n + 1) t + Tadds xs' (n + 1) (update1 x (n + 1) t)
        ≤ 1 + (Nat.log2 (size t + (x :: xs').length) + 2)
            + (xs'.length + 1) * (Nat.log2 (size t + (x :: xs').length) + 3) :=
          Nat.add_le_add (Nat.add_le_add_left hupd2 1) hIH2
      _ = (xs'.length + 1) * (Nat.log2 (size t + (x :: xs').length) + 3)
            + (Nat.log2 (size t + (x :: xs').length) + 3) := by omega

/-- **(#34)** Building an array from a list costs O(n lg n). -/
theorem Tadds_le_array (xs : List α) :
    Tadds xs 0 .Leaf ≤ (xs.length + 1) * (Nat.log2 xs.length + 3) := by
  have h := Tadds_le xs 0 .Leaf braun_leaf (by simp)
  simpa using h

end BraunTree
end Cslib.Algorithms.Lean
