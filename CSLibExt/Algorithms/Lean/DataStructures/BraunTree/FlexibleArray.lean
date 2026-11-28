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

/-!
# Flexible arrays

The flexible-array operations on Braun trees: `del_hi`, `add_lo`,
`merge`, `del_lo` with their correctness specs, the `Array` flex
operations and their specs (both for arrays built from a list and for
arbitrary invariant arrays), `del_lo2` (Exercise 11.6, an equivalent
`del_lo` that avoids the trailing `merge`), and the running-time
bounds for §11.4 (`Tdel_hi`, `Tadd_lo`, `Tmerge`, `Tdel_lo`).

## Cost model

Each `T*` function counts one unit per call. `Tmerge` recurses on
`merge l r` (the node's right child), matching `merge`, and
`Tdel_lo` is one plus `Tmerge`. All four are logarithmic on Braun
trees. The counters measure calls of these functions, not
allocation, traversal, or total runtime.

## Provenance

A Lean formalisation of the Chapter 11 Isabelle development in the
Isabelle distribution's `HOL-Data_Structures` theories
(`Braun_Tree.thy`, `Array_Braun.thy`, `Array_Specs.thy`). The book is
Tobias Nipkow (ed.), *Functional Data Structures and Algorithms*
(ACM Books, 2025; text version of July 27, 2026), Chapter 11, §11.4,
and Exercise 11.6.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace BraunTree

variable {α : Type u}

/-- `del_hi n t`: delete the element with the largest index from a tree
of size `n` (book Fig. 11.5, `del_hi`). -/
def del_hi : ℕ → Tree α → Tree α
  | _, .Leaf => .Leaf
  | n, .Node l x r =>
      if n = 1 then .Leaf
      else if n % 2 = 0 then .Node (del_hi (n / 2) l) x r
      else .Node l x (del_hi (n / 2) r)

/-- `add_lo x t`: prepend `x` (book Fig. 11.5, `add_lo`). -/
def add_lo : α → Tree α → Tree α
  | x, .Leaf => .Node .Leaf x .Leaf
  | x, .Node l a r => .Node (add_lo a r) x l

/-- `merge l r`: the tree with list `splice (list l) (list r)`
(book Fig. 11.5, `merge`). -/
def merge : Tree α → Tree α → Tree α
  | .Leaf, r => r
  | .Node l a r, r' => .Node r' a (merge l r)

/-- `del_lo t`: delete the first element (book Fig. 11.5, `del_lo`). -/
def del_lo : Tree α → Tree α
  | .Leaf => .Leaf
  | .Node l _ r => merge l r

/-- `(a :: l).dropLast = a :: l.dropLast` for `l ≠ []`. -/
theorem dropLast_cons_of_ne {a : α} {l : List α} (h : l ≠ []) :
    (a :: l).dropLast = a :: l.dropLast := by
  cases l with
  | nil => exact absurd rfl h
  | cons b l' => rfl

/-- (47) `butlast_splice`: deleting the last element of a `splice`. -/
theorem butlast_splice (xs ys : List α) :
    (splice xs ys).dropLast
      = if ys.length < xs.length then splice xs.dropLast ys
        else splice xs ys.dropLast := by
  refine splice_ind (P := fun xs ys =>
    (splice xs ys).dropLast
      = if ys.length < xs.length then splice xs.dropLast ys
        else splice xs ys.dropLast) ?_ ?_ xs ys
  · intro ys; simp [splice]
  · intro a xs ys ih
    have hlen : (a :: xs).length = xs.length + 1 := rfl
    by_cases hsp : splice ys xs = []
    · have hnil : ([ ] : List α).length = 0 := rfl
      have h1 : ys = [] := by
        have hl := congrArg List.length hsp
        rw [splice_length] at hl
        exact List.eq_nil_of_length_eq_zero (by omega)
      have h2 : xs = [] := by
        have hl := congrArg List.length hsp
        rw [splice_length] at hl
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst h1; subst h2
      simp [splice]
    · have hpos : 0 < (splice ys xs).length :=
        Nat.pos_of_ne_zero (by
          intro hc; exact hsp (List.eq_nil_of_length_eq_zero hc))
      rw [splice_length] at hpos
      have hLHS : (splice (a :: xs) ys).dropLast = a :: (splice ys xs).dropLast := by
        simp only [splice]
        exact dropLast_cons_of_ne hsp
      rw [hLHS, ih]
      by_cases hcase : ys.length < (a :: xs).length
      · have hxs : xs ≠ [] := by
          rintro rfl
          simp only [List.length_nil, Nat.add_zero] at hpos
          simp only [List.length_cons, List.length_nil] at hcase
          omega
        rw [ite_eq_right (by omega : ¬ xs.length < ys.length), ite_eq_left hcase,
          dropLast_cons_of_ne hxs]
        simp only [splice]
      · have hlt : xs.length < ys.length := by
          have hlen : (a :: xs).length = xs.length + 1 := rfl; omega
        rw [ite_eq_left hlt, ite_eq_right hcase]
        simp only [splice]

/-- (49) `list_merge` + `braun_merge`: `merge` splices the lists and
preserves Braun-ness (for the two children of a Braun node). -/
theorem merge_spec {l r : Tree α} {x : α} (h : braun (Tree.Node l x r)) :
    braun (merge l r) ∧ list (merge l r) = splice (list l) (list r)
      ∧ size (merge l r) = size l + size r := by
  induction l generalizing r x with
  | Leaf =>
    obtain ⟨-, -, hbr⟩ := braun_node.mp h
    refine ⟨hbr, by simp [merge, list, splice], by simp [merge, size]⟩
  | Node l1 a r1 ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    obtain ⟨hb1, hl1, hs1⟩ := ihl (r := r1) (x := a) hbl
    refine ⟨?_, ?_, ?_⟩
    · exact braun_node.mpr
        ⟨by have h1 : size (Tree.Node l1 a r1) = size l1 + size r1 + 1 := rfl; omega,
          hbr, hb1⟩
    · show a :: splice (list r) (list (merge l1 r1))
          = splice (list (Tree.Node l1 a r1)) (list r)
      rw [hl1]
      simp only [list, splice]
    · show size r + size (merge l1 r1) + 1
          = size (Tree.Node l1 a r1) + size r
      rw [hs1]; simp only [size_node]; omega

/-- (50) `list_del_lo` + `braun_del_lo`: deleting the first element. -/
theorem del_lo_spec {t : Tree α} (h : braun t) :
    braun (del_lo t) ∧ list (del_lo t) = (list t).tail
      ∧ size (del_lo t) = size t - 1 := by
  cases t with
  | Leaf =>
    refine ⟨braun_leaf, by simp [del_lo, list], by simp [del_lo, size]⟩
  | Node l a r =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    obtain ⟨hb, hl, hs⟩ :=
      merge_spec (l := l) (r := r) (x := a) (braun_node.mpr ⟨hsz, hbl, hbr⟩)
    refine ⟨hb, ?_, ?_⟩
    · show list (merge l r) = (list (Tree.Node l a r)).tail
      rw [hl, show (list (Tree.Node l a r)).tail = splice (list l) (list r) from rfl]
    · show size (merge l r) = size (Tree.Node l a r) - 1
      rw [hs]; simp only [size_node]; omega

/-- (48) `list_add_lo` + `braun_add_lo`: prepending. -/
theorem add_lo_spec {t : Tree α} (h : braun t) (x : α) :
    braun (add_lo x t) ∧ list (add_lo x t) = x :: list t
      ∧ size (add_lo x t) = size t + 1 := by
  induction t generalizing x with
  | Leaf =>
    refine ⟨?_, ?_, ?_⟩ <;> simp [add_lo, list, splice, size, braun_node, braun]
  | Node l a r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    obtain ⟨hb1, hl1, hs1⟩ := ihr hbr a
    refine ⟨?_, ?_, ?_⟩
    · exact braun_node.mpr
        ⟨by omega, hb1, hbl⟩
    · show x :: splice (list (add_lo a r)) (list l)
          = x :: (a :: splice (list l) (list r))
      rw [hl1]
      simp only [splice]
    · show size (add_lo a r) + size l + 1 = size (Tree.Node l a r) + 1
      rw [hs1]; simp only [size_node]; omega

/-- (46) **(11.6)** `braun_del_hi` + `list_del_hi`: deleting the last element. -/
theorem del_hi_spec {t : Tree α} (h : braun t) :
    braun (del_hi (size t) t) ∧ list (del_hi (size t) t) = (list t).dropLast
      ∧ size (del_hi (size t) t) = size t - 1 := by
  induction t with
  | Leaf =>
    refine ⟨braun_leaf, by simp [del_hi, list], by simp [del_hi, size]⟩
  | Node l a r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    by_cases hn1 : size (Tree.Node l a r) = 1
    · have hl0 : l = .Leaf := by
        have h1 : size l = 0 := by
          have hs : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
        exact size_eq_zero_iff.mp h1
      have hr0 : r = .Leaf := by
        have h1 : size r = 0 := by
          have hs : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
        exact size_eq_zero_iff.mp h1
      subst hl0; subst hr0
      refine ⟨braun_leaf, ?_, ?_⟩
      · show list (del_hi 1 (Tree.Node .Leaf a .Leaf))
            = (list (Tree.Node .Leaf a .Leaf)).dropLast
        simp [del_hi, list, splice]
      · show size (del_hi 1 (Tree.Node .Leaf a .Leaf))
            = size (Tree.Node .Leaf a .Leaf) - 1
        simp [del_hi, size]
    · by_cases hpar : size (Tree.Node l a r) % 2 = 0
      · have hsl : size l = size r + 1 := by
          have hs : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
        have hk : size (Tree.Node l a r) / 2 = size l := by
          have hs : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
        obtain ⟨hb1, hl1, hs1⟩ := ihl hbl
        have e : del_hi (size (Tree.Node l a r)) (Tree.Node l a r)
            = Tree.Node (del_hi (size l) l) a r := by
          simp only [del_hi, ite_eq_right hn1, ite_eq_left hpar, hk]
        rw [e]
        refine ⟨?_, ?_, ?_⟩
        · exact braun_node.mpr ⟨by omega, hb1, hbr⟩
        · show a :: splice (list (del_hi (size l) l)) (list r)
              = (a :: splice (list l) (list r)).dropLast
          rw [hl1]
          have hne : splice (list l) (list r) ≠ [] := by
            intro hc
            have hl := congrArg List.length hc
            rw [splice_length, list_length, list_length] at hl
            simp only [List.length_nil] at hl
            have hs : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
          rw [dropLast_cons_of_ne hne, butlast_splice,
            ite_eq_left (by rw [list_length, list_length]; omega)]
        · simp only [size_node]; omega
      · have hsl : size l = size r := by
          have hs : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
        have hk : size (Tree.Node l a r) / 2 = size r := by
          have hs : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
        obtain ⟨hb2, hl2, hs2⟩ := ihr hbr
        have e : del_hi (size (Tree.Node l a r)) (Tree.Node l a r)
            = Tree.Node l a (del_hi (size r) r) := by
          simp only [del_hi, ite_eq_right hn1, ite_eq_right hpar, hk]
        rw [e]
        refine ⟨?_, ?_, ?_⟩
        · exact braun_node.mpr ⟨by omega, hbl, hb2⟩
        · show a :: splice (list l) (list (del_hi (size r) r))
              = (a :: splice (list l) (list r)).dropLast
          rw [hl2]
          have hne : splice (list l) (list r) ≠ [] := by
            intro hc
            have hl := congrArg List.length hc
            rw [splice_length, list_length, list_length] at hl
            simp only [List.length_nil] at hl
            have hn : size (Tree.Node l a r) = 1 := by
              have hs : size (Tree.Node l a r) = size l + size r + 1 := rfl; omega
            exact hn1 hn
          rw [dropLast_cons_of_ne hne, butlast_splice,
            ite_eq_right (by rw [list_length, list_length]; omega)]
        · simp only [size_node]; omega

/-- Flexible-array operations on `Array` (book Fig. 11.4). -/
def Array.add_lo (a : Array α) (x : α) : Array α :=
  ⟨BraunTree.add_lo x a.tree, a.n + 1⟩

/-- Delete the first element of an array. -/
def Array.del_lo (a : Array α) : Array α := ⟨BraunTree.del_lo a.tree, a.n - 1⟩

/-- Append an element to an array. -/
def Array.add_hi (a : Array α) (x : α) : Array α :=
  ⟨update1 x (a.n + 1) a.tree, a.n + 1⟩

/-- Delete the last element of an array. -/
def Array.del_hi (a : Array α) : Array α := ⟨BraunTree.del_hi a.n a.tree, a.n - 1⟩

/-- (add_lo), (add_lo-inv): flexible-array prepend. -/
theorem flex_add_lo (xs : List α) (x : α) :
    ((Array.ofList xs).add_lo x).toList = x :: xs ∧
    braun (((Array.ofList xs).add_lo x).tree) ∧
    size (((Array.ofList xs).add_lo x).tree) = ((Array.ofList xs).add_lo x).n := by
  show list (add_lo x (ofList xs)) = x :: xs ∧ braun (add_lo x (ofList xs))
    ∧ size (add_lo x (ofList xs)) = xs.length + 1
  obtain ⟨hb, hl, hs⟩ := add_lo_spec (ofList_braun xs) x
  refine ⟨?_, hb, ?_⟩
  · rw [hl, ofList_list]
  · rw [hs, ofList_size]

/-- (del_lo), (del_lo-inv): flexible-array delete-first. -/
theorem flex_del_lo (xs : List α) :
    ((Array.ofList xs).del_lo).toList = xs.tail ∧
    braun (((Array.ofList xs).del_lo).tree) ∧
    size (((Array.ofList xs).del_lo).tree) = ((Array.ofList xs).del_lo).n := by
  show list (del_lo (ofList xs)) = xs.tail ∧ braun (del_lo (ofList xs))
    ∧ size (del_lo (ofList xs)) = xs.length - 1
  obtain ⟨hb, hl, hs⟩ := del_lo_spec (ofList_braun xs)
  refine ⟨?_, hb, ?_⟩
  · rw [hl, ofList_list]
  · rw [hs, ofList_size]

/-- (add_hi), (add_hi-inv): flexible-array append. -/
theorem flex_add_hi (xs : List α) (x : α) :
    ((Array.ofList xs).add_hi x).toList = xs ++ [x] ∧
    braun (((Array.ofList xs).add_hi x).tree) ∧
    size (((Array.ofList xs).add_hi x).tree) = ((Array.ofList xs).add_hi x).n := by
  show list (update1 x (xs.length + 1) (ofList xs)) = xs ++ [x] ∧
    braun (update1 x (xs.length + 1) (ofList xs)) ∧
    size (update1 x (xs.length + 1) (ofList xs)) = xs.length + 1
  rw [← ofList_size xs]
  obtain ⟨hs, hb, hl⟩ := add_hi_spec (ofList_braun xs) x
  rw [ofList_list] at hl
  exact ⟨hl, hb, hs⟩

/-- (del_hi), (del_hi-inv): flexible-array delete-last. -/
theorem flex_del_hi (xs : List α) :
    ((Array.ofList xs).del_hi).toList = xs.dropLast ∧
    braun (((Array.ofList xs).del_hi).tree) ∧
    size (((Array.ofList xs).del_hi).tree) = ((Array.ofList xs).del_hi).n := by
  show list (del_hi xs.length (ofList xs)) = xs.dropLast ∧
    braun (del_hi xs.length (ofList xs)) ∧
    size (del_hi xs.length (ofList xs)) = xs.length - 1
  rw [← ofList_size xs]
  obtain ⟨hb, hl, hs⟩ := del_hi_spec (ofList_braun xs)
  rw [ofList_list] at hl
  exact ⟨hl, hb, hs⟩

/-- (add_lo), (add_lo-inv) for an arbitrary invariant array. -/
theorem flex_add_lo_invar {a : Array α} (h : a.invar) (x : α) :
    ((a.add_lo x).toList = x :: a.toList) ∧ (a.add_lo x).invar := by
  obtain ⟨hb, hsz⟩ := h
  obtain ⟨hb', hl, hs⟩ := add_lo_spec hb x
  refine ⟨?_, ?_⟩
  · show list (add_lo x a.tree) = x :: list a.tree
    exact hl
  · show braun (add_lo x a.tree) ∧ a.n + 1 = size (add_lo x a.tree)
    exact ⟨hb', by omega⟩

/-- (del_lo), (del_lo-inv) for an arbitrary invariant array. -/
theorem flex_del_lo_invar {a : Array α} (h : a.invar) :
    (a.del_lo.toList = a.toList.tail) ∧ (a.del_lo).invar := by
  obtain ⟨hb, hsz⟩ := h
  obtain ⟨hb', hl, hs⟩ := del_lo_spec hb
  refine ⟨?_, ?_⟩
  · show list (del_lo a.tree) = (list a.tree).tail
    exact hl
  · show braun (del_lo a.tree) ∧ a.n - 1 = size (del_lo a.tree)
    exact ⟨hb', by omega⟩

/-- (add_hi), (add_hi-inv) for an arbitrary invariant array. -/
theorem flex_add_hi_invar {a : Array α} (h : a.invar) (x : α) :
    ((a.add_hi x).toList = a.toList ++ [x]) ∧ (a.add_hi x).invar := by
  obtain ⟨hb, hsz⟩ := h
  have h1 : a.n + 1 = size a.tree + 1 := by omega
  obtain ⟨hs, hb', hl⟩ := add_hi_spec hb x
  refine ⟨?_, ?_⟩
  · show list (update1 x (a.n + 1) a.tree) = list a.tree ++ [x]
    rw [h1]
    exact hl
  · show braun (update1 x (a.n + 1) a.tree) ∧ a.n + 1 = size (update1 x (a.n + 1) a.tree)
    rw [h1]
    exact ⟨hb', by omega⟩

/-- (del_hi), (del_hi-inv) for an arbitrary invariant array. -/
theorem flex_del_hi_invar {a : Array α} (h : a.invar) :
    (a.del_hi.toList = a.toList.dropLast) ∧ (a.del_hi).invar := by
  obtain ⟨hb, hsz⟩ := h
  obtain ⟨hb', hl, hs⟩ := del_hi_spec hb
  refine ⟨?_, ?_⟩
  · show list (del_hi a.n a.tree) = (list a.tree).dropLast
    rw [hsz]
    exact hl
  · show braun (del_hi a.n a.tree) ∧ a.n - 1 = size (del_hi a.n a.tree)
    rw [hsz]
    exact ⟨hb', by omega⟩

/-- **Exercise 11.6.** `del_lo2`: delete the first element without any
auxiliary function (cf. `del_lo`, which goes through `merge`). -/
def del_lo2 : Tree α → Tree α
  | .Leaf => .Leaf
  | .Node .Leaf _ r => r
  | .Node (.Node l1 x1 r1) _x r => .Node r x1 (del_lo2 (.Node l1 x1 r1))
termination_by t => size t
decreasing_by simp only [size]; omega

/-- Auxiliary: `del_lo2` agrees with `del_lo` on trees of a given size. -/
theorem del_lo2_eq_aux : ∀ (n : ℕ) (t : Tree α), size t = n → del_lo2 t = del_lo t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t hsize
    cases t with
    | Leaf => simp [del_lo2, del_lo]
    | Node l x r =>
      cases l with
      | Leaf => simp [del_lo2, del_lo, merge]
      | Node l1 x1 r1 =>
        have hlt : size (.Node l1 x1 r1) < n := by
          have hs2 : size (.Node l1 x1 r1) = size l1 + size r1 + 1 := rfl
          simp only [size] at hsize
          omega
        have hih := ih _ hlt _ rfl
        rw [del_lo2.eq_3, hih]
        simp only [del_lo, merge]

/-- **Exercise 11.6.** `del_lo2 t = del_lo t`. -/
theorem del_lo2_eq (t : Tree α) : del_lo2 t = del_lo t :=
  del_lo2_eq_aux (size t) t rfl

/-- `Tdel_hi n t`: running time of `del_hi n t` (1 per call). -/
def Tdel_hi : ℕ → Tree α → ℕ
  | _, .Leaf => 1
  | n, .Node l _ r =>
    if n = 1 then 1
    else if n % 2 = 0 then 1 + Tdel_hi (n / 2) l
    else 1 + Tdel_hi (n / 2) r

/-- **(§11.4)** `del_hi` descends along one branch: `Tdel_hi n t ≤ h t + 1`. -/
theorem Tdel_hi_le (n : ℕ) (t : Tree α) : Tdel_hi n t ≤ height t + 1 := by
  induction t generalizing n with
  | Leaf => simp [Tdel_hi]
  | Node l x r ihl ihr =>
    by_cases hn1 : n = 1
    · subst hn1
      have e : Tdel_hi 1 (Tree.Node l x r) = 1 := by simp [Tdel_hi]
      rw [e]
      have hh : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
      omega
    · by_cases hpar : n % 2 = 0
      · have e : Tdel_hi n (Tree.Node l x r) = 1 + Tdel_hi (n / 2) l := by
          simp [Tdel_hi, hn1, hpar]
        rw [e]
        have hih := ihl (n / 2)
        have hle : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
        have hh : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
        omega
      · have e : Tdel_hi n (Tree.Node l x r) = 1 + Tdel_hi (n / 2) r := by
          simp [Tdel_hi, hn1, hpar]
        rw [e]
        have hih := ihr (n / 2)
        have hle : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
        have hh : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
        omega

/-- `Tadd_lo t`: running time of `add_lo x t` (1 per call; independent of `x`). -/
def Tadd_lo : Tree α → ℕ
  | .Leaf => 1
  | .Node _ _ r => 1 + Tadd_lo r

/-- **(§11.4)** `add_lo` descends along one branch: `Tadd_lo t ≤ h t + 1`. -/
theorem Tadd_lo_le (t : Tree α) : Tadd_lo t ≤ height t + 1 := by
  induction t with
  | Leaf => simp [Tadd_lo]
  | Node l x r ihl ihr =>
    show 1 + Tadd_lo r ≤ height (Tree.Node l x r) + 1
    have hh : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
    have hle : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
    omega

/-- `Tmerge t₁ t₂`: running time of `merge t₁ t₂` (1 per call). -/
def Tmerge : Tree α → Tree α → ℕ
  | .Leaf, _ => 1
  | .Node l _ r, _ => 1 + Tmerge l r

/-- **(§11.4)** `merge` descends along one branch of its first argument:
`Tmerge t₁ t₂ ≤ h t₁ + 1`. -/
theorem Tmerge_le (t₁ t₂ : Tree α) : Tmerge t₁ t₂ ≤ height t₁ + 1 := by
  induction t₁ generalizing t₂ with
  | Leaf => simp [Tmerge]
  | Node l x r ihl ihr =>
    show 1 + Tmerge l r ≤ height (Tree.Node l x r) + 1
    have hih := ihl r
    have hle : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
    have hh : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
    omega

/-- `Tdel_lo t`: running time of `del_lo t` (1 per call). -/
def Tdel_lo : Tree α → ℕ
  | .Leaf => 1
  | .Node l _ r => 1 + Tmerge l r

/-- **(§11.4)** `del_lo` is one `merge` along one branch:
`Tdel_lo t ≤ h t + 1`. -/
theorem Tdel_lo_le (t : Tree α) : Tdel_lo t ≤ height t + 1 := by
  induction t with
  | Leaf => simp [Tdel_lo]
  | Node l x r ihl ihr =>
    show 1 + Tmerge l r ≤ height (Tree.Node l x r) + 1
    have hm := Tmerge_le l r
    have hle : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
    have hh : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
    omega

/-- **(§11.4)** `del_hi` is logarithmic on Braun trees. -/
theorem Tdel_hi_le_braun {n : ℕ} {t : Tree α} (h : braun t) :
    Tdel_hi n t ≤ Nat.log2 (size t) + 2 := by
  have h1 := Tdel_hi_le n t
  have h2 := height_add_one_le_log2_add_two h
  omega

/-- **(§11.4)** `add_lo` is logarithmic on Braun trees. -/
theorem Tadd_lo_le_braun {t : Tree α} (h : braun t) :
    Tadd_lo t ≤ Nat.log2 (size t) + 2 := by
  have h1 := Tadd_lo_le t
  have h2 := height_add_one_le_log2_add_two h
  omega

/-- **(§11.4)** `merge` is logarithmic (in its first argument) on Braun trees. -/
theorem Tmerge_le_braun {t₁ t₂ : Tree α} (h : braun t₁) :
    Tmerge t₁ t₂ ≤ Nat.log2 (size t₁) + 2 := by
  have h1 := Tmerge_le t₁ t₂
  have h2 := height_add_one_le_log2_add_two h
  omega

/-- **(§11.4)** `del_lo` is logarithmic on Braun trees. -/
theorem Tdel_lo_le_braun {t : Tree α} (h : braun t) :
    Tdel_lo t ≤ Nat.log2 (size t) + 2 := by
  have h1 := Tdel_lo_le t
  have h2 := height_add_one_le_log2_add_two h
  omega

end BraunTree
end Cslib.Algorithms.Lean
