/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Skew_Heap/Skew_Heap.thy` (Archive of Formal Proofs, entry `Skew Heap`, https://isa-afp.org/entries/Skew_Heap.html):
Copyright (c) 2014 Tobias Nipkow. All rights reserved.
Licensed under the BSD License.
Authors: Tobias Nipkow
-/

module

public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Skew-heap carrier and merge

Binary trees, the heap predicate, and skew-heap merge: the plain
binary-tree carrier `Tree` (book `'a tree`), `size`, `height`,
`mset_tree`, `set_tree`, `heap`, the skew merge with its size /
multiset / set / heap correctness lemmas, the alternative `merge2`
(with the Lean-only `set_merge2` / `heap_merge2`), the naive merge of
§14.1 (Exercise 14.2), and the priority-queue operations
`insert` / `delMin` / `getMin` defined from `merge` as in §14.1.

Source: the AFP entry `Skew Heap` (Tobias Nipkow, 2014; BSD),
`thys/Skew_Heap/Skew_Heap.thy`
(https://isa-afp.org/entries/Skew_Heap.html), for `merge`, `merge2`,
and their size / multiset / set / heap lemmas. The `heap` predicate
follows `HOL-Data_Structures.Heaps` and book section 14.1; `set_tree`
and `size` follow book Ch. 4. The definitions and proofs are
re-established in Lean; Isabelle-derived names are kept for
traceability to those sources.
Deliberate divergences from the Isabelle sources, preserved here:
`getMin` is `Option`-valued (Isabelle's `get_min` is partial on
`Leaf`); `set_tree` is defined recursively (Ch. 4 / HOL-Library)
with `set_mset_tree` as the proved lemma `toSet_eq`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace SkewHeap

variable {α : Type u}


/-- Binary trees, the book's `'a tree`: `leaf` is `⟨⟩`, `node l a r` is `⟨l; a; r⟩`. -/
inductive Tree (α : Type u) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving DecidableEq

/-- `size t`: number of nodes of `t` (book `|t|`). -/
def size : Tree α → ℕ
  | .leaf => 0
  | .node l _ r => size l + size r + 1

@[simp] theorem size_leaf : size (Tree.leaf : Tree α) = 0 := rfl
@[simp] theorem size_node (l : Tree α) (a : α) (r : Tree α) :
    size (.node l a r) = size l + size r + 1 := rfl

/-- `height t`: number of nodes on a longest root-to-leaf path. -/
def height : Tree α → ℕ
  | .leaf => 0
  | .node l _ r => max (height l) (height r) + 1

@[simp] theorem height_leaf : height (Tree.leaf : Tree α) = 0 := rfl
@[simp] theorem height_node (l : Tree α) (a : α) (r : Tree α) :
    height (.node l a r) = max (height l) (height r) + 1 := rfl

/-- `mset_tree t`: the multiset of elements of `t` (book `mset_tree`). -/
def toMultiset : Tree α → Multiset α
  | .leaf => 0
  | .node l a r => toMultiset l + ({a} : Multiset α) + toMultiset r

@[simp] theorem toMultiset_leaf : toMultiset (Tree.leaf : Tree α) = 0 := rfl
@[simp] theorem toMultiset_node (l : Tree α) (a : α) (r : Tree α) :
    toMultiset (.node l a r) = toMultiset l + ({a} : Multiset α) + toMultiset r := rfl

/-- `set_mset s`: the set underlying a multiset (Isabelle `set_mset`).
Mathlib has no `Multiset.toSet` in this toolchain (checked with
Loogle: only `Multiset.toFinset`, which needs `DecidableEq`), so it is
defined here as `{x | x ∈ s}`. -/
def msetToSet (s : Multiset α) : Set α := {x | x ∈ s}

theorem msetToSet_add (s t : Multiset α) :
    msetToSet (s + t) = msetToSet s ∪ msetToSet t := by
  ext x; simp [msetToSet, Multiset.mem_add]

theorem msetToSet_singleton (a : α) : msetToSet {a} = {a} := by
  ext x; simp [msetToSet]

theorem msetToSet_zero : msetToSet (0 : Multiset α) = ∅ := by
  ext x; simp [msetToSet]

/-- `set_tree t`: the set of elements of `t` (book Ch. 4 `set_tree`,
HOL-Library). Defined by the same recursion as in the book, not as
a composition with `mset_tree`. -/
def toSet : Tree α → Set α
  | .leaf => ∅
  | .node l a r => toSet l ∪ {a} ∪ toSet r

@[simp] theorem toSet_leaf : toSet (Tree.leaf : Tree α) = ∅ := rfl

@[simp] theorem toSet_node (l : Tree α) (a : α) (r : Tree α) :
    toSet (.node l a r) = toSet l ∪ {a} ∪ toSet r := rfl

/-- `set_mset_tree`: `set_tree t = set_mset (mset_tree t)`.
In Isabelle this is a lemma, proved by induction; here too. -/
theorem toSet_eq (t : Tree α) : toSet t = msetToSet (toMultiset t) := by
  induction t with
  | leaf => simp [msetToSet]
  | node l a r ihl ihr =>
    rw [toSet_node, toMultiset_node, msetToSet_add, msetToSet_add,
      msetToSet_singleton, ← ihl, ← ihr]

/-- Membership in the multiset is membership in the set. -/
theorem mem_toMultiset_iff_mem_toSet (x : α) (t : Tree α) :
    x ∈ toMultiset t ↔ x ∈ toSet t := by
  rw [toSet_eq]; exact Iff.rfl

/-- The book's (§14.1) order for `mset_tree` of a node:
`{#a#} + mset_tree l + mset_tree r`. Isabelle/HOL's `mset_tree`
puts the singleton in the middle (`toMultiset_node`); the two agree
because multiset addition is commutative. -/
theorem toMultiset_node_alt (l : Tree α) (a : α) (r : Tree α) :
    toMultiset (.node l a r) = ({a} : Multiset α) + toMultiset l + toMultiset r := by
  rw [toMultiset_node]; ac_rfl

variable {α : Type u} [LinearOrder α]

/-- `heap t`: `t` is heap-ordered (every node's value is ≤ every value
in its subtrees). This is the definition from
`HOL-Data_Structures.Heaps` (Isabelle distribution, not in the AFP
tree): `heap Leaf = True`, and for a node, both subtrees are heaps and
the root is ≤ every element of both subtrees. -/
def heap : Tree α → Prop
  | .leaf => True
  | .node l a r => heap l ∧ heap r ∧ (∀ x ∈ toSet l, a ≤ x) ∧ (∀ y ∈ toSet r, a ≤ y)

theorem heap_leaf : heap (Tree.leaf : Tree α) := trivial

theorem heap_node {l r : Tree α} {a : α} :
    heap (.node l a r) ↔
      heap l ∧ heap r ∧ (∀ x ∈ toSet l, a ≤ x) ∧ (∀ y ∈ toSet r, a ≤ y) :=
  Iff.rfl

/-- Every element of a heap-ordered node is ≥ the node's value. -/
theorem heap_all_ge {l r : Tree α} {a : α} (h : heap (.node l a r)) :
    ∀ x ∈ toSet (.node l a r), a ≤ x := by
  rw [heap_node] at h
  intro x hx
  rw [toSet_node] at hx
  simp only [Set.mem_union, Set.mem_singleton_iff] at hx
  rcases hx with (hx | rfl) | hx
  · exact h.2.2.1 x hx
  · exact le_refl _
  · exact h.2.2.2 x hx

/-- The book's (§14.1) form of `heap` on a node: the root is ≤ every
element of `set_tree l ∪ set_tree r`. Equivalent to the conjunction
of the two subtree bounds used in the `heap` definition (which follows
`HOL-Data_Structures.Heaps`). -/
theorem heap_node_union {l r : Tree α} {a : α} :
    heap (.node l a r) ↔
      (∀ x ∈ toSet l ∪ toSet r, a ≤ x) ∧ heap l ∧ heap r := by
  rw [heap_node]
  constructor
  · rintro ⟨hl, hr, hlge, hrge⟩
    refine ⟨?_, hl, hr⟩
    intro x hx
    rcases hx with hx | hx
    · exact hlge x hx
    · exact hrge x hx
  · rintro ⟨hunion, hl, hr⟩
    refine ⟨hl, hr, ?_, ?_⟩
    · intro x hx; exact hunion x (Or.inl hx)
    · intro x hx; exact hunion x (Or.inr hx)

/-- Every element of a heap-ordered node, in multiset form. -/
theorem heap_all_ge_mset {l r : Tree α} {a : α} (h : heap (.node l a r)) :
    ∀ x ∈ toMultiset (.node l a r), a ≤ x :=
  fun x hx => heap_all_ge h x ((mem_toMultiset_iff_mem_toSet x _).mp hx)

theorem heap_singleton (a : α) : heap (.node .leaf a .leaf) := by
  rw [heap_node]
  exact ⟨heap_leaf, heap_leaf, fun x hx => by simp at hx,
    fun x hx => by simp at hx⟩

/- ## §22.1: `merge` -/

/-- Skew-heap merge: keep the smaller root, merge the other tree
against that root's right child, and swap the children at every node
on the merge path. The recursive-equation counter `T_merge` follows
these same branches. -/
def merge : Tree α → Tree α → Tree α
  | .leaf, t => t
  | t, .leaf => t
  | .node l1 a1 r1, .node l2 a2 r2 =>
      if a1 ≤ a2 then .node (merge (.node l2 a2 r2) r1) a1 l1
      else .node (merge (.node l1 a1 r1) r2) a2 l2
termination_by t1 t2 => size t1 + size t2
decreasing_by (all_goals simp only [size_node]; omega)

theorem merge_leaf_left (t : Tree α) : merge .leaf t = t := by simp [merge]

theorem merge_leaf_right (t : Tree α) : merge t .leaf = t := by
  cases t with
  | leaf => simp [merge]
  | node l a r => simp [merge]

theorem merge_node_node (l1 _a1 r1 l2 _a2 r2 : Tree α) (v1 v2 : α) :
    merge (.node l1 v1 r1) (.node l2 v2 r2) =
      (if v1 ≤ v2 then .node (merge (.node l2 v2 r2) r1) v1 l1
       else .node (merge (.node l1 v1 r1) r2) v2 l2) := by
  simp [merge]

/-- `merge_code`: the `case`-based reformulation of `merge`. -/
theorem merge_code (t1 t2 : Tree α) :
    merge t1 t2 =
      match t1, t2 with
      | .leaf, _ => t2
      | .node l1 a1 r1, .leaf => .node l1 a1 r1
      | .node l1 a1 r1, .node l2 a2 r2 =>
          if a1 ≤ a2 then .node (merge (.node l2 a2 r2) r1) a1 l1
          else .node (merge (.node l1 a1 r1) r2) a2 l2 := by
  cases t1 with
  | leaf => simp [merge]
  | node l1 a1 r1 =>
    cases t2 with
    | leaf => simp [merge]
    | node l2 a2 r2 => simp [merge]

/-- Book #1: `size_merge`. -/
theorem size_merge (t1 t2 : Tree α) : size (merge t1 t2) = size t1 + size t2 := by
  induction t1, t2 using merge.induct with
  | case1 t => simp [merge]
  | case2 t ht => simp [merge]
  | case3 l1 a1 r1 l2 a2 r2 h ih => simp [merge, h, ih]; omega
  | case4 l1 a1 r1 l2 a2 r2 h ih => simp [merge, h, ih]; omega

/-- Book #2: `mset_merge`. -/
theorem mset_merge (t1 t2 : Tree α) :
    toMultiset (merge t1 t2) = toMultiset t1 + toMultiset t2 := by
  induction t1, t2 using merge.induct with
  | case1 t => simp [merge]
  | case2 t ht => simp [merge]
  | case3 l1 a1 r1 l2 a2 r2 h ih => simp [merge, h, ih]; ac_rfl
  | case4 l1 a1 r1 l2 a2 r2 h ih => simp [merge, h, ih]; ac_rfl

/-- `set_merge`. Isabelle proves this by `metis` from `mset_merge`,
`set_mset_tree`, and `set_mset_union`; this proof has exactly that
shape: `set_merge` is a corollary of `mset_merge`. -/
theorem set_merge (t1 t2 : Tree α) : toSet (merge t1 t2) = toSet t1 ∪ toSet t2 := by
  simp [toSet_eq, mset_merge, msetToSet_add]

/-- Book #3: `heap_merge`. -/
theorem heap_merge {t1 t2 : Tree α} (h1 : heap t1) (h2 : heap t2) :
    heap (merge t1 t2) := by
  induction t1, t2 using merge.induct with
  | case1 t => simpa [merge] using h2
  | case2 t ht => simpa [merge_leaf_right] using h1
  | case3 l1 a1 r1 l2 a2 r2 h ih =>
    have h1' := (heap_node).mp h1
    have hmerge : heap (merge (.node l2 a2 r2) r1) := ih h2 h1'.2.1
    rw [show merge (.node l1 a1 r1) (.node l2 a2 r2) =
      .node (merge (.node l2 a2 r2) r1) a1 l1 by simp [merge, h]]
    rw [heap_node]
    refine ⟨hmerge, h1'.1, ?_, h1'.2.2.1⟩
    intro x hx
    rw [set_merge] at hx
    rcases hx with hx | hx
    · exact le_trans h (heap_all_ge h2 x hx)
    · exact h1'.2.2.2 x hx
  | case4 l1 a1 r1 l2 a2 r2 h ih =>
    have h1' := (heap_node).mp h1
    have h2' := (heap_node).mp h2
    have hmerge : heap (merge (.node l1 a1 r1) r2) := ih h1 h2'.2.1
    rw [show merge (.node l1 a1 r1) (.node l2 a2 r2) =
      .node (merge (.node l1 a1 r1) r2) a2 l2 by simp [merge, h]]
    rw [heap_node]
    refine ⟨hmerge, h2'.1, ?_, h2'.2.2.1⟩
    intro x hx
    rw [set_merge] at hx
    rcases hx with hx | hx
    · exact le_trans (le_of_lt (lt_of_not_ge h)) (heap_all_ge h1 x hx)
    · exact h2'.2.2.2 x hx

/-- The `Heap_Merge` locale (`HOL-Data_Structures.Heaps`), as a structure:
a merge operation together with its two defining properties.
Isabelle's locale also defines `insert`, `del_min`, `get_min` from
`merge`; in this file those are the file-level `insert` / `delMin` /
`getMin` below, defined from `SkewHeap.merge` in exactly the same way. -/
structure HeapMerge (α : Type u) [LinearOrder α] where
  merge : Tree α → Tree α → Tree α
  mset_merge : ∀ t1 t2, toMultiset (merge t1 t2) = toMultiset t1 + toMultiset t2
  heap_merge : ∀ {t1 t2}, heap t1 → heap t2 → heap (merge t1 t2)

/-- The `interpretation skew_heap: Heap_Merge` at the end of `Skew_Heap.thy`. -/
def skewHeapMerge : HeapMerge α where
  merge := merge
  mset_merge := mset_merge
  heap_merge := heap_merge

/-- The alternative `merge2`, which always walks to the `Leaf` of both heaps. -/
def merge2 : Tree α → Tree α → Tree α
  | .leaf, .leaf => .leaf
  | .leaf, .node l2 a2 r2 => .node (merge2 r2 .leaf) a2 l2
  | .node l1 a1 r1, .leaf => .node (merge2 r1 .leaf) a1 l1
  | .node l1 a1 r1, .node l2 a2 r2 =>
      if a1 ≤ a2 then .node (merge2 (.node l2 a2 r2) r1) a1 l1
      else .node (merge2 (.node l1 a1 r1) r2) a2 l2
termination_by t1 t2 => size t1 + size t2
decreasing_by (all_goals simp only [size_node]; omega)

/-- `size_merge2`. -/
theorem size_merge2 (t1 t2 : Tree α) : size (merge2 t1 t2) = size t1 + size t2 := by
  induction t1, t2 using merge2.induct with
  | case1 => simp [merge2]
  | case2 l2 a2 r2 ih => simp [merge2, ih]; omega
  | case3 l1 a1 r1 ih => simp [merge2, ih]; omega
  | case4 l1 a1 r1 l2 a2 r2 h ih => simp [merge2, h, ih]; omega
  | case5 l1 a1 r1 l2 a2 r2 h ih => simp [merge2, h, ih]; omega

/-- `mset_merge2`. This is an additional Lean lemma: Isabelle's
`Skew_Heap.thy` proves `size_merge2` but not the multiset version. -/
theorem mset_merge2 (t1 t2 : Tree α) :
    toMultiset (merge2 t1 t2) = toMultiset t1 + toMultiset t2 := by
  induction t1, t2 using merge2.induct with
  | case1 => simp [merge2]
  | case2 l2 a2 r2 ih => simp [merge2, ih]; ac_rfl
  | case3 l1 a1 r1 ih => simp [merge2, ih]; ac_rfl
  | case4 l1 a1 r1 l2 a2 r2 h ih => simp [merge2, h, ih]; ac_rfl
  | case5 l1 a1 r1 l2 a2 r2 h ih => simp [merge2, h, ih]; ac_rfl

/- ## Priority-queue operations (§14.1, via `merge`) -/

/-- `insert a t = merge ⟨⟨⟩; a; ⟨⟩⟩ t`. -/
def insert (a : α) (t : Tree α) : Tree α := merge (.node .leaf a .leaf) t

/-- `delMin`: remove the root (the minimum), merging its subtrees. -/
def delMin : Tree α → Tree α
  | .leaf => .leaf
  | .node l _ r => merge l r

/-- Non-vacuity checks: concrete counterexamples showing the
definitions are not trivial / vacuous (e.g. `merge` is not
commutative, `heap` is not always true, `Phi` is not always `0`).
These are proved theorems, not random tests: the `plausible` tactic
cannot be used for this out of the box, because it needs
`SampleableExt` instances for the custom `Tree` type and decidable
predicates (`heap` is a `Prop`, not `Decidable`), and deriving those
instances in this file would pollute the development. -/
theorem merge_not_commutative :
    ∃ t1 t2 : Tree ℕ,
      merge t1 t2 ≠ merge t2 t1 := by
  refine ⟨.node .leaf 0 .leaf, .node .leaf 0 (.node .leaf 0 .leaf), ?_⟩
  simp [merge]

theorem exists_non_heap : ∃ t : Tree ℕ, ¬ heap t := by
  refine ⟨.node .leaf 1 (.node .leaf 0 .leaf), ?_⟩
  intro h
  have h' := (heap_node).mp h
  have h0 : (0 : ℕ) ∈ toSet (.node .leaf 0 .leaf) := by simp [toSet_node]
  have := h'.2.2.2 0 h0
  norm_num at this

theorem insert_changes : ∃ (a : ℕ) (t : Tree ℕ), insert a t ≠ t := by
  refine ⟨0, .leaf, ?_⟩
  simp [insert, merge]

/-- `getMin`: the root value, if any. Isabelle's `get_min` is a total
function that is unspecified on `Leaf` (partial in the book's sense);
here that partiality is made explicit with `Option`. -/
def getMin : Tree α → Option α
  | .leaf => none
  | .node _ a _ => some a

theorem toSet_insert (a : α) (t : Tree α) : toSet (insert a t) = {a} ∪ toSet t := by
  simp [insert, set_merge, toSet_node, toSet_leaf]

theorem mset_insert (a : α) (t : Tree α) :
    toMultiset (insert a t) = {a} + toMultiset t := by
  simp [insert, mset_merge, toMultiset_node, toMultiset_leaf]

theorem heap_insert {t : Tree α} (a : α) (h : heap t) : heap (insert a t) :=
  heap_merge (heap_singleton a) h

theorem delMin_leaf : delMin (Tree.leaf : Tree α) = .leaf := rfl

theorem delMin_node (l : Tree α) (a : α) (r : Tree α) :
    delMin (.node l a r) = merge l r := rfl

theorem mset_delMin_node (l : Tree α) (a : α) (r : Tree α) :
    toMultiset (delMin (.node l a r)) = toMultiset l + toMultiset r := by
  simp [delMin_node, mset_merge]

/-- Deleting the minimum removes exactly the root element. -/
theorem mset_delMin_add (l : Tree α) (a : α) (r : Tree α) :
    toMultiset (delMin (.node l a r)) + {a} = toMultiset (.node l a r) := by
  simp [delMin_node, mset_merge, toMultiset_node]; ac_rfl

theorem heap_delMin {t : Tree α} (h : heap t) : heap (delMin t) := by
  cases t with
  | leaf => exact heap_leaf
  | node l a r =>
    have h' := (heap_node).mp h
    rw [delMin_node]
    exact heap_merge h'.1 h'.2.1

theorem getMin_le {t : Tree α} (h : heap t) {m : α} (hm : getMin t = some m) :
    ∀ x ∈ toSet t, m ≤ x := by
  cases t with
  | leaf => simp [getMin] at hm
  | node l a r =>
    have hm' : m = a := by simp [getMin] at hm; exact hm.symm
    subst hm'
    exact heap_all_ge h

omit [LinearOrder α] in
/-- The minimum is itself an element of the tree. -/
theorem getMin_mem {t : Tree α} {m : α} (hm : getMin t = some m) : m ∈ toSet t := by
  cases t with
  | leaf => simp [getMin] at hm
  | node l a r =>
    have hm' : m = a := by simp [getMin] at hm; exact hm.symm
    subst hm'
    simp [toSet_node]

/- ## `merge2`: set and heap properties -/

/-- `set_merge2`: the set version of `mset_merge2` (no Isabelle
counterpart, like `mset_merge2`). -/
theorem set_merge2 (t1 t2 : Tree α) : toSet (merge2 t1 t2) = toSet t1 ∪ toSet t2 := by
  simp [toSet_eq, mset_merge2, msetToSet_add]

/-- `heap_merge2`: `merge2` preserves `heap` (no Isabelle
counterpart; Isabelle's `Skew_Heap.thy` proves only `size_merge2`). -/
theorem heap_merge2 {t1 t2 : Tree α} (h1 : heap t1) (h2 : heap t2) :
    heap (merge2 t1 t2) := by
  induction t1, t2 using merge2.induct with
  | case1 => simp only [merge2]; exact heap_leaf
  | case2 l2 a2 r2 ih =>
    have h2' := (heap_node).mp h2
    have hmerge : heap (merge2 r2 .leaf) := ih h2'.2.1 heap_leaf
    rw [show merge2 (Tree.leaf : Tree α) (.node l2 a2 r2) =
      .node (merge2 r2 .leaf) a2 l2 by simp [merge2]]
    rw [heap_node]
    refine ⟨hmerge, h2'.1, ?_, h2'.2.2.1⟩
    intro x hx
    rw [set_merge2] at hx
    rcases hx with hx | hx
    · exact heap_all_ge h2 x (by simp [toSet_node, hx])
    · simp at hx
  | case3 l1 a1 r1 ih =>
    have h1' := (heap_node).mp h1
    have hmerge : heap (merge2 r1 .leaf) := ih h1'.2.1 heap_leaf
    rw [show merge2 (.node l1 a1 r1) (Tree.leaf : Tree α) =
      .node (merge2 r1 .leaf) a1 l1 by simp [merge2]]
    rw [heap_node]
    refine ⟨hmerge, h1'.1, ?_, h1'.2.2.1⟩
    intro x hx
    rw [set_merge2] at hx
    rcases hx with hx | hx
    · exact heap_all_ge h1 x (by simp [toSet_node, hx])
    · simp at hx
  | case4 l1 a1 r1 l2 a2 r2 h ih =>
    have h1' := (heap_node).mp h1
    have hmerge : heap (merge2 (.node l2 a2 r2) r1) := ih h2 h1'.2.1
    rw [show merge2 (.node l1 a1 r1) (.node l2 a2 r2) =
      .node (merge2 (.node l2 a2 r2) r1) a1 l1 by simp [merge2, h]]
    rw [heap_node]
    refine ⟨hmerge, h1'.1, ?_, h1'.2.2.1⟩
    intro x hx
    rw [set_merge2] at hx
    rcases hx with hx | hx
    · exact le_trans h (heap_all_ge h2 x hx)
    · exact h1'.2.2.2 x hx
  | case5 l1 a1 r1 l2 a2 r2 h ih =>
    have h2' := (heap_node).mp h2
    have hmerge : heap (merge2 (.node l1 a1 r1) r2) := ih h1 h2'.2.1
    rw [show merge2 (.node l1 a1 r1) (.node l2 a2 r2) =
      .node (merge2 (.node l1 a1 r1) r2) a2 l2 by simp [merge2, h]]
    rw [heap_node]
    refine ⟨hmerge, h2'.1, ?_, h2'.2.2.1⟩
    intro x hx
    rw [set_merge2] at hx
    rcases hx with hx | hx
    · exact le_trans (le_of_lt (lt_of_not_ge h)) (heap_all_ge h1 x hx)
    · exact h2'.2.2.2 x hx

/- ## The naive merge (§14.1) -/

/-- The "tempting" merge function from §14.1: same as `merge` but
without swapping the children. Functionally correct (Exercise 14.2),
but it can produce very unbalanced heaps — the motivation for skew
heaps, which swap on every node of the merge path. -/
def naiveMerge : Tree α → Tree α → Tree α
  | .leaf, t => t
  | t, .leaf => t
  | .node l1 a1 r1, .node l2 a2 r2 =>
      if a1 ≤ a2 then .node l1 a1 (naiveMerge r1 (.node l2 a2 r2))
      else .node l2 a2 (naiveMerge (.node l1 a1 r1) r2)
termination_by t1 t2 => size t1 + size t2
decreasing_by (all_goals simp only [size_node]; omega)

theorem naiveMerge_leaf_left (t : Tree α) : naiveMerge .leaf t = t := by simp [naiveMerge]

theorem naiveMerge_leaf_right (t : Tree α) : naiveMerge t .leaf = t := by
  cases t with
  | leaf => simp [naiveMerge]
  | node l a r => simp [naiveMerge]

theorem naiveMerge_node_node (l1 _a1 r1 l2 _a2 r2 : Tree α) (v1 v2 : α) :
    naiveMerge (.node l1 v1 r1) (.node l2 v2 r2) =
      (if v1 ≤ v2 then .node l1 v1 (naiveMerge r1 (.node l2 v2 r2))
       else .node l2 v2 (naiveMerge (.node l1 v1 r1) r2)) := by
  simp [naiveMerge]

/-- `size` of the naive merge (Exercise 14.2). -/
theorem size_naiveMerge (t1 t2 : Tree α) :
    size (naiveMerge t1 t2) = size t1 + size t2 := by
  induction t1, t2 using naiveMerge.induct with
  | case1 t => simp [naiveMerge]
  | case2 t ht => simp [naiveMerge]
  | case3 l1 a1 r1 l2 a2 r2 h ih => simp [naiveMerge, h, ih]; omega
  | case4 l1 a1 r1 l2 a2 r2 h ih => simp [naiveMerge, h, ih]; omega

/-- `mset` of the naive merge (Exercise 14.2). -/
theorem mset_naiveMerge (t1 t2 : Tree α) :
    toMultiset (naiveMerge t1 t2) = toMultiset t1 + toMultiset t2 := by
  induction t1, t2 using naiveMerge.induct with
  | case1 t => simp [naiveMerge]
  | case2 t ht => simp [naiveMerge]
  | case3 l1 a1 r1 l2 a2 r2 h ih => simp [naiveMerge, h, ih]; ac_rfl
  | case4 l1 a1 r1 l2 a2 r2 h ih => simp [naiveMerge, h, ih]; ac_rfl

/-- `set` of the naive merge. -/
theorem set_naiveMerge (t1 t2 : Tree α) :
    toSet (naiveMerge t1 t2) = toSet t1 ∪ toSet t2 := by
  simp [toSet_eq, mset_naiveMerge, msetToSet_add]

/-- `heap` for the naive merge (Exercise 14.2). -/
theorem heap_naiveMerge {t1 t2 : Tree α} (h1 : heap t1) (h2 : heap t2) :
    heap (naiveMerge t1 t2) := by
  induction t1, t2 using naiveMerge.induct with
  | case1 t => simpa [naiveMerge] using h2
  | case2 t ht => simpa [naiveMerge_leaf_right] using h1
  | case3 l1 a1 r1 l2 a2 r2 h ih =>
    have h1' := (heap_node).mp h1
    have hmerge : heap (naiveMerge r1 (.node l2 a2 r2)) := ih h1'.2.1 h2
    rw [show naiveMerge (.node l1 a1 r1) (.node l2 a2 r2) =
      .node l1 a1 (naiveMerge r1 (.node l2 a2 r2)) by simp [naiveMerge, h]]
    rw [heap_node]
    refine ⟨h1'.1, hmerge, h1'.2.2.1, ?_⟩
    intro x hx
    rw [set_naiveMerge] at hx
    rcases hx with hx | hx
    · exact h1'.2.2.2 x hx
    · exact le_trans h (heap_all_ge h2 x hx)
  | case4 l1 a1 r1 l2 a2 r2 h ih =>
    have h2' := (heap_node).mp h2
    have hmerge : heap (naiveMerge (.node l1 a1 r1) r2) := ih h1 h2'.2.1
    rw [show naiveMerge (.node l1 a1 r1) (.node l2 a2 r2) =
      .node l2 a2 (naiveMerge (.node l1 a1 r1) r2) by simp [naiveMerge, h]]
    rw [heap_node]
    refine ⟨h2'.1, hmerge, h2'.2.2.1, ?_⟩
    intro x hx
    rw [set_naiveMerge] at hx
    rcases hx with hx | hx
    · exact le_trans (le_of_lt (lt_of_not_ge h)) (heap_all_ge h1 x hx)
    · exact h2'.2.2.2 x hx


end SkewHeap

end Cslib.Algorithms.Lean
