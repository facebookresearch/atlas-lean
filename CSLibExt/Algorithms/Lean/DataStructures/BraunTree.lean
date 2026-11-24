/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Common
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Braun-tree priority queues

Persistent min-priority queues implemented with Braun trees, following
Nipkow et al., *Functional Data Structures and Algorithms*, Chapter 16,
and the AFP entry `Priority_Queue_Braun` (Paulson's implementation, after
Okasaki). A Braun tree is a binary tree in which, at every node, the left
subtree has the same size as the right subtree or one element more
(`BraunTree.Braun`); `BraunTree.Heap` is the min-heap invariant (every
root is `≤` every element of both subtrees).

Operations: `BraunTree.insert`, `BraunTree.delLeft` (delete the leftmost
element), `BraunTree.siftDown`, `BraunTree.delMin`, `BraunTree.getMin`,
`BraunTree.isEmpty`. Correctness: each operation preserves the multiset
of elements (`BraunTree.msetTree`), the heap invariant, the Braun
invariant, and the size. `BraunTree.pq_spec` discharges the book's
priority-queue ADT.

## Totality and decidability

`delLeft` returns `Option (α × BraunTree α)`: `none` on `Leaf`
(Isabelle leaves it unspecified there). `getMin` returns `Option α`.
`insert` / `siftDown` / the time functions need decidable `<` / `≤`.

`siftDown` is well-founded-recursive on `size l + size r`. Isabelle's
patterns leave the case
`siftDown (Node (Node l₁ x₁ r₁) x₂ r₂) a Leaf` unspecified; this file
totalises it to mirror the `Node`/`Node` case (compare with `x₂` and
recurse into `siftDown (Node l₁ x₁ r₁) a r₂`). The choice is irrelevant
to every proved lemma, because the gap case cannot satisfy `Braun`: it
would require `size l = 0 ∨ size l = 1`, but the gap case has
`size l ≥ 2`. The gap cases are proved by contradiction from `Braun`.

## Cost model

`BraunTree.T_insert`, `BraunTree.T_delLeft`, `BraunTree.T_siftDown` and
`BraunTree.T_delMin` count recursive-call steps (Appendix B.6 of the
book): one per equation of the recursive function, zero for
non-recursive helpers. The bounds (`T_insert_le`, `T_delLeft_le`,
`T_siftDown_le`, `T_delMin_le`, i.e. Lemma 16.1) are in terms of
`height`. Size computations, comparisons, allocation, and all other
overhead are excluded.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean



/-- Binary trees. `Leaf` is the book's `hi`, `Node l x r` is `⟨l; x; r⟩`. -/
inductive BraunTree (α : Type u) where
  | Leaf : BraunTree α
  | Node : BraunTree α → α → BraunTree α → BraunTree α
deriving DecidableEq, Repr

namespace BraunTree

variable {α : Type u} [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α]

/-- Number of nodes: the book's `|t|`. -/
def size : BraunTree α → ℕ
  | .Leaf => 0
  | .Node l _ r => size l + size r + 1

/-- Height: the book's `h t`. -/
def height : BraunTree α → ℕ
  | .Leaf => 0
  | .Node l _ r => max (height l) (height r) + 1

/-- Multiset of elements: the book's `mset_tree`. -/
def msetTree : BraunTree α → Multiset α
  | .Leaf => 0
  | .Node l a r => {a} + msetTree l + msetTree r

/-- Braun invariant: at every node, `|l| = |r|` or `|l| = |r| + 1`,
    and both children are Braun trees. -/
def Braun : BraunTree α → Prop
  | .Leaf => True
  | .Node l _ r => (size l = size r ∨ size l = size r + 1) ∧ Braun l ∧ Braun r

/-- Heap invariant: at every node, the root is `≤` every element of
    both subtrees, and both subtrees are heaps. -/
def Heap : BraunTree α → Prop
  | .Leaf => True
  | .Node l a r =>
      (∀ x ∈ msetTree l, a ≤ x) ∧ (∀ x ∈ msetTree r, a ≤ x) ∧ Heap l ∧ Heap r

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem braun_leaf : Braun (BraunTree.Leaf : BraunTree α) := trivial

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem braun_node {l r : BraunTree α} {a : α} :
    Braun (BraunTree.Node l a r) ↔
      (size l = size r ∨ size l = size r + 1) ∧ Braun l ∧ Braun r :=
  Iff.rfl

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem heap_leaf : Heap (BraunTree.Leaf : BraunTree α) := trivial

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem heap_node {l r : BraunTree α} {a : α} :
    Heap (BraunTree.Node l a r) ↔
      (∀ x ∈ msetTree l, a ≤ x) ∧ (∀ x ∈ msetTree r, a ≤ x) ∧ Heap l ∧ Heap r :=
  Iff.rfl

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem size_eq_zero {t : BraunTree α} : size t = 0 ↔ t = BraunTree.Leaf := by
  cases t with
  | Leaf => simp [size]
  | Node l a r => simp [size]

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem size_pos_of_ne_leaf {t : BraunTree α} (h : t ≠ BraunTree.Leaf) : 0 < size t := by
  cases t with
  | Leaf => exact absurd rfl h
  | Node l a r => simp [size]

/-- The book's `get_min`, made total: `none` on the empty tree. -/
def getMin : BraunTree α → Option α
  | .Leaf => none
  | .Node _ a _ => some a

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem getMin_node (l r : BraunTree α) (a : α) : getMin (BraunTree.Node l a r) = some a := rfl

/-- The book's `set_tree`: the set of elements of a tree. The `Heap`
    definition above uses `msetTree` membership instead of `setTree`
    membership; `mem_setTree` shows the two are exactly equivalent,
    so the two renderings of the heap invariant coincide. -/
def setTree : BraunTree α → Set α
  | .Leaf => ∅
  | .Node l a r => {a} ∪ setTree l ∪ setTree r

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem mem_setTree {t : BraunTree α} {x : α} :
    x ∈ setTree t ↔ x ∈ msetTree t := by
  induction t with
  | Leaf => simp [setTree, msetTree]
  | Node l a r ihl ihr =>
      simp only [setTree, msetTree, Set.mem_union, Set.mem_singleton_iff,
        Multiset.mem_add, Multiset.mem_singleton, ihl, ihr]

/-- Isabelle's `Min_mset`: `Min (set_mset m)`, the minimum of a
    multiset, as an `Option` (`none` for the empty multiset).
    Isabelle's `Min_mset` is unspecified for `m = 0`; the `Option`
    totalisation makes that explicit. -/
def Min_mset (m : Multiset α) : Option α :=
  if h : m.toFinset.Nonempty then some (m.toFinset.min' h) else none

omit [DecidableLT α] [DecidableLE α] in
theorem Min_mset_empty : Min_mset (0 : Multiset α) = none := by
  simp [Min_mset]

omit [DecidableLT α] [DecidableLE α] in
theorem Min_mset_some {m : Multiset α} {a : α} (ha : a ∈ m)
    (hle : ∀ y ∈ m, a ≤ y) : Min_mset m = some a := by
  have hne : m.toFinset.Nonempty := ⟨a, Multiset.mem_toFinset.mpr ha⟩
  unfold Min_mset
  rw [dite_eq_left hne]
  congr 1
  rw [Finset.min'_eq_iff]
  exact ⟨Multiset.mem_toFinset.mpr ha, fun b hb => hle b (Multiset.mem_toFinset.mp hb)⟩

/-- The AFP locale's `is_empty` field (`is_empty = λh. h = Leaf`) has
    no counterpart in the book's Fig. 14.1; it is recorded here for
    completeness of the interpretation. -/
def isEmpty : BraunTree α → Bool
  | .Leaf => true
  | .Node _ _ _ => false

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem isEmpty_leaf : isEmpty (BraunTree.Leaf : BraunTree α) = true := rfl

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem isEmpty_node (l r : BraunTree α) (a : α) :
    isEmpty (BraunTree.Node l a r) = false := rfl

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- `isEmpty` is the emptiness test: it holds exactly when the tree's
    multiset is empty. This is the AFP locale's `is_empty` field
    (`is_empty = λh. h = Leaf`) expressed via `msetTree`. -/
theorem isEmpty_iff_mset_eq_zero (t : BraunTree α) :
    isEmpty t = true ↔ msetTree t = 0 := by
  cases t with
  | Leaf => simp [isEmpty, msetTree]
  | Node l a r => simp [isEmpty, msetTree]

/-- Insertion (§16.1). Inserts into the right (possibly smaller)
    child and swaps children to re-establish the Braun invariant. -/
def insert (a : α) : BraunTree α → BraunTree α
  | .Leaf => BraunTree.Node BraunTree.Leaf a BraunTree.Leaf
  | .Node l x r =>
      if a < x then BraunTree.Node (insert x r) a l else BraunTree.Node (insert a r) x l

/-- `del_left` (§16.1). Returns `none` on `Leaf`; otherwise removes
    and returns the leftmost element together with the remaining tree,
    swapping children along the way. -/
def delLeft : BraunTree α → Option (α × BraunTree α)
  | .Leaf => none
  | .Node .Leaf x r => some (x, r)
  | .Node (.Node l₁ x₁ r₁) x r =>
      match delLeft (.Node l₁ x₁ r₁) with
      | some (y, l') => some (y, BraunTree.Node r x l')
      | none => none

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem delLeft_leaf : delLeft (BraunTree.Leaf : BraunTree α) = none := rfl

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem delLeft_node_leaf (x : α) (r : BraunTree α) :
    delLeft (BraunTree.Node BraunTree.Leaf x r) = some (x, r) := rfl

/-- `sift_down` (§16.1). Well-founded recursion on `size l + size r`
    (the book's tighter measure `max (height l) (height r)` is used
    for the running-time bound in `T_siftDown_le` below). -/
def siftDown : BraunTree α → α → BraunTree α → BraunTree α
  | .Leaf, a, _ => BraunTree.Node BraunTree.Leaf a BraunTree.Leaf
  | .Node .Leaf x _, a, .Leaf =>
      if a ≤ x then BraunTree.Node (BraunTree.Node BraunTree.Leaf x BraunTree.Leaf) a BraunTree.Leaf
      else BraunTree.Node (BraunTree.Node BraunTree.Leaf a BraunTree.Leaf) x BraunTree.Leaf
  | .Node (.Node l₁ x₁ r₁) x₂ r₂, a, .Leaf =>
      if a ≤ x₂ then
        BraunTree.Node (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x₂ r₂) a BraunTree.Leaf
      else
        BraunTree.Node (siftDown (BraunTree.Node l₁ x₁ r₁) a r₂) x₂ BraunTree.Leaf
  | .Node l₁ x₁ r₁, a, .Node l₂ x₂ r₂ =>
      if a ≤ x₁ ∧ a ≤ x₂ then
        BraunTree.Node (BraunTree.Node l₁ x₁ r₁) a (BraunTree.Node l₂ x₂ r₂)
      else if x₁ ≤ x₂ then
        BraunTree.Node (siftDown l₁ a r₁) x₁ (BraunTree.Node l₂ x₂ r₂)
      else
        BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x₂ (siftDown l₂ a r₂)
termination_by l _ r => size l + size r
decreasing_by
  all_goals simp only [size]
  all_goals omega

/-- Deletion of the minimum (§16.1): extract the leftmost element
    with `delLeft` and let it sift down. -/
def delMin : BraunTree α → BraunTree α
  | .Leaf => BraunTree.Leaf
  | .Node .Leaf _ _ => BraunTree.Leaf
  | .Node (.Node l₁ x₁ r₁) _ r =>
      match delLeft (BraunTree.Node l₁ x₁ r₁) with
      | some (y, l') => siftDown r y l'
      | none => BraunTree.Leaf

omit [DecidableLT α] [DecidableEq α] in
theorem delMin_leaf : delMin (BraunTree.Leaf : BraunTree α) = BraunTree.Leaf := rfl

omit [DecidableLT α] [DecidableEq α] in
theorem delMin_node_leaf (x : α) (r : BraunTree α) :
    delMin (BraunTree.Node BraunTree.Leaf x r) = BraunTree.Leaf := rfl

/-! ### Correctness of `insert` — book #1–#4 -/

omit [DecidableLE α] [DecidableEq α] in
theorem size_insert (a : α) (t : BraunTree α) : size (insert a t) = size t + 1 := by
  induction t generalizing a with
  | Leaf => rfl
  | Node l x r ihl ihr =>
      simp only [insert]
      split_ifs with h
      · simp only [size, ihr]; omega
      · simp only [size, ihr]; omega

omit [DecidableLE α] [DecidableEq α] in
theorem mset_insert (a : α) (t : BraunTree α) :
    msetTree (insert a t) = {a} + msetTree t := by
  induction t generalizing a with
  | Leaf => simp [insert, msetTree]
  | Node l x r ihl ihr =>
      simp only [insert]
      split_ifs with h
      · simp only [msetTree, ihr]; ac_rfl
      · simp only [msetTree, ihr]; ac_rfl

omit [DecidableLE α] [DecidableEq α] in
theorem braun_insert {t : BraunTree α} (a : α) (ht : Braun t) : Braun (insert a t) := by
  induction t generalizing a with
  | Leaf => exact ⟨Or.inl rfl, trivial, trivial⟩
  | Node l x r ihl ihr =>
      rw [braun_node] at ht
      obtain ⟨hsize, hbl, hbr⟩ := ht
      simp only [insert]
      split_ifs with h
      · rw [braun_node]
        refine ⟨?_, ihr x hbr, hbl⟩
        rw [size_insert]
        rcases hsize with hs | hs <;> omega
      · rw [braun_node]
        refine ⟨?_, ihr a hbr, hbl⟩
        rw [size_insert]
        rcases hsize with hs | hs <;> omega

omit [DecidableLE α] [DecidableEq α] in
theorem heap_insert {t : BraunTree α} (a : α) (ht : Heap t) : Heap (insert a t) := by
  induction t generalizing a with
  | Leaf =>
      simp only [insert]
      rw [heap_node]
      refine ⟨?_, ?_, trivial, trivial⟩ <;> simp [msetTree]
  | Node l x r ihl ihr =>
      rw [heap_node] at ht
      obtain ⟨hxl, hxr, hhl, hhr⟩ := ht
      simp only [insert]
      split_ifs with h
      · rw [heap_node]
        have h1 : Heap (insert x r) := ihr x hhr
        have hm : ∀ y ∈ msetTree (insert x r), a ≤ y := by
          intro y hy
          rw [mset_insert] at hy
          simp only [Multiset.mem_add, Multiset.mem_singleton] at hy
          rcases hy with rfl | hy
          · exact le_of_lt h
          · exact le_trans (le_of_lt h) (hxr y hy)
        refine ⟨hm, ?_, h1, hhl⟩
        intro y hy
        exact le_trans (le_of_lt h) (hxl y hy)
      · rw [heap_node]
        have h1 : Heap (insert a r) := ihr a hhr
        have hxa : x ≤ a := le_of_not_gt h
        have hm : ∀ y ∈ msetTree (insert a r), x ≤ y := by
          intro y hy
          rw [mset_insert] at hy
          simp only [Multiset.mem_add, Multiset.mem_singleton] at hy
          rcases hy with rfl | hy
          · exact hxa
          · exact hxr y hy
        exact ⟨hm, hxl, h1, hhl⟩


/-! ### Correctness of `delLeft` — book #5–#8, plus #19 (16.5) -/

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- `delLeft` is defined on every non-empty tree. -/
theorem delLeft_some_of_ne_leaf {t : BraunTree α} (ht : t ≠ BraunTree.Leaf) :
    ∃ x t', delLeft t = some (x, t') := by
  induction t with
  | Leaf => exact absurd rfl ht
  | Node l c r ih =>
      cases l with
      | Leaf => exact ⟨c, r, rfl⟩
      | Node l₁ x₁ r₁ =>
          obtain ⟨y, l', hdl⟩ := ih (by simp)
          exact ⟨y, BraunTree.Node r c l', by simp [delLeft, hdl]⟩

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- Combined specification of `delLeft`: multiset, size, heap and
    Braun preservation, and the height bound (16.5). The individual
    book lemmas #5–#8 and #19 are corollaries below. -/
theorem delLeft_spec {t : BraunTree α} {x : α} {t' : BraunTree α}
    (h : delLeft t = some (x, t')) :
    msetTree t = {x} + msetTree t' ∧ size t = size t' + 1 ∧
    (Heap t → Heap t') ∧ (Braun t → Braun t') ∧ height t' ≤ height t := by
  induction t generalizing x t' with
  | Leaf => simp [delLeft] at h
  | Node l c r ih =>
      cases l with
      | Leaf =>
          simp only [delLeft] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simp [msetTree]
          · simp [size]
          · intro hh; rw [heap_node] at hh; exact hh.2.2.2
          · intro hb; rw [braun_node] at hb; exact hb.2.2
          · simp [height]
      | Node l₁ x₁ r₁ =>
          cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
          | none => simp [delLeft, hdl] at h
          | some p =>
              obtain ⟨y, l'⟩ := p
              have hdl' : delLeft (BraunTree.Node l₁ x₁ r₁) = some (y, l') := hdl
              have ihspec := ih hdl'
              obtain ⟨ihmset, ihsize, ihheap, ihbraun, ihheight⟩ := ihspec
              simp only [delLeft, hdl] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · have h1 : msetTree (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                    = {c} + msetTree (BraunTree.Node l₁ x₁ r₁) + msetTree r := rfl
                have h2 : msetTree (BraunTree.Node r c l') = {c} + msetTree r + msetTree l' := rfl
                rw [h1, ihmset, h2]
                ac_rfl
              · have h1 : size (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                    = size (BraunTree.Node l₁ x₁ r₁) + size r + 1 := rfl
                have h2 : size (BraunTree.Node r c l') = size r + size l' + 1 := rfl
                omega
              · intro hh
                rw [heap_node] at hh
                obtain ⟨hcl, hcr, hhl, hhr⟩ := hh
                have hhl' : Heap (BraunTree.Node l₁ x₁ r₁) := hhl
                rw [heap_node] at hhl'
                obtain ⟨_, _, hhl1, hhr1⟩ := hhl'
                have hl'heap : Heap l' := ihheap hhl
                rw [heap_node]
                refine ⟨hcr, ?_, hhr, hl'heap⟩
                intro z hz
                have hz_in : z ∈ msetTree (BraunTree.Node l₁ x₁ r₁) := by
                  rw [ihmset]
                  exact (Multiset.mem_add).mpr (Or.inr hz)
                exact hcl z hz_in
              · intro hb
                rw [braun_node] at hb
                obtain ⟨hsize, hbl, hbr⟩ := hb
                have hbl' : Braun (BraunTree.Node l₁ x₁ r₁) := hbl
                rw [braun_node] at hbl'
                obtain ⟨hsize1, hb1, hbr1⟩ := hbl'
                have hl'braun : Braun l' := ihbraun hbl
                rw [braun_node]
                refine ⟨?_, hbr, hl'braun⟩
                -- size r = size l' ∨ size r = size l' + 1, from
                -- size (Node l₁..) = size r ∨ = size r + 1 and size l' + 1 = size (Node l₁..)
                have hsz : size (BraunTree.Node l₁ x₁ r₁) = size l' + 1 := by
                  rw [ihsize]
                simp only [size] at hsize hsz
                omega
              · have h1 : height (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                    = max (height (BraunTree.Node l₁ x₁ r₁)) (height r) + 1 := rfl
                have h2 : height (BraunTree.Node r c l')
                    = max (height r) (height l') + 1 := rfl
                omega

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- Book #5. AFP lemma `del_left_mset_plus` (the plus form). -/
theorem delLeft_mset {t : BraunTree α} {x : α} {t' : BraunTree α}
    (h : delLeft t = some (x, t')) : msetTree t = {x} + msetTree t' :=
  (delLeft_spec h).1

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- Book #7 = (16.1). -/
theorem delLeft_size {t : BraunTree α} {x : α} {t' : BraunTree α}
    (h : delLeft t = some (x, t')) : size t = size t' + 1 :=
  (delLeft_spec h).2.1

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- Book #6. -/
theorem delLeft_heap {t : BraunTree α} {x : α} {t' : BraunTree α}
    (h : delLeft t = some (x, t')) (ht : Heap t) : Heap t' :=
  (delLeft_spec h).2.2.1 ht

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- Book #8 = (16.2). -/
theorem delLeft_braun {t : BraunTree α} {x : α} {t' : BraunTree α}
    (h : delLeft t = some (x, t')) (ht : Braun t) : Braun t' :=
  (delLeft_spec h).2.2.2.1 ht

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- Book #19 = (16.5). -/
theorem delLeft_height {t : BraunTree α} {x : α} {t' : BraunTree α}
    (h : delLeft t = some (x, t')) : height t' ≤ height t :=
  (delLeft_spec h).2.2.2.2

omit [DecidableLT α] [DecidableLE α] in
/-- AFP lemma `del_left_mset`, in its minus form: the removed element
    is in the tree, and the remaining tree's multiset is the tree's
    multiset minus that element. (The book states the equivalent plus
    form `delLeft_mset`; the `t ≠ Leaf` hypothesis in the AFP statement
    is redundant here, since `delLeft t = some …` already implies it.) -/
theorem delLeft_mset_sub {t : BraunTree α} {x : α} {t' : BraunTree α}
    (h : delLeft t = some (x, t')) :
    x ∈ msetTree t ∧ msetTree t' = msetTree t - {x} := by
  constructor
  · rw [delLeft_mset h]
    exact (Multiset.mem_add).mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
  · rw [delLeft_mset h, add_tsub_cancel_left]

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `del_left_set`. -/
theorem delLeft_set {t : BraunTree α} {x : α} {t' : BraunTree α}
    (h : delLeft t = some (x, t')) :
    setTree t = ({x} : Set α) ∪ setTree t' := by
  ext y
  rw [mem_setTree, delLeft_mset h]
  simp [mem_setTree]

omit [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `set_insert`. -/
theorem set_insert (a : α) (t : BraunTree α) :
    setTree (insert a t) = ({a} : Set α) ∪ setTree t := by
  ext y
  rw [mem_setTree, mset_insert]
  simp [mem_setTree]



/-! ### Helper: the root of a heap is `≤` every element of the tree -/

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
theorem heap_root_le {l r : BraunTree α} {a : α} (h : Heap (BraunTree.Node l a r)) :
    ∀ y ∈ msetTree (BraunTree.Node l a r), a ≤ y := by
  rw [heap_node] at h
  obtain ⟨h1, h2, _, _⟩ := h
  intro y hy
  simp only [msetTree, Multiset.mem_add, Multiset.mem_singleton] at hy
  rcases hy with (rfl | hy) | hy
  · exact le_refl _
  · exact h1 y hy
  · exact h2 y hy
omit [DecidableLT α] [DecidableLE α] in
/-- AFP lemma `get_min`: on a non-empty heap, `getMin` is the minimum
    of the multiset of elements. -/
theorem getMin_eq_Min_mset {t : BraunTree α} (ht : Heap t) (hne : t ≠ BraunTree.Leaf) :
    getMin t = Min_mset (msetTree t) := by
  cases t with
  | Leaf => exact absurd rfl hne
  | Node l a r =>
      have ha : a ∈ msetTree (BraunTree.Node l a r) := by simp [msetTree]
      have hle : ∀ y ∈ msetTree (BraunTree.Node l a r), a ≤ y := heap_root_le ht
      exact (Min_mset_some ha hle).symm


/-! ### Correctness of `siftDown` — book #9–#12 -/

omit [DecidableLT α] [DecidableEq α] in
/-- Combined specification of `siftDown`. The individual book lemmas
    #9–#12 are corollaries below. -/
theorem siftDown_spec {l : BraunTree α} {a : α} {r : BraunTree α}
    (hbraun : Braun (BraunTree.Node l a r)) :
    size (siftDown l a r) = size l + size r + 1 ∧
    Braun (siftDown l a r) ∧
    msetTree (siftDown l a r) = {a} + (msetTree l + msetTree r) ∧
    (Heap l → Heap r → Heap (siftDown l a r)) := by
  induction l, a, r using siftDown.induct with
  | case1 a x =>
      rw [braun_node] at hbraun
      have hsize0 : size x = 0 := by
        have hb := hbraun.1
        simp only [size] at hb
        omega
      have hx : x = BraunTree.Leaf := by
        cases x with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst hx
      have hsd : siftDown (BraunTree.Leaf : BraunTree α) a BraunTree.Leaf
          = BraunTree.Node BraunTree.Leaf a BraunTree.Leaf := by simp [siftDown]
      rw [hsd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [size]
      · rw [braun_node]; exact ⟨Or.inl rfl, trivial, trivial⟩
      · simp [msetTree]
      · intro _ _
        rw [heap_node]
        refine ⟨?_, ?_, trivial, trivial⟩ <;> intro y hy <;> simp [msetTree] at hy
  | case2 x a a1 hle =>
      rw [braun_node] at hbraun
      have hsize0 : size a = 0 := by
        have hb := hbraun.1
        simp only [size] at hb
        omega
      have ha : a = BraunTree.Leaf := by
        cases a with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst ha
      have hsd : siftDown (BraunTree.Node BraunTree.Leaf x BraunTree.Leaf) a1 BraunTree.Leaf
          = BraunTree.Node (BraunTree.Node BraunTree.Leaf x BraunTree.Leaf) a1 BraunTree.Leaf := by
        simp [siftDown, hle]
      rw [hsd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [size]
      · rw [braun_node]
        refine ⟨Or.inr rfl, ?_, trivial⟩
        rw [braun_node]; exact ⟨Or.inl rfl, trivial, trivial⟩
      · have m1 : msetTree (BraunTree.Node (BraunTree.Node BraunTree.Leaf x BraunTree.Leaf)
              a1 BraunTree.Leaf)
            = {a1} + msetTree (BraunTree.Node BraunTree.Leaf x BraunTree.Leaf)
              + msetTree BraunTree.Leaf := rfl
        have m2 : msetTree (BraunTree.Node BraunTree.Leaf x BraunTree.Leaf)
            = {x} + msetTree BraunTree.Leaf + msetTree BraunTree.Leaf := rfl
        rw [m1, m2]; ac_rfl
      · intro hl _
        rw [heap_node]
        refine ⟨?_, ?_, hl, trivial⟩
        · intro y hy
          have hyx : y = x := by simpa [msetTree] using hy
          subst hyx; exact hle
        · intro y hy; simp [msetTree] at hy
  | case3 x a a1 hle =>
      rw [braun_node] at hbraun
      have hsize0 : size a = 0 := by
        have hb := hbraun.1
        simp only [size] at hb
        omega
      have ha : a = BraunTree.Leaf := by
        cases a with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst ha
      have hxa : x ≤ a1 := le_of_lt (lt_of_not_ge hle)
      have hsd : siftDown (BraunTree.Node BraunTree.Leaf x BraunTree.Leaf) a1 BraunTree.Leaf
          = BraunTree.Node (BraunTree.Node BraunTree.Leaf a1 BraunTree.Leaf) x BraunTree.Leaf := by
        simp [siftDown, hle]
      rw [hsd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [size]
      · rw [braun_node]
        refine ⟨Or.inr rfl, ?_, trivial⟩
        rw [braun_node]; exact ⟨Or.inl rfl, trivial, trivial⟩
      · have m1 : msetTree (BraunTree.Node (BraunTree.Node BraunTree.Leaf a1 BraunTree.Leaf)
              x BraunTree.Leaf)
            = {x} + msetTree (BraunTree.Node BraunTree.Leaf a1 BraunTree.Leaf)
              + msetTree BraunTree.Leaf := rfl
        have m2 : msetTree (BraunTree.Node BraunTree.Leaf a1 BraunTree.Leaf)
            = {a1} + msetTree BraunTree.Leaf + msetTree BraunTree.Leaf := rfl
        have m3 : msetTree (BraunTree.Node BraunTree.Leaf x BraunTree.Leaf)
            = {x} + msetTree BraunTree.Leaf + msetTree BraunTree.Leaf := rfl
        rw [m1, m2, m3]; ac_rfl
      · intro _ _
        rw [heap_node]
        refine ⟨?_, ?_, ?_, trivial⟩
        · intro y hy
          have hya : y = a1 := by simpa [msetTree] using hy
          subst hya; exact hxa
        · intro y hy; simp [msetTree] at hy
        · rw [heap_node]
          refine ⟨?_, ?_, trivial, trivial⟩ <;> intro y hy <;> simp [msetTree] at hy
  | case4 l₁ x₁ r₁ x₂ r₂ a hle =>
      rw [braun_node] at hbraun
      exfalso
      have hb := hbraun.1
      simp only [size] at hb
      omega
  | case5 l₁ x₁ r₁ x₂ r₂ a hle ih =>
      rw [braun_node] at hbraun
      exfalso
      have hb := hbraun.1
      simp only [size] at hb
      omega
  | case6 l₁ x₁ r₁ a l₂ x₂ r₂ hle =>
      obtain ⟨hsize, hbl, hbr⟩ := hbraun
      have hsd : siftDown (BraunTree.Node l₁ x₁ r₁) a (BraunTree.Node l₂ x₂ r₂)
          = BraunTree.Node (BraunTree.Node l₁ x₁ r₁) a (BraunTree.Node l₂ x₂ r₂) := by
        simp [siftDown, hle]
      rw [hsd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rfl
      · rw [braun_node]; exact ⟨hsize, hbl, hbr⟩
      · have h1 : msetTree (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) a (BraunTree.Node l₂ x₂ r₂))
            = {a} + msetTree (BraunTree.Node l₁ x₁ r₁) + msetTree (BraunTree.Node l₂ x₂ r₂) := rfl
        rw [h1, add_assoc]
      · intro hl hr
        rw [heap_node]
        have bound_l : ∀ y ∈ msetTree (BraunTree.Node l₁ x₁ r₁), a ≤ y := by
          intro y hy
          exact le_trans hle.1 (heap_root_le hl y hy)
        have bound_r : ∀ y ∈ msetTree (BraunTree.Node l₂ x₂ r₂), a ≤ y := by
          intro y hy
          exact le_trans hle.2 (heap_root_le hr y hy)
        exact ⟨bound_l, bound_r, hl, hr⟩
  | case7 l₁ x₁ r₁ a l₂ x₂ r₂ hle h12 ih =>
      obtain ⟨hsize, hbl, hbr⟩ := hbraun
      have hb1 : Braun (BraunTree.Node l₁ a r₁) := by
        rw [braun_node] at hbl
        rw [braun_node]
        exact ⟨hbl.1, hbl.2.1, hbl.2.2⟩
      obtain ⟨ihsize, ihbraun, ihmset, ihheap⟩ := ih hb1
      have hsd : siftDown (BraunTree.Node l₁ x₁ r₁) a (BraunTree.Node l₂ x₂ r₂)
          = BraunTree.Node (siftDown l₁ a r₁) x₁ (BraunTree.Node l₂ x₂ r₂) := by
        simp [siftDown, hle, h12]
      rw [hsd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h1 : size (BraunTree.Node (siftDown l₁ a r₁) x₁ (BraunTree.Node l₂ x₂ r₂))
            = size (siftDown l₁ a r₁) + size (BraunTree.Node l₂ x₂ r₂) + 1 := rfl
        have h2 : size (BraunTree.Node l₁ x₁ r₁) = size l₁ + size r₁ + 1 := rfl
        have h3 : size (BraunTree.Node l₂ x₂ r₂) = size l₂ + size r₂ + 1 := rfl
        rcases hsize with hs | hs <;> omega
      · rw [braun_node]
        refine ⟨?_, ihbraun, hbr⟩
        have h1 : size (siftDown l₁ a r₁) = size l₁ + size r₁ + 1 := ihsize
        have h2 : size (BraunTree.Node l₂ x₂ r₂) = size l₂ + size r₂ + 1 := rfl
        have h3 : size (BraunTree.Node l₁ x₁ r₁) = size l₁ + size r₁ + 1 := rfl
        rcases hsize with hs | hs <;> omega
      · have m1 : msetTree (BraunTree.Node (siftDown l₁ a r₁) x₁ (BraunTree.Node l₂ x₂ r₂))
            = {x₁} + msetTree (siftDown l₁ a r₁) + msetTree (BraunTree.Node l₂ x₂ r₂) := rfl
        have m2 : msetTree (BraunTree.Node l₁ x₁ r₁) = {x₁} + msetTree l₁ + msetTree r₁ := rfl
        have m3 : msetTree (BraunTree.Node l₂ x₂ r₂) = {x₂} + msetTree l₂ + msetTree r₂ := rfl
        rw [m1, ihmset, m2, m3]
        ac_rfl
      · intro hl hr
        have hl' := hl; rw [heap_node] at hl'
        obtain ⟨hl1, hl2, hhl1, hhr1⟩ := hl'
        have hsift_heap : Heap (siftDown l₁ a r₁) := ihheap hhl1 hhr1
        have hxa : x₁ ≤ a := le_of_not_gt (fun h => hle ⟨le_of_lt h, le_trans (le_of_lt h) h12⟩)
        rw [heap_node]
        refine ⟨?_, ?_, hsift_heap, hr⟩
        · intro y hy
          rw [ihmset] at hy
          simp only [Multiset.mem_add, Multiset.mem_singleton] at hy
          rcases hy with rfl | (hy | hy)
          · exact hxa
          · exact hl1 y hy
          · exact hl2 y hy
        · intro y hy
          exact le_trans h12 (heap_root_le hr y hy)
  | case8 l₁ x₁ r₁ a l₂ x₂ r₂ hle h12 ih =>
      obtain ⟨hsize, hbl, hbr⟩ := hbraun
      have hb2 : Braun (BraunTree.Node l₂ a r₂) := by
        rw [braun_node] at hbr
        rw [braun_node]
        exact ⟨hbr.1, hbr.2.1, hbr.2.2⟩
      obtain ⟨ihsize, ihbraun, ihmset, ihheap⟩ := ih hb2
      have hsd : siftDown (BraunTree.Node l₁ x₁ r₁) a (BraunTree.Node l₂ x₂ r₂)
          = BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x₂ (siftDown l₂ a r₂) := by
        simp [siftDown, hle, h12]
      rw [hsd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h1 : size (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x₂ (siftDown l₂ a r₂))
            = size (BraunTree.Node l₁ x₁ r₁) + size (siftDown l₂ a r₂) + 1 := rfl
        have h2 : size (BraunTree.Node l₁ x₁ r₁) = size l₁ + size r₁ + 1 := rfl
        have h3 : size (BraunTree.Node l₂ x₂ r₂) = size l₂ + size r₂ + 1 := rfl
        rcases hsize with hs | hs <;> omega
      · rw [braun_node]
        refine ⟨?_, hbl, ihbraun⟩
        have h1 : size (siftDown l₂ a r₂) = size l₂ + size r₂ + 1 := ihsize
        have h2 : size (BraunTree.Node l₁ x₁ r₁) = size l₁ + size r₁ + 1 := rfl
        have h3 : size (BraunTree.Node l₂ x₂ r₂) = size l₂ + size r₂ + 1 := rfl
        rcases hsize with hs | hs <;> omega
      · have m1 : msetTree (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x₂ (siftDown l₂ a r₂))
            = {x₂} + msetTree (BraunTree.Node l₁ x₁ r₁) + msetTree (siftDown l₂ a r₂) := rfl
        have m2 : msetTree (BraunTree.Node l₁ x₁ r₁) = {x₁} + msetTree l₁ + msetTree r₁ := rfl
        have m3 : msetTree (BraunTree.Node l₂ x₂ r₂) = {x₂} + msetTree l₂ + msetTree r₂ := rfl
        rw [m1, ihmset, m2, m3]
        ac_rfl
      · intro hl hr
        have hr' := hr; rw [heap_node] at hr'
        obtain ⟨hr1, hr2, hhr1, hhr2⟩ := hr'
        have hsift_heap : Heap (siftDown l₂ a r₂) := ihheap hhr1 hhr2
        have hx21 : x₂ ≤ x₁ := le_of_not_ge h12
        have hx2a : x₂ ≤ a :=
          le_of_not_gt (fun h => hle ⟨le_trans (le_of_lt h) hx21, le_of_lt h⟩)
        rw [heap_node]
        refine ⟨?_, ?_, hl, hsift_heap⟩
        · intro y hy
          exact le_trans hx21 (heap_root_le hl y hy)
        · intro y hy
          rw [ihmset] at hy
          simp only [Multiset.mem_add, Multiset.mem_singleton] at hy
          rcases hy with rfl | (hy | hy)
          · exact hx2a
          · exact hr1 y hy
          · exact hr2 y hy



omit [DecidableLT α] [DecidableEq α] in
/-- Book #9. -/
theorem size_siftDown {l : BraunTree α} {a : α} {r : BraunTree α}
    (h : Braun (BraunTree.Node l a r)) :
    size (siftDown l a r) = size l + size r + 1 :=
  (siftDown_spec h).1

omit [DecidableLT α] [DecidableEq α] in
/-- Book #10. -/
theorem braun_siftDown {l : BraunTree α} {a : α} {r : BraunTree α}
    (h : Braun (BraunTree.Node l a r)) : Braun (siftDown l a r) :=
  (siftDown_spec h).2.1

omit [DecidableLT α] [DecidableEq α] in
/-- Book #11. -/
theorem mset_siftDown {l : BraunTree α} {a : α} {r : BraunTree α}
    (h : Braun (BraunTree.Node l a r)) :
    msetTree (siftDown l a r) = {a} + (msetTree l + msetTree r) :=
  (siftDown_spec h).2.2.1

omit [DecidableLT α] [DecidableEq α] in
/-- Book #12. -/
theorem heap_siftDown {l : BraunTree α} {a : α} {r : BraunTree α}
    (h : Braun (BraunTree.Node l a r)) (hl : Heap l) (hr : Heap r) :
    Heap (siftDown l a r) :=
  (siftDown_spec h).2.2.2 hl hr

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `set_sift_down`. -/
theorem set_siftDown {l : BraunTree α} {a : α} {r : BraunTree α}
    (h : Braun (BraunTree.Node l a r)) :
    setTree (siftDown l a r) = ({a} : Set α) ∪ (setTree l ∪ setTree r) := by
  ext y
  rw [mem_setTree, mset_siftDown h]
  simp [mem_setTree]

/-! ### Correctness of `delMin` — book #13–#15 -/

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- The tree rebuilt by `delMin` from a Braun tree is again Braun:
    used for both `delMin` correctness and `T_delMin`. -/
theorem braun_siftDown_arg {l : BraunTree α} {c : α} {r : BraunTree α} {y : α} {l' : BraunTree α}
    (hbraun : Braun (BraunTree.Node l c r)) (hdl : delLeft l = some (y, l')) :
    Braun (BraunTree.Node r y l') := by
  cases l with
  | Leaf => simp [delLeft] at hdl
  | Node l₁ x₁ r₁ =>
      obtain ⟨hsize, hbl, hbr⟩ := hbraun
      have hl' : Braun l' := delLeft_braun hdl hbl
      rw [braun_node]
      refine ⟨?_, hbr, hl'⟩
      have hsz : size (BraunTree.Node l₁ x₁ r₁) = size l' + 1 := delLeft_size hdl
      rcases hsize with hs | hs <;> omega

omit [DecidableLT α] [DecidableEq α] in
/-- Book #13. -/
theorem braun_delMin {t : BraunTree α} (ht : Braun t) : Braun (delMin t) := by
  cases t with
  | Leaf => exact trivial
  | Node l c r =>
      cases l with
      | Leaf => exact trivial
      | Node l₁ x₁ r₁ =>
          cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
          | none =>
              have hsd : delMin (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                  = BraunTree.Leaf := by
                simp [delMin, hdl]
              rw [hsd]; exact trivial
          | some p =>
              obtain ⟨y, l'⟩ := p
              have hdl' : delLeft (BraunTree.Node l₁ x₁ r₁) = some (y, l') := hdl
              have hs : Braun (BraunTree.Node r y l') := braun_siftDown_arg ht hdl'
              have hsd : delMin (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                  = siftDown r y l' := by simp [delMin, hdl]
              rw [hsd]
              exact braun_siftDown hs

omit [DecidableLT α] [DecidableEq α] in
/-- Book #14. -/
theorem heap_delMin {t : BraunTree α} (hheap : Heap t) (hbraun : Braun t) :
    Heap (delMin t) := by
  cases t with
  | Leaf => exact trivial
  | Node l c r =>
      cases l with
      | Leaf => exact trivial
      | Node l₁ x₁ r₁ =>
          cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
          | none =>
              have hsd : delMin (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                  = BraunTree.Leaf := by
                simp [delMin, hdl]
              rw [hsd]; exact trivial
          | some p =>
              obtain ⟨y, l'⟩ := p
              have hdl' : delLeft (BraunTree.Node l₁ x₁ r₁) = some (y, l') := hdl
              have hs : Braun (BraunTree.Node r y l') := braun_siftDown_arg hbraun hdl'
              have hsd : delMin (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                  = siftDown r y l' := by simp [delMin, hdl]
              rw [hsd]
              rw [heap_node] at hheap
              obtain ⟨_, _, hhl, hhr⟩ := hheap
              have hl' : Heap l' := delLeft_heap hdl' hhl
              exact heap_siftDown hs hhr hl'

omit [DecidableLT α] in
/-- Book #15, in the form used by the AFP (`get_min` is the root of
    the non-empty tree). -/
theorem mset_delMin {t : BraunTree α} (hbraun : Braun t) (ht : t ≠ BraunTree.Leaf) :
    ∀ l a r, t = BraunTree.Node l a r →
      msetTree (delMin t) = msetTree t - {a} := by
  intro l a r hteq
  subst hteq
  cases l with
  | Leaf =>
      obtain ⟨hsize, _, _⟩ := hbraun
      have hr0 : size r = 0 := by
        simp only [size] at hsize
        rcases hsize with hs | hs <;> omega
      have hr : r = BraunTree.Leaf := by
        cases r with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hr0
      subst hr
      rw [delMin_node_leaf]
      simp [msetTree]
  | Node l₁ x₁ r₁ =>
      cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
      | none =>
          obtain ⟨y, l', hdl'⟩ := delLeft_some_of_ne_leaf
            (show (BraunTree.Node l₁ x₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
          rw [hdl'] at hdl; contradiction
      | some p =>
          obtain ⟨y, l'⟩ := p
          have hdl' : delLeft (BraunTree.Node l₁ x₁ r₁) = some (y, l') := hdl
          have hs : Braun (BraunTree.Node r y l') := braun_siftDown_arg hbraun hdl'
          have hsd : delMin (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) a r)
              = siftDown r y l' := by simp [delMin, hdl]
          rw [hsd, mset_siftDown hs]
          have hdelm : msetTree (BraunTree.Node l₁ x₁ r₁) = {y} + msetTree l' :=
            delLeft_mset hdl'
          have h1 : msetTree (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) a r)
              = {a} + msetTree (BraunTree.Node l₁ x₁ r₁) + msetTree r := rfl
          rw [h1, hdelm]
          rw [show ({a} + ({y} + msetTree l') + msetTree r)
              = {a} + (({y} + msetTree l') + msetTree r) from by ac_rfl]
          rw [add_tsub_cancel_left]
          ac_rfl

omit [DecidableLT α] in
/-- Book #15 with `getMin`: the deleted element is `getMin t`. -/
theorem mset_delMin_getMin {t : BraunTree α} (hbraun : Braun t) (ht : t ≠ BraunTree.Leaf) :
    ∃ a, getMin t = some a ∧ msetTree (delMin t) = msetTree t - {a} := by
  cases t with
  | Leaf => exact absurd rfl ht
  | Node l a r =>
      exact ⟨a, rfl, mset_delMin hbraun ht l a r rfl⟩

omit [DecidableLT α] [DecidableEq α] in
/-- Not a book statement (AFP extra): `delMin` removes exactly one element. -/
theorem size_delMin {t : BraunTree α} (hbraun : Braun t) :
    size (delMin t) = size t - 1 := by
  cases t with
  | Leaf => rfl
  | Node l c r =>
      cases l with
      | Leaf =>
          obtain ⟨hsize, _, _⟩ := hbraun
          have hr0 : size r = 0 := by
            simp only [size] at hsize
            rcases hsize with hs | hs <;> omega
          have hr : r = BraunTree.Leaf := by
            cases r with
            | Leaf => rfl
            | Node l' y r' => simp [size] at hr0
          subst hr
          rfl
      | Node l₁ x₁ r₁ =>
          cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
          | none =>
              obtain ⟨y, l', hdl'⟩ := delLeft_some_of_ne_leaf
                (show (BraunTree.Node l₁ x₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
              rw [hdl'] at hdl; contradiction
          | some p =>
              obtain ⟨y, l'⟩ := p
              have hdl' : delLeft (BraunTree.Node l₁ x₁ r₁) = some (y, l') := hdl
              have hs : Braun (BraunTree.Node r y l') := braun_siftDown_arg hbraun hdl'
              have hsd : delMin (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                  = siftDown r y l' := by simp [delMin, hdl]
              rw [hsd, size_siftDown hs]
              have h1 : size (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                  = size (BraunTree.Node l₁ x₁ r₁) + size r + 1 := rfl
              have hsz : size (BraunTree.Node l₁ x₁ r₁) = size l' + 1 := delLeft_size hdl'
              omega



/-! ### Running-time functions — Appendix B.6, book #16–#20 -/

/-- Step-counting version of `insert` (Appendix B.6). -/
def T_insert (a : α) : BraunTree α → ℕ
  | .Leaf => 1
  | .Node _ x r => (if a < x then T_insert x r else T_insert a r) + 1

/-- Step-counting version of `delLeft` (Appendix B.6). -/
def T_delLeft : BraunTree α → ℕ
  | .Leaf => 0
  | .Node .Leaf _ _ => 1
  | .Node (.Node l₁ x₁ r₁) _ _ => T_delLeft (BraunTree.Node l₁ x₁ r₁) + 1

/-- Step-counting version of `siftDown` (Appendix B.6, with the same
    totalisation case as `siftDown`). -/
def T_siftDown : BraunTree α → α → BraunTree α → ℕ
  | .Leaf, _, _ => 1
  | .Node .Leaf _ _, _, .Leaf => 1
  | .Node (.Node l₁ x₁ r₁) x₂ r₂, a, .Leaf =>
      if a ≤ x₂ then 1 else T_siftDown (BraunTree.Node l₁ x₁ r₁) a r₂ + 1
  | .Node l₁ x₁ r₁, a, .Node l₂ x₂ r₂ =>
      if a ≤ x₁ ∧ a ≤ x₂ then 1
      else if x₁ ≤ x₂ then T_siftDown l₁ a r₁ + 1
      else T_siftDown l₂ a r₂ + 1
termination_by l _ r => size l + size r
decreasing_by
  all_goals simp only [size]
  all_goals omega

/-- Step-counting version of `delMin` (Appendix B.6). -/
def T_delMin : BraunTree α → ℕ
  | .Leaf => 0
  | .Node .Leaf _ _ => 0
  | .Node (.Node l₁ x₁ r₁) _ r =>
      T_delLeft (BraunTree.Node l₁ x₁ r₁) +
        (match delLeft (BraunTree.Node l₁ x₁ r₁) with
         | some (y, l') => T_siftDown r y l'
         | none => 0)

omit [DecidableLT α] [DecidableEq α] in
omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `T_del_min_neq_Leaf`: the defining equation of
    `T_delMin` on a non-empty left subtree. (For `l = Leaf`,
    `T_delMin (Node Leaf x r) = 0` by definition.) -/
theorem T_delMin_eq {l : BraunTree α} {x : α} {r : BraunTree α} (hl : l ≠ BraunTree.Leaf) :
    T_delMin (BraunTree.Node l x r) = T_delLeft l +
      (match delLeft l with
       | some (y, l') => T_siftDown r y l'
       | none => 0) := by
  cases l with
  | Leaf => exact absurd rfl hl
  | Node l₁ x₁ r₁ => rfl

omit [DecidableLE α] [DecidableEq α] in
omit [DecidableLE α] [DecidableEq α] in
/-- Book #16. -/
theorem T_insert_le (a : α) (t : BraunTree α) : T_insert a t ≤ height t + 1 := by
  induction t generalizing a with
  | Leaf => rfl
  | Node l x r ihl ihr =>
      simp only [T_insert, height]
      split_ifs with h
      · have h1 : T_insert x r ≤ height r + 1 := ihr x
        omega
      · have h1 : T_insert a r ≤ height r + 1 := ihr a
        omega

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- Book #17 = (16.3). -/
theorem T_delLeft_le {t : BraunTree α} (ht : t ≠ BraunTree.Leaf) :
    T_delLeft t ≤ height t := by
  induction t with
  | Leaf => exact absurd rfl ht
  | Node l c r ih =>
      cases l with
      | Leaf => simp [T_delLeft, height]
      | Node l₁ x₁ r₁ =>
          have h1 : T_delLeft (BraunTree.Node l₁ x₁ r₁)
              ≤ height (BraunTree.Node l₁ x₁ r₁) :=
            ih (by simp)
          have hT : T_delLeft (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
              = T_delLeft (BraunTree.Node l₁ x₁ r₁) + 1 := rfl
          have hH : height (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
              = max (height (BraunTree.Node l₁ x₁ r₁)) (height r) + 1 := rfl
          rw [hT, hH]
          exact le_trans (Nat.add_le_add_right h1 1)
            (Nat.add_le_add_right (le_max_left _ _) 1)

omit [DecidableLT α] [DecidableEq α] in
/-- Book #18 = (16.4). -/
theorem T_siftDown_le {l : BraunTree α} {a : α} {r : BraunTree α}
    (hbraun : Braun (BraunTree.Node l a r)) :
    T_siftDown l a r ≤ max (height l) (height r) + 1 := by
  induction l, a, r using T_siftDown.induct with
  | case1 a x =>
      rw [braun_node] at hbraun
      have hsize0 : size x = 0 := by
        have hb := hbraun.1
        simp only [size] at hb
        omega
      have hx : x = BraunTree.Leaf := by
        cases x with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst hx
      simp [T_siftDown, height]
  | case2 x a a1 =>
      -- `l = Node Leaf x a`, `r = Leaf`, element `a1` (names in this
      -- induction case: `x` root, `a` right subtree, `a1` element).
      rw [braun_node] at hbraun
      have hsize0 : size a = 0 := by
        have hb := hbraun.1
        simp only [size] at hb
        omega
      have ha : a = BraunTree.Leaf := by
        cases a with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst ha
      simp [T_siftDown, height]
  | case3 l₁ x₁ r₁ x₂ r₂ a hle =>
      rw [braun_node] at hbraun
      exfalso
      have hb := hbraun.1
      simp only [size] at hb
      omega
  | case4 l₁ x₁ r₁ x₂ r₂ a hle ih =>
      rw [braun_node] at hbraun
      exfalso
      have hb := hbraun.1
      simp only [size] at hb
      omega
  | case5 l₁ x₁ r₁ a l₂ x₂ r₂ hle =>
      simp [T_siftDown, hle, height]
  | case6 l₁ x₁ r₁ a l₂ x₂ r₂ hle h12 ih =>
      obtain ⟨hsize, hbl, hbr⟩ := hbraun
      have hb1 : Braun (BraunTree.Node l₁ a r₁) := by
        rw [braun_node] at hbl
        rw [braun_node]
        exact ⟨hbl.1, hbl.2.1, hbl.2.2⟩
      have hih := ih hb1
      have hsd : T_siftDown (BraunTree.Node l₁ x₁ r₁) a (BraunTree.Node l₂ x₂ r₂)
          = T_siftDown l₁ a r₁ + 1 := by simp [T_siftDown, hle, h12]
      rw [hsd]
      have h1 : height (BraunTree.Node l₁ x₁ r₁) = max (height l₁) (height r₁) + 1 := rfl
      have hA : max (height l₁) (height r₁) + 1
          ≤ max (height (BraunTree.Node l₁ x₁ r₁)) (height (BraunTree.Node l₂ x₂ r₂)) := by
        rw [h1]; exact le_max_left _ _
      exact le_trans (Nat.add_le_add_right hih 1) (Nat.add_le_add_right hA 1)
  | case7 l₁ x₁ r₁ a l₂ x₂ r₂ hle h12 ih =>
      obtain ⟨hsize, hbl, hbr⟩ := hbraun
      have hb2 : Braun (BraunTree.Node l₂ a r₂) := by
        rw [braun_node] at hbr
        rw [braun_node]
        exact ⟨hbr.1, hbr.2.1, hbr.2.2⟩
      have hih := ih hb2
      have hsd : T_siftDown (BraunTree.Node l₁ x₁ r₁) a (BraunTree.Node l₂ x₂ r₂)
          = T_siftDown l₂ a r₂ + 1 := by simp [T_siftDown, hle, h12]
      rw [hsd]
      have h2 : height (BraunTree.Node l₂ x₂ r₂) = max (height l₂) (height r₂) + 1 := rfl
      have hA : max (height l₂) (height r₂) + 1
          ≤ max (height (BraunTree.Node l₁ x₁ r₁)) (height (BraunTree.Node l₂ x₂ r₂)) := by
        rw [h2]; exact le_max_right _ _
      exact le_trans (Nat.add_le_add_right hih 1) (Nat.add_le_add_right hA 1)

omit [DecidableLT α] [DecidableEq α] in
/-- Book #20 = **Lemma 16.1**: `T_delMin` is at most twice the height. -/
theorem T_delMin_le {t : BraunTree α} (hbraun : Braun t) :
    T_delMin t ≤ 2 * height t := by
  cases t with
  | Leaf => rfl
  | Node l c r =>
      cases l with
      | Leaf =>
          have hT : T_delMin (BraunTree.Node BraunTree.Leaf c r) = 0 := rfl
          rw [hT]; exact Nat.zero_le _
      | Node l₁ x₁ r₁ =>
          cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
          | none =>
              obtain ⟨y, l', hdl'⟩ := delLeft_some_of_ne_leaf
                (show (BraunTree.Node l₁ x₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
              rw [hdl'] at hdl; contradiction
          | some p =>
              obtain ⟨y, l'⟩ := p
              have hdl' : delLeft (BraunTree.Node l₁ x₁ r₁) = some (y, l') := hdl
              have hs : Braun (BraunTree.Node r y l') := braun_siftDown_arg hbraun hdl'
              have hT : T_delMin (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                  = T_delLeft (BraunTree.Node l₁ x₁ r₁) + T_siftDown r y l' := by
                simp [T_delMin, hdl]
              rw [hT]
              have h1 : T_delLeft (BraunTree.Node l₁ x₁ r₁)
                  ≤ height (BraunTree.Node l₁ x₁ r₁) :=
                T_delLeft_le (by simp)
              have h2 : T_siftDown r y l' ≤ max (height r) (height l') + 1 :=
                T_siftDown_le hs
              have h3 : height l' ≤ height (BraunTree.Node l₁ x₁ r₁) :=
                delLeft_height hdl'
              have h4 : height (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                  = max (height (BraunTree.Node l₁ x₁ r₁)) (height r) + 1 := rfl
              have hle : height (BraunTree.Node l₁ x₁ r₁)
                  ≤ max (height (BraunTree.Node l₁ x₁ r₁)) (height r) :=
                le_max_left _ _
              have hmax2 : max (height r) (height l')
                  ≤ max (height (BraunTree.Node l₁ x₁ r₁)) (height r) :=
                le_trans (max_le_max le_rfl h3) (le_of_eq (max_comm _ _))
              omega



/-! ### Logarithmic height (AFP extra, `height_size_braun`) -/

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- Braun trees have logarithmic height: `2 ^ height t ≤ 2 * size t + 1`.
    Not a Chapter 16 statement (it is proved in the AFP entry, and it
    is what makes the running-time bounds in #16–#20 logarithmic). -/
theorem braun_height_size {t : BraunTree α} (ht : Braun t) :
    2 ^ height t ≤ 2 * size t + 1 := by
  induction t with
  | Leaf => simp [height, size]
  | Node l x r ihl ihr =>
      obtain ⟨hsize, hbl, hbr⟩ := ht
      have ihl' := ihl hbl
      have ihr' := ihr hbr
      have hH : height (BraunTree.Node l x r) = max (height l) (height r) + 1 := rfl
      have hS : size (BraunTree.Node l x r) = size l + size r + 1 := rfl
      rw [hH, hS]
      rcases le_total (height l) (height r) with hlr | hrl
      · rw [max_eq_right hlr]
        by_cases h0 : height r = 0
        · rw [h0]
          have hpow : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
          rw [hpow]; omega
        · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
          have hpow : (2 : ℕ) ^ height r = 2 * 2 ^ n := by rw [hn, pow_succ]; ring
          have hbound : 2 ^ n ≤ size r := by
            have h1 := ihr'
            rw [hpow] at h1
            omega
          have hgoal : (2 : ℕ) ^ (height r + 1) = 4 * 2 ^ n := by
            rw [hn, pow_succ, pow_succ]; ring
          rw [hgoal]
          rcases hsize with hs | hs <;> nlinarith [hbound]
      · rw [max_eq_left hrl]
        by_cases h0 : height l = 0
        · rw [h0]
          have hpow : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
          rw [hpow]; omega
        · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
          have hpow : (2 : ℕ) ^ height l = 2 * 2 ^ n := by rw [hn, pow_succ]; ring
          have hbound : 2 ^ n ≤ size l := by
            have h1 := ihl'
            rw [hpow] at h1
            omega
          have hgoal : (2 : ℕ) ^ (height l + 1) = 4 * 2 ^ n := by
            rw [hn, pow_succ, pow_succ]; ring
          rw [hgoal]
          rcases hsize with hs | hs <;> nlinarith [hbound]

/-! ### The ADT discharge: Braun trees *are* priority queues -/

/-- The book's ADT `Priority_Queue` (Chapter 14, Fig. 14.1), discharged
    for Braun trees: empty tree, emptiness test, Braun + heap invariant,
    insertion, deletion, and the root-is-minimum property. In the AFP
    this is `interpretation braun: Priority_Queue`. -/
theorem pq_spec :
    msetTree (BraunTree.Leaf : BraunTree α) = 0 ∧
    (Braun (BraunTree.Leaf : BraunTree α) ∧ Heap (BraunTree.Leaf : BraunTree α)) ∧
    (∀ (a : α) (t : BraunTree α), Braun t ∧ Heap t →
      msetTree (insert a t) = {a} + msetTree t ∧
      Braun (insert a t) ∧ Heap (insert a t)) ∧
    (∀ (l : BraunTree α) (a : α) (r : BraunTree α),
      Braun (BraunTree.Node l a r) ∧ Heap (BraunTree.Node l a r) →
      msetTree (delMin (BraunTree.Node l a r)) = msetTree (BraunTree.Node l a r) - {a} ∧
      Braun (delMin (BraunTree.Node l a r)) ∧ Heap (delMin (BraunTree.Node l a r))) ∧
    (∀ (t : BraunTree α), Braun t ∧ Heap t → msetTree t ≠ 0 →
      getMin t = Min_mset (msetTree t)) ∧
    (∀ (l : BraunTree α) (a : α) (r : BraunTree α), Heap (BraunTree.Node l a r) →
      ∀ y ∈ msetTree (BraunTree.Node l a r), a ≤ y) ∧
    (∀ (t : BraunTree α), isEmpty t = true ↔ msetTree t = 0) := by
  refine ⟨rfl, ⟨trivial, trivial⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro a t h
    exact ⟨mset_insert a t, braun_insert a h.1, heap_insert a h.2⟩
  · intro l a r h
    exact ⟨mset_delMin h.1 (by simp) l a r rfl, braun_delMin h.1,
      heap_delMin h.2 h.1⟩
  · intro t h hm
    exact getMin_eq_Min_mset h.2 (by
      intro hleaf; subst hleaf; simp [msetTree] at hm)
  · intro l a r h y hy
    exact heap_root_le h y hy
  · intro t
    exact isEmpty_iff_mset_eq_zero t

end BraunTree

end Cslib.Algorithms.Lean
