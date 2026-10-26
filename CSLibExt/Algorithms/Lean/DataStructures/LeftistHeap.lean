/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Group.Multiset

/-!
# Leftist heaps and tail-recursive adjacent merging

A concrete persistent min-heap with stored right-spine ranks. `LHeap.heap`
expresses heap ordering; `LHeap.ltree` separately checks every stored rank
and the leftist inequality. `LHeap.merge` preserves both invariants and the
multiset of elements. `LHeap.merge_adj2` merges adjacent pairs using a
reversed accumulator, and `LHeap.merge_all2` repeatedly applies this pass.
`LHeap.lheap_list2` constructs a valid heap with exactly the input multiset.

## Cost model

`LHeap.T_mergeAux` counts only recursive heap-merge steps with two nonempty
arguments; empty-heap base cases cost zero. `LHeap.T_merge_adj` and
`LHeap.T_merge_adj2` sum these merge costs. Accumulator reversal, list
traversal/allocation, size computation, comparisons, and all other overhead
are excluded. Equality of these counters is not equality of total runtime.
No asymptotic construction-time bound is asserted here.

## Provenance

Adapted from `auto-fdsa-15-04/environment/Task.lean` (frozen definitions and
four theorem conjuncts) and `auto-fdsa-15-04/solution/Solution.lean` (complete
reference proof) in `codimango/sw-verification-zhih` at pinned source commit
`16412d086eb5af2e74da78731bde50da0667bc79`. The graded declaration remains
`Cslib.Algorithms.Lean.fdsa_chap15_ex04` for compatibility. Source context:
`auto-fdsa-15-04/solution/provenance/source_context.md` and
`auto-fdsa-15-04/solution/provenance/source_location.json`, grounded in
*Functional Data Structures and Algorithms*, Section 15.4, Exercise 15.2,
`books/functional-data-structures-algorithms/chapters/chapter-15/text.txt`,
lines 4942–4950. The preceding context explicitly counts only merge time;
the exercise does not require output-list equality of the two passes.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

open Multiset

/-! ## Leftist Heap datatype (concrete) -/

/-- Leftist heap: Empty or Node rank value left right -/
inductive LHeap (α : Type) where
| E : LHeap α
| N : Nat → α → LHeap α → LHeap α → LHeap α
deriving DecidableEq

namespace LHeap

variable {α : Type}

/-- Size (number of nodes) -/
def size : LHeap α → Nat
| .E => 0
| .N _ _ l r => 1 + size l + size r

/-- Rank (right spine length, or stored rank) -/
def rank : LHeap α → Nat
| .E => 0
| .N r _ _ _ => r

/-- Multiset of elements -/
def mset_tree : LHeap α → Multiset α
| .E => 0
| .N _ x l r => {x} + mset_tree l + mset_tree r

/-- All elements in heap are ≥ x (for heap ordering) -/
def all_le [LE α] (x : α) : LHeap α → Prop
| .E => True
| .N _ y l r => x ≤ y ∧ all_le x l ∧ all_le x r

/-- Min-heap property: root ≤ all in subtrees -/
def heap [LE α] : LHeap α → Prop
| .E => True
| .N _ x l r => all_le x l ∧ all_le x r ∧ heap l ∧ heap r

/-- Leftist invariant: stored rank is correct and left rank ≥ right rank
    For every node `N storedRank x l r`, require:
    - `storedRank = rank r + 1`;
    - `rank l ≥ rank r`;
    - `ltree l`;
    - `ltree r`.
-/
def ltree : LHeap α → Prop
| .E => True
| .N rk _ l r => rk = r.rank + 1 ∧ l.rank ≥ r.rank ∧ l.ltree ∧ r.ltree

/-- Helper to restore leftist property.
    Constructs a node whose stored rank is exactly one plus the rank
    of its resulting right subtree (b.rank + 1 or a.rank + 1 after swap). -/
def make (x : α) (a b : LHeap α) : LHeap α :=
  if a.rank ≥ b.rank then
    .N (b.rank + 1) x a b
  else
    .N (a.rank + 1) x b a

/-- Auxiliary fuel-based merge to avoid termination proof complexity.
    When reconstructing an existing node during recursion, preserves its
    original stored rank (does not replace it with 0). -/
def mergeAux [LinearOrder α] : Nat → LHeap α → LHeap α → LHeap α
| _, .E, h => h
| _, h, .E => h
| 0, _, _ => .E
| fuel + 1, .N rx x la ra, .N ry y lb rb =>
  if x ≤ y then
    make x la (mergeAux fuel ra (LHeap.N ry y lb rb))
  else
    make y lb (mergeAux fuel (LHeap.N rx x la ra) rb)

/-- Leftist merge (public API) -/
def merge [LinearOrder α] (h1 h2 : LHeap α) : LHeap α :=
  mergeAux (h1.size + h2.size) h1 h2

/-- Auxiliary fuel-based cost of merge.
    Complexity model faithful to textbook convention: only calls/steps of `merge`
    are counted. Reversal of accumulator in `merge_adj2` and other auxiliary
    operations are not counted. -/
def T_mergeAux [LinearOrder α] : Nat → LHeap α → LHeap α → Nat
| _, .E, _ => 0
| _, _, .E => 0
| 0, _, _ => 0
| fuel + 1, .N rx x _ ra, .N ry y _ rb =>
  if x ≤ y then
    1 + T_mergeAux fuel ra (LHeap.N ry y (LHeap.E : LHeap α) rb)
  else
    1 + T_mergeAux fuel (LHeap.N rx x (LHeap.E : LHeap α) ra) rb

/-- Cost of merge: number of merge steps (only merge calls counted) -/
def T_merge [LinearOrder α] (h1 h2 : LHeap α) : Nat :=
  T_mergeAux (h1.size + h2.size) h1 h2

/-- Non-tail-recursive merge_adj -/
def merge_adj [LinearOrder α] : List (LHeap α) → List (LHeap α)
| [] => []
| [t] => [t]
| t1 :: t2 :: ts => (t1.merge t2) :: merge_adj ts

/-- Tail-recursive merge_adj2 with accumulator, no use of List.append.
    Genuinely tail-recursive: uses an accumulator and reverse at base case.
    Does not use List.append (avoids append operator).
    Complexity model: only merge steps counted, so `T_merge_adj2 acc ts = T_merge_adj ts`
    should hold; accumulator reversal overhead is intentionally excluded
    per textbook convention that only merge calls are counted. -/
def merge_adj2 [LinearOrder α] (acc : List (LHeap α)) (ts : List (LHeap α)) : List (LHeap α) :=
  match ts with
  | [] => acc.reverse
  | [t] => (t :: acc).reverse
  | t1 :: t2 :: ts' => merge_adj2 (t1.merge t2 :: acc) ts'
termination_by ts.length

/-- Cost of merge_adj: only merge steps counted per textbook -/
def T_merge_adj [LinearOrder α] : List (LHeap α) → Nat
| [] => 0
| [_] => 0
| t1 :: t2 :: ts => (T_merge t1 t2) + T_merge_adj ts

/-- Cost of merge_adj2 (accumulator version): only merge steps counted.
    Follows textbook convention that only calls/steps of `merge` are counted,
    so accumulator handling does not contribute to cost. Hence the required
    comparison `T_merge_adj2 acc ts = T_merge_adj ts` remains valid. -/
def T_merge_adj2 [LinearOrder α] : List (LHeap α) → List (LHeap α) → Nat
| _, [] => 0
| _, [_] => 0
| acc, t1 :: t2 :: ts => (T_merge t1 t2) + T_merge_adj2 (t1.merge t2 :: acc) ts
termination_by _ ts => ts.length

/-! ### merge_all variants using fuel to avoid complex termination proofs -/

def merge_allAux [LinearOrder α] : Nat → List (LHeap α) → LHeap α
| _, [] => .E
| _, [t] => t
| 0, _ => .E
| fuel + 1, ts => merge_allAux fuel (merge_adj ts)

def merge_all [LinearOrder α] (ts : List (LHeap α)) : LHeap α :=
  merge_allAux ts.length ts

/-- merge_all2 uses merge_adj2 (tail-recursive variant) -/
def merge_all2Aux [LinearOrder α] : Nat → List (LHeap α) → LHeap α
| _, [] => .E
| _, [t] => t
| 0, _ => .E
| fuel + 1, ts => merge_all2Aux fuel (merge_adj2 [] ts)

def merge_all2 [LinearOrder α] (ts : List (LHeap α)) : LHeap α :=
  merge_all2Aux ts.length ts

/-- Singleton heap: stored rank 1 = rank E + 1, leftist -/
def singleton [LinearOrder α] (x : α) : LHeap α :=
  .N 1 x .E .E

/-- lheap_list2: convert list to leftist heap via merge_all2 (tail-recursive adj).
    Uses merge_all2 which itself uses merge_adj2. -/
def lheap_list2 [LinearOrder α] (xs : List α) : LHeap α :=
  merge_all2 (xs.map singleton)

end LHeap

open LHeap

namespace LHeap

variable {α : Type}

/-! ### Node construction and merge correctness -/
theorem mset_make (x : α) (a b : LHeap α) :
  mset_tree (make x a b) = ({x} : Multiset α) + mset_tree a + mset_tree b := by
  by_cases h : a.rank ≥ b.rank
  · have hm : make x a b = LHeap.N (b.rank + 1) x a b := by simp [make, h]
    rw [hm]; simp [mset_tree]
  · have hm : make x a b = LHeap.N (a.rank + 1) x b a := by simp [make, h]
    rw [hm]; simp only [mset_tree]; ac_rfl

theorem size_make (x : α) (a b : LHeap α) :
  size (make x a b) = 1 + size a + size b := by
  by_cases h : a.rank ≥ b.rank
  · have hm : make x a b = LHeap.N (b.rank + 1) x a b := by simp [make, h]
    rw [hm]; simp [size]
  · have hm : make x a b = LHeap.N (a.rank + 1) x b a := by simp [make, h]
    rw [hm]; simp [size]; ac_rfl

theorem rank_make (x : α) (a b : LHeap α) :
  rank (make x a b) = min (rank a) (rank b) + 1 := by
  by_cases h : a.rank ≥ b.rank
  · have hm : make x a b = LHeap.N (b.rank + 1) x a b := by simp [make, h]
    rw [hm, rank, Nat.min_eq_right h]
  · have hm : make x a b = LHeap.N (a.rank + 1) x b a := by simp [make, h]
    rw [hm, rank]
    have hle : a.rank ≤ b.rank := Nat.le_of_not_ge h
    rw [Nat.min_eq_left hle]

theorem all_le_make [LE α] {x z : α} {a b : LHeap α} :
  z ≤ x → all_le z a → all_le z b → all_le z (make x a b) := by
  intro hzx ha hb
  by_cases h : a.rank ≥ b.rank
  · have hm : make x a b = LHeap.N (b.rank + 1) x a b := by simp [make, h]
    rw [hm]
    simp only [all_le]
    exact ⟨hzx, ha, hb⟩
  · have hm : make x a b = LHeap.N (a.rank + 1) x b a := by simp [make, h]
    rw [hm]
    simp only [all_le]
    exact ⟨hzx, hb, ha⟩

theorem heap_make [LinearOrder α] {x : α} {a b : LHeap α} :
  all_le x a → all_le x b → heap a → heap b → heap (make x a b) := by
  intro ha hb hha hhb
  by_cases h : a.rank ≥ b.rank
  · have hm : make x a b = LHeap.N (b.rank + 1) x a b := by simp [make, h]
    rw [hm]
    simp only [heap]
    exact ⟨ha, hb, hha, hhb⟩
  · have hm : make x a b = LHeap.N (a.rank + 1) x b a := by simp [make, h]
    rw [hm]
    simp only [heap]
    exact ⟨hb, ha, hhb, hha⟩

theorem ltree_make {x : α} {a b : LHeap α} (ha : ltree a) (hb : ltree b) :
  ltree (make x a b) := by
  by_cases h : a.rank ≥ b.rank
  · have hm : make x a b = LHeap.N (b.rank + 1) x a b := by simp [make, h]
    rw [hm]
    simp only [ltree, rank, true_and]
    exact ⟨h, ha, hb⟩
  · have hm : make x a b = LHeap.N (a.rank + 1) x b a := by simp [make, h]
    rw [hm]
    simp only [ltree, rank, true_and]
    have hle : a.rank ≤ b.rank := Nat.le_of_not_ge h
    exact ⟨hle, hb, ha⟩

theorem all_le_trans [Preorder α] {x y : α} {h : LHeap α} :
  x ≤ y → all_le y h → all_le x h := by
  intro hxy hy
  induction h with
  | E => trivial
  | N r v l r ihl ihr =>
    simp only [all_le] at hy ⊢
    obtain ⟨hyv, hyl, hyr⟩ := hy
    exact ⟨le_trans hxy hyv, ihl hyl, ihr hyr⟩

theorem heap_all_le [Preorder α] {x : α} {l r : LHeap α} {rk : Nat}
  (h : heap (LHeap.N rk x l r)) : all_le x (LHeap.N rk x l r) := by
  unfold heap at h
  unfold all_le
  exact ⟨le_refl x, h.1, h.2.1⟩

theorem mset_mergeAux [LinearOrder α] (fuel : Nat) (h1 h2 : LHeap α)
  (hf : h1.size + h2.size ≤ fuel) :
  mset_tree (mergeAux fuel h1 h2) = mset_tree h1 + mset_tree h2 := by
  induction fuel generalizing h1 h2 with
  | zero =>
    cases h1 with
    | E => simp [mergeAux, mset_tree]
    | N rx x la ra =>
      cases h2 with
      | E => simp [mergeAux, mset_tree]
      | N ry y lb rb =>
        simp at hf
        have h1size : 0 < (LHeap.N rx x la ra).size := by simp only [size]; omega
        have h2size : 0 < (LHeap.N ry y lb rb).size := by simp only [size]; omega
        omega
  | succ fuel ih =>
    cases h1 with
    | E => simp [mergeAux, mset_tree]
    | N rx x la ra =>
      cases h2 with
      | E => simp [mergeAux, mset_tree]
      | N ry y lb rb =>
        simp only [mergeAux]
        by_cases hxy : x ≤ y
        · simp only [hxy, ↓reduceIte]
          rw [mset_make]
          have hf' : ra.size + (LHeap.N ry y lb rb).size ≤ fuel := by
            simp only [size] at hf ⊢
            omega
          rw [ih ra (LHeap.N ry y lb rb) hf']
          simp only [mset_tree]
          ac_rfl
        · simp only [hxy, ↓reduceIte]
          rw [mset_make]
          have hf' : (LHeap.N rx x la ra).size + rb.size ≤ fuel := by
            simp only [size] at hf ⊢
            omega
          rw [ih (LHeap.N rx x la ra) rb hf']
          simp only [mset_tree]
          ac_rfl

theorem all_le_mergeAux [LinearOrder α] (fuel : Nat) (h1 h2 : LHeap α) (z : α)
  (hf : h1.size + h2.size ≤ fuel)
  (hz1 : all_le z h1) (hz2 : all_le z h2) :
  all_le z (mergeAux fuel h1 h2) := by
  induction fuel generalizing h1 h2 with
  | zero =>
    cases h1 with
    | E => simp only [mergeAux] at *; exact hz2
    | N rx x la ra =>
      cases h2 with
      | E => simp only [mergeAux] at *; exact hz1
      | N ry y lb rb =>
        simp at hf
        have h1size : 0 < (LHeap.N rx x la ra).size := by simp only [size]; omega
        have h2size : 0 < (LHeap.N ry y lb rb).size := by simp only [size]; omega
        omega
  | succ fuel ih =>
    cases h1 with
    | E => simp only [mergeAux] at *; exact hz2
    | N rx x la ra =>
      cases h2 with
      | E => simp only [mergeAux] at *; exact hz1
      | N ry y lb rb =>
        simp only [mergeAux]
        by_cases hxy : x ≤ y
        · simp only [hxy, ↓reduceIte]
          apply all_le_make
          · simp only [all_le] at hz1 ⊢; exact hz1.1
          · simp only [all_le] at hz1; exact hz1.2.1
          · apply ih
            · simp [size] at hf ⊢; omega
            · simp only [all_le] at hz1; exact hz1.2.2
            · exact hz2
        · simp only [hxy, ↓reduceIte]
          apply all_le_make
          · simp only [all_le] at hz2 ⊢; exact hz2.1
          · simp only [all_le] at hz2; exact hz2.2.1
          · apply ih
            · simp [size] at hf ⊢; omega
            · exact hz1
            · simp only [all_le] at hz2; exact hz2.2.2

theorem heap_mergeAux [LinearOrder α] (fuel : Nat) (h1 h2 : LHeap α)
  (hf : h1.size + h2.size ≤ fuel)
  (hh1 : heap h1) (hh2 : heap h2) :
  heap (mergeAux fuel h1 h2) := by
  induction fuel generalizing h1 h2 with
  | zero =>
    cases h1 with
    | E => simp only [mergeAux]; exact hh2
    | N rx x la ra =>
      cases h2 with
      | E => simp only [mergeAux]; exact hh1
      | N ry y lb rb =>
        simp at hf
        have h1size : 0 < (LHeap.N rx x la ra).size := by simp only [size]; omega
        have h2size : 0 < (LHeap.N ry y lb rb).size := by simp only [size]; omega
        omega
  | succ fuel ih =>
    cases h1 with
    | E => simp only [mergeAux]; exact hh2
    | N rx x la ra =>
      cases h2 with
      | E => simp only [mergeAux]; exact hh1
      | N ry y lb rb =>
        simp only [mergeAux]
        by_cases hxy : x ≤ y
        · simp only [hxy, ↓reduceIte]
          apply heap_make
          · unfold heap at hh1; exact hh1.1
          · have hall_ra : all_le x ra := by unfold heap at hh1; exact hh1.2.1
            have hall_h2 : all_le x (LHeap.N ry y lb rb) := by
              have hay : all_le y (LHeap.N ry y lb rb) := heap_all_le hh2
              exact all_le_trans hxy hay
            exact all_le_mergeAux fuel ra (LHeap.N ry y lb rb) x
              (by simp only [size] at hf ⊢; omega) hall_ra hall_h2
          · unfold heap at hh1; exact hh1.2.2.1
          · apply ih
            · simp [size] at hf ⊢; omega
            · unfold heap at hh1; exact hh1.2.2.2
            · exact hh2
        · simp only [hxy, ↓reduceIte]
          apply heap_make
          · unfold heap at hh2; exact hh2.1
          · have hall_rb : all_le y rb := by unfold heap at hh2; exact hh2.2.1
            have h_y_le_x : y ≤ x := le_of_not_ge hxy
            have hall_y_h1 : all_le y (LHeap.N rx x la ra) := by
              have hay : all_le x (LHeap.N rx x la ra) := heap_all_le hh1
              exact all_le_trans h_y_le_x hay
            exact all_le_mergeAux fuel (LHeap.N rx x la ra) rb y
              (by simp only [size] at hf ⊢; omega) hall_y_h1 hall_rb
          · unfold heap at hh2; exact hh2.2.2.1
          · apply ih
            · simp [size] at hf ⊢; omega
            · exact hh1
            · unfold heap at hh2; exact hh2.2.2.2

theorem ltree_mergeAux [LinearOrder α] (fuel : Nat) (h1 h2 : LHeap α)
  (hf : h1.size + h2.size ≤ fuel)
  (hl1 : ltree h1) (hl2 : ltree h2) :
  ltree (mergeAux fuel h1 h2) := by
  induction fuel generalizing h1 h2 with
  | zero =>
    cases h1 with
    | E => simp only [mergeAux]; exact hl2
    | N rx x la ra =>
      cases h2 with
      | E => simp only [mergeAux]; exact hl1
      | N ry y lb rb =>
        simp at hf
        have h1size : 0 < (LHeap.N rx x la ra).size := by simp only [size]; omega
        have h2size : 0 < (LHeap.N ry y lb rb).size := by simp only [size]; omega
        omega
  | succ fuel ih =>
    cases h1 with
    | E => simp only [mergeAux]; exact hl2
    | N rx x la ra =>
      cases h2 with
      | E => simp only [mergeAux]; exact hl1
      | N ry y lb rb =>
        simp only [mergeAux]
        by_cases hxy : x ≤ y
        · simp only [hxy, ↓reduceIte]
          apply ltree_make
          · unfold ltree at hl1; exact hl1.2.2.1
          · apply ih
            · simp [size] at hf ⊢; omega
            · unfold ltree at hl1; exact hl1.2.2.2
            · exact hl2
        · simp only [hxy, ↓reduceIte]
          apply ltree_make
          · unfold ltree at hl2; exact hl2.2.2.1
          · apply ih
            · simp [size] at hf ⊢; omega
            · exact hl1
            · unfold ltree at hl2; exact hl2.2.2.2

theorem mset_merge [LinearOrder α] (h1 h2 : LHeap α) :
  mset_tree (h1.merge h2) = mset_tree h1 + mset_tree h2 := by
  unfold merge
  apply mset_mergeAux
  omega

theorem heap_merge [LinearOrder α] (h1 h2 : LHeap α) (hh1 : heap h1) (hh2 : heap h2) :
  heap (h1.merge h2) := by
  unfold merge
  apply heap_mergeAux
  · omega
  · exact hh1
  · exact hh2

theorem ltree_merge [LinearOrder α] (h1 h2 : LHeap α) (hl1 : ltree h1) (hl2 : ltree h2) :
  ltree (h1.merge h2) := by
  unfold merge
  apply ltree_mergeAux
  · omega
  · exact hl1
  · exact hl2

-- sum and list helpers
/-- Combined multiset of every heap in a list, including duplicates. -/
def sumMSet : List (LHeap α) → Multiset α
| [] => 0
| t :: ts => mset_tree t + sumMSet ts

theorem sumMSet_append (l1 l2 : List (LHeap α)) : sumMSet (l1 ++ l2) = sumMSet l1 + sumMSet l2 := by
  induction l1 with
  | nil => simp [sumMSet]
  | cons x xs ih => simp [sumMSet, ih]; ac_rfl

theorem sumMSet_reverse (l : List (LHeap α)) : sumMSet (l.reverse) = sumMSet l := by
  induction l with
  | nil => simp [sumMSet]
  | cons x xs ih =>
    rw [List.reverse_cons]
    rw [sumMSet_append]
    rw [ih]
    simp [sumMSet]
    ac_rfl

theorem sumMSet_merge_adj [LinearOrder α] (ts : List (LHeap α)) :
  sumMSet (merge_adj ts) = sumMSet ts := by
  match ts with
  | [] => simp [merge_adj, sumMSet]
  | [t] => simp [merge_adj, sumMSet]
  | t1 :: t2 :: ts' =>
    simp only [merge_adj, sumMSet, mset_merge]
    rw [sumMSet_merge_adj ts']
    ac_rfl

/-- Every heap in the list satisfies the min-heap ordering predicate. -/
def HeapList [LE α] (ts : List (LHeap α)) : Prop := ∀ t ∈ ts, heap t

/-- Every heap in the list has correct stored ranks and is leftist. -/
def LTreeList (ts : List (LHeap α)) : Prop := ∀ t ∈ ts, ltree t

theorem HeapList_cons [LE α] {x : LHeap α} {xs : List (LHeap α)} :
  HeapList (x :: xs) ↔ heap (α:=α) x ∧ HeapList xs := by
  constructor
  · intro h
    constructor
    · exact h x (by simp)
    · intro t ht
      exact h t (by simp [ht])
  · intro h t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact h.1
    · exact h.2 t ht

theorem HeapList_append [LE α] {l1 l2 : List (LHeap α)} :
  HeapList (l1 ++ l2) ↔ HeapList l1 ∧ HeapList l2 := by
  constructor
  · intro h
    constructor
    · intro t ht
      exact h t (by simp [ht])
    · intro t ht
      exact h t (by simp [ht])
  · intro h t ht
    simp only [List.mem_append] at ht
    rcases ht with ht | ht
    · exact h.1 t ht
    · exact h.2 t ht

theorem HeapList_reverse [LE α] {l : List (LHeap α)} :
  HeapList (l.reverse) ↔ HeapList l := by
  constructor
  · intro h t ht
    exact h t (by rw [List.mem_reverse]; exact ht)
  · intro h t ht
    rw [List.mem_reverse] at ht
    exact h t ht

theorem LTreeList_cons {x : LHeap α} {xs : List (LHeap α)} :
  LTreeList (x :: xs) ↔ ltree x ∧ LTreeList xs := by
  constructor
  · intro h
    constructor
    · exact h x (by simp)
    · intro t ht
      exact h t (by simp [ht])
  · intro h t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact h.1
    · exact h.2 t ht

theorem LTreeList_reverse {l : List (LHeap α)} :
  LTreeList (l.reverse) ↔ LTreeList l := by
  constructor
  · intro h t ht
    exact h t (by rw [List.mem_reverse]; exact ht)
  · intro h t ht
    rw [List.mem_reverse] at ht
    exact h t ht

theorem LTreeList_append {l1 l2 : List (LHeap α)} :
  LTreeList (l1 ++ l2) ↔ LTreeList l1 ∧ LTreeList l2 := by
  constructor
  · intro h
    constructor
    · intro t ht
      exact h t (by simp [ht])
    · intro t ht
      exact h t (by simp [ht])
  · intro h t ht
    simp only [List.mem_append] at ht
    rcases ht with ht | ht
    · exact h.1 t ht
    · exact h.2 t ht

theorem heapList_merge_adj [LinearOrder α] (ts : List (LHeap α)) (h : HeapList ts) :
  HeapList (merge_adj ts) := by
  match ts with
  | [] => exact h
  | [t] => exact h
  | t1 :: t2 :: ts' =>
    simp only [merge_adj]
    intro u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · apply heap_merge
      · exact h t1 (by simp)
      · exact h t2 (by simp [List.mem_cons])
    · have h' : HeapList ts' := by
        intro v hv
        exact h v (by simp [hv])
      have ih := heapList_merge_adj ts' h'
      exact ih u hu

theorem ltreeList_merge_adj [LinearOrder α] (ts : List (LHeap α)) (h : LTreeList ts) :
  LTreeList (merge_adj ts) := by
  match ts with
  | [] => exact h
  | [t] => exact h
  | t1 :: t2 :: ts' =>
    simp only [merge_adj]
    intro u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · apply ltree_merge
      · exact h t1 (by simp)
      · exact h t2 (by simp [List.mem_cons])
    · have h' : LTreeList ts' := by
        intro v hv
        exact h v (by simp [hv])
      have ih := ltreeList_merge_adj ts' h'
      exact ih u hu

-- length lemmas
theorem length_merge_adj [LinearOrder α] (ts : List (LHeap α)) :
  (merge_adj ts).length ≤ ts.length := by
  match ts with
  | [] => simp [merge_adj]
  | [t] => simp [merge_adj]
  | t1 :: t2 :: ts' =>
    simp [merge_adj]
    have ih := length_merge_adj (ts' : List (LHeap α))
    omega

theorem length_merge_adj_lt [LinearOrder α] (ts : List (LHeap α)) (h : ts.length ≥ 2) :
  (merge_adj ts).length < ts.length := by
  match ts with
  | [] => simp at h
  | [t] => simp at h
  | t1 :: t2 :: ts' =>
    simp [merge_adj]
    have hle := length_merge_adj (ts' : List (LHeap α))
    omega

theorem length_merge_adj2_le [LinearOrder α] (acc ts : List (LHeap α)) :
  (merge_adj2 acc ts).length ≤ acc.length + ts.length := by
  match ts with
  | [] =>
    simp [merge_adj2]
  | [t] =>
    simp [merge_adj2]
  | t1 :: t2 :: ts' =>
    simp only [merge_adj2]
    have ih := length_merge_adj2_le (t1.merge t2 :: acc) ts'
    simp at ih
    have hlen : (t1 :: t2 :: ts').length = ts'.length + 2 := by simp
    omega

theorem length_merge_adj2_lt [LinearOrder α] (ts : List (LHeap α)) (h : ts.length ≥ 2) :
  (merge_adj2 ([] : List (LHeap α)) ts).length < ts.length := by
  match ts with
  | [] => simp at h
  | [t] => simp at h
  | t1 :: t2 :: ts' =>
    simp only [merge_adj2]
    have hle := length_merge_adj2_le [t1.merge t2] ts'
    simp at hle
    have hlen : (t1 :: t2 :: ts').length = ts'.length + 2 := by simp
    omega

-- merge_adj2 sum and heap/ltree
theorem sumMSet_merge_adj2 [LinearOrder α] (acc ts : List (LHeap α)) :
  sumMSet (merge_adj2 acc ts) = sumMSet acc + sumMSet ts := by
  match ts with
  | [] =>
    simp only [merge_adj2, sumMSet_reverse, sumMSet]
    simp
  | [t] =>
    simp only [merge_adj2, sumMSet, sumMSet_reverse]
    ac_rfl
  | t1 :: t2 :: ts' =>
    simp only [merge_adj2]
    rw [sumMSet_merge_adj2 (t1.merge t2 :: acc) ts']
    simp [sumMSet, mset_merge]
    ac_rfl

theorem heapList_merge_adj2 [LinearOrder α] (acc ts : List (LHeap α))
  (hacc : HeapList acc) (hts : HeapList ts) :
  HeapList (merge_adj2 acc ts) := by
  match ts with
  | [] =>
    simp only [merge_adj2]
    rw [HeapList_reverse]
    exact hacc
  | t :: [] =>
    simp only [merge_adj2]
    rw [HeapList_reverse, HeapList_cons]
    constructor
    · exact hts t (by simp)
    · exact hacc
  | t1 :: t2 :: ts' =>
    simp only [merge_adj2]
    have hacc' : HeapList (t1.merge t2 :: acc) := by
      rw [HeapList_cons]
      constructor
      · apply heap_merge
        · exact hts t1 (by simp)
        · exact hts t2 (by simp [List.mem_cons])
      · exact hacc
    have hts' : HeapList ts' := by
      intro v hv
      exact hts v (by simp [hv])
    exact heapList_merge_adj2 (t1.merge t2 :: acc) ts' hacc' hts'

theorem ltreeList_merge_adj2 [LinearOrder α] (acc ts : List (LHeap α))
  (hacc : LTreeList acc) (hts : LTreeList ts) :
  LTreeList (merge_adj2 acc ts) := by
  match ts with
  | [] =>
    simp only [merge_adj2]
    rw [LTreeList_reverse]
    exact hacc
  | t :: [] =>
    simp only [merge_adj2]
    rw [LTreeList_reverse, LTreeList_cons]
    constructor
    · exact hts t (by simp)
    · exact hacc
  | t1 :: t2 :: ts' =>
    simp only [merge_adj2]
    have hacc' : LTreeList (t1.merge t2 :: acc) := by
      rw [LTreeList_cons]
      constructor
      · apply ltree_merge
        · exact hts t1 (by simp)
        · exact hts t2 (by simp [List.mem_cons])
      · exact hacc
    have hts' : LTreeList ts' := by
      intro v hv
      exact hts v (by simp [hv])
    exact ltreeList_merge_adj2 (t1.merge t2 :: acc) ts' hacc' hts'

-- T lemmas
theorem T_merge_adj2_eq [LinearOrder α] (acc ts : List (LHeap α)) :
  T_merge_adj2 acc ts = T_merge_adj ts := by
  match ts with
  | [] => simp [T_merge_adj, T_merge_adj2]
  | [t] => simp [T_merge_adj, T_merge_adj2]
  | t1 :: t2 :: ts' =>
    simp only [T_merge_adj, T_merge_adj2]
    rw [T_merge_adj2_eq (t1.merge t2 :: acc) ts']

-- singleton lemmas
theorem mset_singleton [LinearOrder α] (x : α) : mset_tree (singleton (α:=α) x) = {x} := by
  simp [singleton, mset_tree]

theorem heap_singleton [LinearOrder α] (x : α) : heap (singleton (α:=α) x) := by
  simp [singleton, heap, all_le]

theorem ltree_singleton [LinearOrder α] (x : α) : ltree (singleton (α:=α) x) := by
  simp [singleton, ltree, rank]

theorem sumMSet_map_singleton [LinearOrder α] (xs : List α) :
  sumMSet (xs.map singleton) = (xs : Multiset α) := by
  induction xs with
  | nil => simp [sumMSet]
  | cons x xs ih =>
    simp [sumMSet, mset_singleton, ih]

theorem heapList_map_singleton [LinearOrder α] (xs : List α) : HeapList (xs.map singleton) := by
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  exact heap_singleton x

theorem ltreeList_map_singleton [LinearOrder α] (xs : List α) : LTreeList (xs.map singleton) := by
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  exact ltree_singleton x

-- merge_all lemmas
theorem mset_merge_allAux [LinearOrder α] (fuel : Nat) (ts : List (LHeap α))
  (hf : ts.length ≤ fuel) :
  mset_tree (merge_allAux fuel ts) = sumMSet ts := by
  induction fuel generalizing ts with
  | zero =>
    match ts with
    | [] => simp [merge_allAux, sumMSet, mset_tree]
    | [t] => simp [merge_allAux, sumMSet]
    | t1 :: t2 :: ts' =>
      simp at hf
  | succ fuel ih =>
    match ts with
    | [] => simp [merge_allAux, sumMSet, mset_tree]
    | [t] => simp [merge_allAux, sumMSet]
    | t1 :: t2 :: ts' =>
      simp only [merge_allAux]
      have hf' : (merge_adj (t1 :: t2 :: ts')).length ≤ fuel := by
        have hle := length_merge_adj (t1 :: t2 :: ts')
        have hlt : (merge_adj (t1 :: t2 :: ts')).length < (t1 :: t2 :: ts').length := by
          apply length_merge_adj_lt; simp
        omega
      rw [ih (merge_adj (t1 :: t2 :: ts')) hf']
      rw [sumMSet_merge_adj]

theorem heap_merge_allAux [LinearOrder α] (fuel : Nat) (ts : List (LHeap α))
  (hf : ts.length ≤ fuel) (h : HeapList ts) :
  heap (merge_allAux fuel ts) := by
  induction fuel generalizing ts with
  | zero =>
    match ts with
    | [] => simp [merge_allAux, heap]
    | [t] =>
      simp only [merge_allAux]
      exact h t (by simp)
    | t1 :: t2 :: ts' => simp at hf
  | succ fuel ih =>
    match ts with
    | [] => simp [merge_allAux, heap]
    | [t] =>
      simp only [merge_allAux]
      exact h t (by simp)
    | t1 :: t2 :: ts' =>
      simp only [merge_allAux]
      have hf' : (merge_adj (t1 :: t2 :: ts')).length ≤ fuel := by
        have hle := length_merge_adj (t1 :: t2 :: ts')
        have hlt : (merge_adj (t1 :: t2 :: ts')).length < (t1 :: t2 :: ts').length := by
          apply length_merge_adj_lt; simp
        omega
      have h' : HeapList (merge_adj (t1 :: t2 :: ts')) := heapList_merge_adj _ h
      exact ih (merge_adj (t1 :: t2 :: ts')) hf' h'

theorem ltree_merge_allAux [LinearOrder α] (fuel : Nat) (ts : List (LHeap α))
  (hf : ts.length ≤ fuel) (h : LTreeList ts) :
  ltree (merge_allAux fuel ts) := by
  induction fuel generalizing ts with
  | zero =>
    match ts with
    | [] => simp [merge_allAux, ltree]
    | [t] =>
      simp only [merge_allAux]
      exact h t (by simp)
    | t1 :: t2 :: ts' => simp at hf
  | succ fuel ih =>
    match ts with
    | [] => simp [merge_allAux, ltree]
    | [t] =>
      simp only [merge_allAux]
      exact h t (by simp)
    | t1 :: t2 :: ts' =>
      simp only [merge_allAux]
      have hf' : (merge_adj (t1 :: t2 :: ts')).length ≤ fuel := by
        have hle := length_merge_adj (t1 :: t2 :: ts')
        have hlt : (merge_adj (t1 :: t2 :: ts')).length < (t1 :: t2 :: ts').length := by
          apply length_merge_adj_lt; simp
        omega
      have h' : LTreeList (merge_adj (t1 :: t2 :: ts')) := ltreeList_merge_adj _ h
      exact ih (merge_adj (t1 :: t2 :: ts')) hf' h'

theorem mset_merge_all [LinearOrder α] (ts : List (LHeap α)) :
  mset_tree (merge_all ts) = sumMSet ts := by
  unfold merge_all
  apply mset_merge_allAux
  omega

theorem heap_merge_all [LinearOrder α] (ts : List (LHeap α)) (h : HeapList ts) :
  heap (merge_all ts) := by
  unfold merge_all
  apply heap_merge_allAux
  · omega
  · exact h

theorem ltree_merge_all [LinearOrder α] (ts : List (LHeap α)) (h : LTreeList ts) :
  ltree (merge_all ts) := by
  unfold merge_all
  apply ltree_merge_allAux
  · omega
  · exact h

-- merge_all2 lemmas (using merge_adj2)
theorem mset_merge_all2Aux [LinearOrder α] (fuel : Nat) (ts : List (LHeap α))
  (hf : ts.length ≤ fuel) :
  mset_tree (merge_all2Aux fuel ts) = sumMSet ts := by
  induction fuel generalizing ts with
  | zero =>
    match ts with
    | [] => simp [merge_all2Aux, sumMSet, mset_tree]
    | [t] => simp [merge_all2Aux, sumMSet]
    | t1 :: t2 :: ts' => simp at hf
  | succ fuel ih =>
    match ts with
    | [] => simp [merge_all2Aux, sumMSet, mset_tree]
    | [t] => simp [merge_all2Aux, sumMSet]
    | t1 :: t2 :: ts' =>
      simp only [merge_all2Aux]
      have hf' : (merge_adj2 [] (t1 :: t2 :: ts')).length ≤ fuel := by
        have hle := length_merge_adj2_le ([] : List (LHeap α)) (t1 :: t2 :: ts')
        simp at hle
        have hlt : (merge_adj2 [] (t1 :: t2 :: ts')).length < (t1 :: t2 :: ts').length := by
          apply length_merge_adj2_lt; simp
        omega
      have hsum : sumMSet (merge_adj2 [] (t1 :: t2 :: ts')) = sumMSet (t1 :: t2 :: ts') := by
        have h := sumMSet_merge_adj2 [] (t1 :: t2 :: ts')
        have h2 : sumMSet ([] : List (LHeap α)) = 0 := by simp [sumMSet]
        rw [h, h2, zero_add]
      rw [ih (merge_adj2 [] (t1 :: t2 :: ts')) hf']
      exact hsum

theorem heap_merge_all2Aux [LinearOrder α] (fuel : Nat) (ts : List (LHeap α))
  (hf : ts.length ≤ fuel) (h : HeapList ts) :
  heap (merge_all2Aux fuel ts) := by
  induction fuel generalizing ts with
  | zero =>
    match ts with
    | [] => simp [merge_all2Aux, heap]
    | [t] =>
      simp only [merge_all2Aux]
      exact h t (by simp)
    | t1 :: t2 :: ts' => simp at hf
  | succ fuel ih =>
    match ts with
    | [] => simp [merge_all2Aux, heap]
    | [t] =>
      simp only [merge_all2Aux]
      exact h t (by simp)
    | t1 :: t2 :: ts' =>
      simp only [merge_all2Aux]
      have hf' : (merge_adj2 [] (t1 :: t2 :: ts')).length ≤ fuel := by
        have hle := length_merge_adj2_le ([] : List (LHeap α)) (t1 :: t2 :: ts')
        simp at hle
        have hlt : (merge_adj2 [] (t1 :: t2 :: ts')).length < (t1 :: t2 :: ts').length := by
          apply length_merge_adj2_lt; simp
        omega
      have h' : HeapList (merge_adj2 [] (t1 :: t2 :: ts')) := by
        have h0 : HeapList ([] : List (LHeap α)) := by intro t ht; simp at ht
        exact heapList_merge_adj2 [] (t1 :: t2 :: ts') h0 h
      exact ih (merge_adj2 [] (t1 :: t2 :: ts')) hf' h'

theorem ltree_merge_all2Aux [LinearOrder α] (fuel : Nat) (ts : List (LHeap α))
  (hf : ts.length ≤ fuel) (h : LTreeList ts) :
  ltree (merge_all2Aux fuel ts) := by
  induction fuel generalizing ts with
  | zero =>
    match ts with
    | [] => simp [merge_all2Aux, ltree]
    | [t] =>
      simp only [merge_all2Aux]
      exact h t (by simp)
    | t1 :: t2 :: ts' => simp at hf
  | succ fuel ih =>
    match ts with
    | [] => simp [merge_all2Aux, ltree]
    | [t] =>
      simp only [merge_all2Aux]
      exact h t (by simp)
    | t1 :: t2 :: ts' =>
      simp only [merge_all2Aux]
      have hf' : (merge_adj2 [] (t1 :: t2 :: ts')).length ≤ fuel := by
        have hle := length_merge_adj2_le ([] : List (LHeap α)) (t1 :: t2 :: ts')
        simp at hle
        have hlt : (merge_adj2 [] (t1 :: t2 :: ts')).length < (t1 :: t2 :: ts').length := by
          apply length_merge_adj2_lt; simp
        omega
      have h' : LTreeList (merge_adj2 [] (t1 :: t2 :: ts')) := by
        have h0 : LTreeList ([] : List (LHeap α)) := by intro t ht; simp at ht
        exact ltreeList_merge_adj2 [] (t1 :: t2 :: ts') h0 h
      exact ih (merge_adj2 [] (t1 :: t2 :: ts')) hf' h'

theorem mset_merge_all2 [LinearOrder α] (ts : List (LHeap α)) :
  mset_tree (merge_all2 ts) = sumMSet ts := by
  unfold merge_all2
  apply mset_merge_all2Aux
  omega

theorem heap_merge_all2 [LinearOrder α] (ts : List (LHeap α)) (h : HeapList ts) :
  heap (merge_all2 ts) := by
  unfold merge_all2
  apply heap_merge_all2Aux
  · omega
  · exact h

theorem ltree_merge_all2 [LinearOrder α] (ts : List (LHeap α)) (h : LTreeList ts) :
  ltree (merge_all2 ts) := by
  unfold merge_all2
  apply ltree_merge_all2Aux
  · omega
  · exact h

end LHeap

open LHeap

/-- Graded theorem: correctness of lheap_list2 and complexity equivalence.
    Complexity model faithful to textbook: only merge calls counted. -/
theorem fdsa_chap15_ex04 {α : Type} [LinearOrder α] :
    (∀ xs : List α, (lheap_list2 xs).mset_tree = (xs : Multiset α)) ∧
    (∀ xs : List α, (lheap_list2 xs).heap) ∧
    (∀ xs : List α, (lheap_list2 xs).ltree) ∧
    (∀ (acc : List (LHeap α)) (ts : List (LHeap α)),
        T_merge_adj2 acc ts = T_merge_adj ts) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro xs
    unfold lheap_list2
    rw [mset_merge_all2]
    rw [sumMSet_map_singleton]
  · intro xs
    unfold lheap_list2
    apply heap_merge_all2
    exact heapList_map_singleton xs
  · intro xs
    unfold lheap_list2
    apply ltree_merge_all2
    exact ltreeList_map_singleton xs
  · intro acc ts
    exact T_merge_adj2_eq acc ts

namespace LHeap

variable {α : Type} [LinearOrder α]

/-- List construction preserves the entire input multiset, including duplicates. -/
theorem mset_lheap_list2 (xs : List α) :
    (lheap_list2 xs).mset_tree = (xs : Multiset α) :=
  fdsa_chap15_ex04.1 xs

/-- List construction satisfies min-heap ordering. -/
theorem heap_lheap_list2 (xs : List α) : (lheap_list2 xs).heap :=
  fdsa_chap15_ex04.2.1 xs

/-- List construction satisfies both stored-rank correctness and leftist balance. -/
theorem ltree_lheap_list2 (xs : List α) : (lheap_list2 xs).ltree :=
  fdsa_chap15_ex04.2.2.1 xs

/-- A reusable per-input form of the three construction-correctness conjuncts. -/
theorem lheap_list2_correct (xs : List α) :
    (lheap_list2 xs).mset_tree = (xs : Multiset α) ∧
    (lheap_list2 xs).heap ∧ (lheap_list2 xs).ltree :=
  ⟨mset_lheap_list2 xs, heap_lheap_list2 xs, ltree_lheap_list2 xs⟩

/-- The accumulator is a reversed prefix; newly merged pairs follow it in
input order. This additional output characterization is not required by the
original exercise. Append appears only in the specification, not the algorithm. -/
theorem merge_adj2_eq_reverse_append (acc ts : List (LHeap α)) :
    merge_adj2 acc ts = acc.reverse ++ merge_adj ts := by
  match ts with
  | [] => simp [merge_adj2, merge_adj]
  | [t] => simp [merge_adj2, merge_adj, List.reverse_cons]
  | t1 :: t2 :: ts' =>
    rw [merge_adj2, merge_adj2_eq_reverse_append (t1.merge t2 :: acc) ts']
    simp [merge_adj, List.reverse_cons, List.append_assoc]

end LHeap

end Cslib.Algorithms.Lean
