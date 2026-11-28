/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

/-!
# Priority queues via Braun trees, second implementation

An alternative deletion operation for Braun-tree priority queues,
following the AFP entry `Priority_Queue_Braun2`: `replaceMin` replaces
the root by a new element and restores the heap invariant with
`siftDown`, and `delMin2` deletes the minimum by dropping the root of
a node and merging its two children (`delMin2 (Node l _ r) = merge l
r`). `replaceMin` (on a Braun tree) is exactly `siftDown`
(`replaceMin_siftDown`).

`merge` merges two heaps into a heap containing both multisets
(`mset_merge`): it compares the roots, keeps the smaller root as the
new root, and merges the remainder. It drops no element: merging the
singleton heaps `1` and `2` retains both values. It does not preserve
`Braun` in general, but it preserves it when the arguments are the
children of a single Braun node (`braun_size_merge`), which is all
`delMin2` needs.

`delMin2` is correct (`braun_delMin2`, `heap_delMin2`,
`mset_delMin2`), and `pq_spec2` discharges the book's
priority-queue ADT a second time.

## Totality

Isabelle's `merge` is unspecified on `(Leaf, Node …)`; this file
totalises it as `merge Leaf r = r`. Isabelle's `replace_min` uses
`value Leaf` in its `else` branch when the left subtree is `Leaf`;
this file totalises the `Node Leaf` case as
`replaceMin x (Node Leaf _ r) = Node Leaf x r`. Both totalisations
are unreachable on the inputs the lemmas use (the `Braun` hypothesis
forces `l = Leaf → r = Leaf`), and no lemma depends on them. Note
Sorting's `merge` (in `BraunTree.Sorting`) is a *different* function
(classic heap merge); the two are distinguished by namespace
(`BraunTree.ReplaceMin.merge` vs `BraunTree.Sorting.merge`).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTree.ReplaceMin

open BraunTree





variable {α : Type u} [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α]

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- Root-irrelevance of `Braun`: `Braun (Node l a r)` does not mention
    the root `a`, so it is the same for any root. Used to feed
    induction hypotheses whose root differs from the goal's. -/
theorem braun_node_root_irrel {l r : BraunTree α} {a b : α} :
    Braun (BraunTree.Node l a r) ↔ Braun (BraunTree.Node l b r) :=
  Iff.rfl

/-- Isabelle's `le_root`: `a` is `≤` the root of `t`, vacuously true
    on the empty tree. -/
def leRoot (a : α) : BraunTree α → Bool
  | .Leaf => true
  | .Node _ b _ => decide (a ≤ b)

omit [DecidableLT α] [DecidableEq α] in
theorem leRoot_leaf (a : α) : leRoot a (BraunTree.Leaf : BraunTree α) = true := rfl

omit [DecidableLT α] [DecidableEq α] in
theorem leRoot_node (a b : α) (l r : BraunTree α) :
    leRoot a (BraunTree.Node l b r) = decide (a ≤ b) := rfl

/-- Isabelle's `replace_min`: replace the root of a tree by `x` and
    sift `x` down. The original root is discarded (hence `_` in the
    patterns). -/
def replaceMin (x : α) : BraunTree α → BraunTree α
  | .Leaf => BraunTree.Leaf
  | .Node .Leaf _ r => BraunTree.Node BraunTree.Leaf x r
  | .Node (.Node l₁ x₁ r₁) _ .Leaf =>
      if x ≤ x₁ then BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x BraunTree.Leaf
      else BraunTree.Node (replaceMin x (BraunTree.Node l₁ x₁ r₁)) x₁ BraunTree.Leaf
  | .Node (.Node l₁ x₁ r₁) _ (.Node l₂ x₂ r₂) =>
      if x ≤ x₁ && x ≤ x₂ then
        BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x (BraunTree.Node l₂ x₂ r₂)
      else if x₁ ≤ x₂ then
        BraunTree.Node (replaceMin x (BraunTree.Node l₁ x₁ r₁)) x₁ (BraunTree.Node l₂ x₂ r₂)
      else
        BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x₂ (replaceMin x (BraunTree.Node l₂ x₂ r₂))

omit [DecidableLT α] [DecidableEq α] in
omit [DecidableLT α] [DecidableEq α] in
/-- `replaceMin` ignores the original root: the patterns only
    match on the shapes of `l` and `r`. Proved by casing on those
    shapes; in each shape both sides have the same equation. -/
theorem replaceMin_root_irrel {x : α} {l r : BraunTree α} {a b : α} :
    replaceMin x (BraunTree.Node l a r) = replaceMin x (BraunTree.Node l b r) := by
  cases l with
  | Leaf => rfl
  | Node l₁ x₁ r₁ =>
      cases l₁ with
      | Leaf =>
          cases r with
          | Leaf => rfl
          | Node l₂ x₂ r₂ => rfl
      | Node l₁' x₁' r₁' =>
          cases r with
          | Leaf => rfl
          | Node l₂ x₂ r₂ => rfl

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `replace_min_sift_down`: `replaceMin` is just
    `siftDown` in disguise. -/
theorem replaceMin_siftDown {l : BraunTree α} {a : α} {r : BraunTree α} {x : α}
    (h : Braun (BraunTree.Node l a r)) :
    replaceMin x (BraunTree.Node l a r) = siftDown l x r := by
  induction l, x, r using siftDown.induct with
  | case1 x_elem r =>
      rw [braun_node] at h
      have hsize0 : size r = 0 := by
        have hb := h.1
        simp only [size] at hb
        omega
      have hr : r = BraunTree.Leaf := by
        cases r with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst hr
      simp [replaceMin, siftDown]
  | case2 x₀ a_sub x_elem hle =>
      rw [braun_node] at h
      have hsize0 : size a_sub = 0 := by
        have hb := h.1
        simp only [size] at hb
        omega
      have ha : a_sub = BraunTree.Leaf := by
        cases a_sub with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst ha
      simp [replaceMin, siftDown, hle]
  | case3 x₀ a_sub x_elem hle =>
      rw [braun_node] at h
      have hsize0 : size a_sub = 0 := by
        have hb := h.1
        simp only [size] at hb
        omega
      have ha : a_sub = BraunTree.Leaf := by
        cases a_sub with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst ha
      simp [replaceMin, siftDown, hle]
  | case4 l₁ x₁ r₁ x₂ r₂ a_elem hle =>
      rw [braun_node] at h
      exfalso
      have hb := h.1
      simp only [size] at hb
      omega
  | case5 l₁ x₁ r₁ x₂ r₂ a_elem hle ih =>
      rw [braun_node] at h
      exfalso
      have hb := h.1
      simp only [size] at hb
      omega
  | case6 l₁ x₁ r₁ a_elem l₂ x₂ r₂ hle =>
      -- `replaceMin` condition `x ≤ x₁ ∧ x ≤ x₂` holds, so both
      -- sides are `Node (Node l₁ x₁ r₁) a_elem (Node l₂ x₂ r₂)`.
      simp [replaceMin, siftDown, hle]
  | case7 l₁ x₁ r₁ a_elem l₂ x₂ r₂ hle h12 ih =>
      -- `replaceMin` takes the `else / x₁ ≤ x₂` branch, mirroring
      -- `siftDown`'s. The induction hypothesis is
      -- `replaceMin a_elem (Node l₁ a_elem r₁) = siftDown l₁ a_elem r₁`
      -- (with root `a_elem`); `replaceMin` ignores the root, so it
      -- also holds with root `x₁`.
      have hbraun1 : Braun (BraunTree.Node l₁ a_elem r₁) := by
        obtain ⟨_, hbl, _⟩ := h
        rw [braun_node] at hbl
        rw [braun_node]
        exact ⟨hbl.1, hbl.2.1, hbl.2.2⟩
      have hih := ih hbraun1
      have hroot : replaceMin a_elem (BraunTree.Node l₁ x₁ r₁) =
          siftDown l₁ a_elem r₁ := by rw [replaceMin_root_irrel]; exact hih
      simp [replaceMin, siftDown, hle, h12, hroot]
  | case8 l₁ x₁ r₁ a_elem l₂ x₂ r₂ hle h12 ih =>
      have hbraun2 : Braun (BraunTree.Node l₂ a_elem r₂) := by
        obtain ⟨_, _, hbr⟩ := h
        rw [braun_node] at hbr
        rw [braun_node]
        exact ⟨hbr.1, hbr.2.1, hbr.2.2⟩
      have hih := ih hbraun2
      have hroot : replaceMin a_elem (BraunTree.Node l₂ x₂ r₂) =
          siftDown l₂ a_elem r₂ := by rw [replaceMin_root_irrel]; exact hih
      simp [replaceMin, siftDown, hle, h12, hroot]

/-- Isabelle's `merge` for `delMin2`. -/
def merge : BraunTree α → BraunTree α → BraunTree α
  | .Leaf, r => r
  | .Node l₁ a₁ r₁, .Leaf => BraunTree.Node l₁ a₁ r₁
  | .Node l₁ a₁ r₁, .Node l₂ a₂ r₂ =>
      if a₁ ≤ a₂ then BraunTree.Node (BraunTree.Node l₂ a₂ r₂) a₁ (merge l₁ r₁)
      else match delLeft (BraunTree.Node l₁ a₁ r₁) with
           | some (x, l') => BraunTree.Node (replaceMin x (BraunTree.Node l₂ a₂ r₂)) a₂ l'
           | none => BraunTree.Node l₁ a₁ r₁

/-- Isabelle's `del_min2`. -/
def delMin2 : BraunTree α → BraunTree α
  | .Leaf => BraunTree.Leaf
  | .Node l _ r => merge l r


omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `mset_tree_merge`. -/
theorem mset_merge {l : BraunTree α} {a : α} {r : BraunTree α}
    (h : Braun (BraunTree.Node l a r)) :
    msetTree (merge l r) = msetTree l + msetTree r := by
  induction l, r using merge.induct with
  | case1 r =>
      rw [braun_node] at h
      have hsize0 : size r = 0 := by
        have hb := h.1
        simp only [size] at hb
        omega
      have hr : r = BraunTree.Leaf := by
        cases r with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst hr
      simp [merge, msetTree]
  | case2 l₁ a₁ r₁ =>
      simp [merge, msetTree]
  | case3 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      have hbraun1 : Braun (BraunTree.Node l₁ a r₁) := by
        obtain ⟨_, hbl, _⟩ := h
        exact braun_node_root_irrel.mp hbl
      have hih := ih hbraun1
      have hmerge : merge (BraunTree.Node l₁ a₁ r₁) (BraunTree.Node l₂ a₂ r₂)
          = BraunTree.Node (BraunTree.Node l₂ a₂ r₂) a₁ (merge l₁ r₁) := by
        simp [merge, hle]
      rw [hmerge]
      have m1 : msetTree (BraunTree.Node (BraunTree.Node l₂ a₂ r₂) a₁ (merge l₁ r₁))
          = {a₁} + msetTree (BraunTree.Node l₂ a₂ r₂) + msetTree (merge l₁ r₁) := rfl
      have m2 : msetTree (BraunTree.Node l₁ a₁ r₁)
          = {a₁} + msetTree l₁ + msetTree r₁ := rfl
      have m3 : msetTree (BraunTree.Node l₂ a₂ r₂)
          = {a₂} + msetTree l₂ + msetTree r₂ := rfl
      rw [m1, hih, m2, m3]
      ac_rfl
  | case4 l₁ a₁ r₁ l₂ a₂ r₂ hle x l' hdl =>
      have hbraun2 : Braun (BraunTree.Node l₂ a₂ r₂) := by
        obtain ⟨_, _, hbr⟩ := h
        exact hbr
      have hbraun2' : Braun (BraunTree.Node l₂ x r₂) :=
        braun_node_root_irrel.mp hbraun2
      have hrep : replaceMin x (BraunTree.Node l₂ a₂ r₂) = siftDown l₂ x r₂ :=
        replaceMin_siftDown hbraun2
      have hmerge : merge (BraunTree.Node l₁ a₁ r₁) (BraunTree.Node l₂ a₂ r₂)
          = BraunTree.Node (replaceMin x (BraunTree.Node l₂ a₂ r₂)) a₂ l' := by
        simp [merge, hle, hdl]
      have hdelm : msetTree (BraunTree.Node l₁ a₁ r₁) = {x} + msetTree l' :=
        delLeft_mset hdl
      have m1 : msetTree (BraunTree.Node (siftDown l₂ x r₂) a₂ l')
          = {a₂} + msetTree (siftDown l₂ x r₂) + msetTree l' := rfl
      rw [hmerge, hrep, m1, mset_siftDown hbraun2']
      have m2 : msetTree (BraunTree.Node l₁ a₁ r₁)
          = {a₁} + msetTree l₁ + msetTree r₁ := rfl
      have m3 : msetTree (BraunTree.Node l₂ a₂ r₂)
          = {a₂} + msetTree l₂ + msetTree r₂ := rfl
      rw [hdelm, m3]
      ac_rfl
  | case5 l₁ a₁ r₁ l₂ a₂ r₂ hle hdl =>
      obtain ⟨y, l'', hdl'⟩ := delLeft_some_of_ne_leaf
        (show (BraunTree.Node l₁ a₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
      rw [hdl'] at hdl
      contradiction

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `heap_merge`. -/
theorem heap_merge {l : BraunTree α} {a : α} {r : BraunTree α}
    (hbraun : Braun (BraunTree.Node l a r)) (hl : Heap l) (hr : Heap r) :
    Heap (merge l r) := by
  induction l, r using merge.induct with
  | case1 r =>
      rw [braun_node] at hbraun
      have hsize0 : size r = 0 := by
        have hb := hbraun.1
        simp only [size] at hb
        omega
      have hr0 : r = BraunTree.Leaf := by
        cases r with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst hr0
      exact hr
  | case2 l₁ a₁ r₁ =>
      exact hl
  | case3 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      have hbraun1 : Braun (BraunTree.Node l₁ a r₁) := by
        obtain ⟨_, hbl, _⟩ := hbraun
        exact braun_node_root_irrel.mp hbl
      have hhl : Heap (BraunTree.Node l₁ a₁ r₁) := hl
      rw [heap_node] at hhl
      obtain ⟨_, _, hhl1, hhr1⟩ := hhl
      have hih : Heap (merge l₁ r₁) := ih hbraun1 hhl1 hhr1
      have hmerge : merge (BraunTree.Node l₁ a₁ r₁) (BraunTree.Node l₂ a₂ r₂)
          = BraunTree.Node (BraunTree.Node l₂ a₂ r₂) a₁ (merge l₁ r₁) := by
        simp [merge, hle]
      rw [hmerge, heap_node]
      refine ⟨?_, ?_, hr, hih⟩
      · intro y hy
        exact le_trans hle (heap_root_le hr y hy)
      · intro y hy
        have hmem : y ∈ msetTree l₁ + msetTree r₁ := by
          have hm : msetTree (merge l₁ r₁) = msetTree l₁ + msetTree r₁ :=
            mset_merge hbraun1
          rw [← hm]
          exact hy
        simp only [Multiset.mem_add] at hmem
        rcases hmem with hy1 | hy1
        · exact heap_root_le hl y (by
            rw [show msetTree (BraunTree.Node l₁ a₁ r₁) = {a₁} + msetTree l₁ + msetTree r₁ from rfl]
            exact (Multiset.mem_add).mpr (Or.inl ((Multiset.mem_add).mpr (Or.inr hy1))))
        · exact heap_root_le hl y (by
            rw [show msetTree (BraunTree.Node l₁ a₁ r₁) = {a₁} + msetTree l₁ + msetTree r₁ from rfl]
            exact (Multiset.mem_add).mpr (Or.inr hy1))
  | case4 l₁ a₁ r₁ l₂ a₂ r₂ hle x l' hdl =>
      have hbraun2 : Braun (BraunTree.Node l₂ a₂ r₂) := by
        obtain ⟨_, _, hbr⟩ := hbraun
        exact hbr
      have hbraun2' : Braun (BraunTree.Node l₂ x r₂) :=
        braun_node_root_irrel.mp hbraun2
      have hrep : replaceMin x (BraunTree.Node l₂ a₂ r₂) = siftDown l₂ x r₂ :=
        replaceMin_siftDown hbraun2
      have hmerge : merge (BraunTree.Node l₁ a₁ r₁) (BraunTree.Node l₂ a₂ r₂)
          = BraunTree.Node (replaceMin x (BraunTree.Node l₂ a₂ r₂)) a₂ l' := by
        simp [merge, hle, hdl]
      rw [hmerge]
      have hhl : Heap (BraunTree.Node l₁ a₁ r₁) := hl
      rw [heap_node] at hhl
      obtain ⟨_, _, hhl1, hhr1⟩ := hhl
      have hhr : Heap (BraunTree.Node l₂ a₂ r₂) := hr
      rw [heap_node] at hhr
      obtain ⟨_, _, hhr1, hhr2⟩ := hhr
      have hrep_heap : Heap (replaceMin x (BraunTree.Node l₂ a₂ r₂)) := by
        rw [hrep]
        exact heap_siftDown hbraun2' hhr1 hhr2
      have hl'_heap : Heap l' := delLeft_heap hdl hl
      have hx : a₂ ≤ x := by
        have hmem : x ∈ msetTree (BraunTree.Node l₁ a₁ r₁) := by
          rw [delLeft_mset hdl]
          exact (Multiset.mem_add).mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
        have ha1x : a₁ ≤ x := heap_root_le hl x hmem
        exact le_trans (le_of_lt (lt_of_not_ge hle)) ha1x
      rw [heap_node]
      refine ⟨?_, ?_, hrep_heap, hl'_heap⟩
      · intro y hy
        rw [hrep, mset_siftDown hbraun2'] at hy
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hy
        rcases hy with rfl | (hy | hy)
        · exact hx
        · exact heap_root_le hr y (by
            rw [show msetTree (BraunTree.Node l₂ a₂ r₂) = {a₂} + msetTree l₂ + msetTree r₂ from rfl]
            exact (Multiset.mem_add).mpr (Or.inl ((Multiset.mem_add).mpr (Or.inr hy))))
        · exact heap_root_le hr y (by
            rw [show msetTree (BraunTree.Node l₂ a₂ r₂) = {a₂} + msetTree l₂ + msetTree r₂ from rfl]
            exact (Multiset.mem_add).mpr (Or.inr hy))
      · intro y hy
        have hy_in : y ∈ msetTree (BraunTree.Node l₁ a₁ r₁) := by
          rw [delLeft_mset hdl]
          exact (Multiset.mem_add).mpr (Or.inr hy)
        exact le_trans (le_of_lt (lt_of_not_ge hle)) (heap_root_le hl y hy_in)
  | case5 l₁ a₁ r₁ l₂ a₂ r₂ hle hdl =>
      obtain ⟨y, l'', hdl'⟩ := delLeft_some_of_ne_leaf
        (show (BraunTree.Node l₁ a₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
      rw [hdl'] at hdl
      contradiction

omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
omit [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `del_left_braun_size`: `delLeft` preserves `Braun` and
    removes exactly one element. The AFP's `t ≠ Leaf` hypothesis is
    redundant here, since `delLeft t = some …` already implies it. -/
theorem delLeft_braun_size {t : BraunTree α} {x : α} {t' : BraunTree α}
    (h : delLeft t = some (x, t')) (ht : Braun t) :
    Braun t' ∧ size t = size t' + 1 :=
  ⟨delLeft_braun h ht, delLeft_size h⟩

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `braun_size_merge`. -/
theorem braun_size_merge {l : BraunTree α} {a : α} {r : BraunTree α}
    (h : Braun (BraunTree.Node l a r)) :
    Braun (merge l r) ∧ size (merge l r) = size l + size r := by
  induction l, r using merge.induct with
  | case1 r =>
      rw [braun_node] at h
      have hsize0 : size r = 0 := by
        have hb := h.1
        simp only [size] at hb
        omega
      have hr : r = BraunTree.Leaf := by
        cases r with
        | Leaf => rfl
        | Node l' y r' => simp [size] at hsize0
      subst hr
      exact ⟨trivial, by simp [merge, size]⟩
  | case2 l₁ a₁ r₁ =>
      obtain ⟨_, hbl, _⟩ := h
      exact ⟨hbl, by simp [merge, size]⟩
  | case3 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      obtain ⟨hsize, hbl, hbr⟩ := h
      have hbraun1 : Braun (BraunTree.Node l₁ a r₁) := braun_node_root_irrel.mp hbl
      obtain ⟨ihbraun, ihsize⟩ := ih hbraun1
      have hmerge : merge (BraunTree.Node l₁ a₁ r₁) (BraunTree.Node l₂ a₂ r₂)
          = BraunTree.Node (BraunTree.Node l₂ a₂ r₂) a₁ (merge l₁ r₁) := by
        simp [merge, hle]
      rw [hmerge]
      constructor
      · rw [braun_node]
        refine ⟨?_, hbr, ihbraun⟩
        have h1 : size (BraunTree.Node l₂ a₂ r₂) = size l₂ + size r₂ + 1 := rfl
        have h2 : size (merge l₁ r₁) = size l₁ + size r₁ := ihsize
        have h3 : size (BraunTree.Node l₁ a₁ r₁) = size l₁ + size r₁ + 1 := rfl
        have h4 : size (BraunTree.Node l₂ a₂ r₂) = size l₂ + size r₂ + 1 := rfl
        rcases hsize with hs | hs <;> omega
      · have h1 : size (BraunTree.Node (BraunTree.Node l₂ a₂ r₂) a₁ (merge l₁ r₁))
            = size (BraunTree.Node l₂ a₂ r₂) + size (merge l₁ r₁) + 1 := rfl
        have h2 : size (BraunTree.Node l₂ a₂ r₂) = size l₂ + size r₂ + 1 := rfl
        have h3 : size (BraunTree.Node l₁ a₁ r₁) = size l₁ + size r₁ + 1 := rfl
        omega
  | case4 l₁ a₁ r₁ l₂ a₂ r₂ hle x l' hdl =>
      obtain ⟨hsize, hbl, hbr⟩ := h
      have hbraun2 : Braun (BraunTree.Node l₂ a₂ r₂) := hbr
      have hbraun2' : Braun (BraunTree.Node l₂ x r₂) :=
        braun_node_root_irrel.mp hbraun2
      have hrep : replaceMin x (BraunTree.Node l₂ a₂ r₂) = siftDown l₂ x r₂ :=
        replaceMin_siftDown hbraun2
      have hmerge : merge (BraunTree.Node l₁ a₁ r₁) (BraunTree.Node l₂ a₂ r₂)
          = BraunTree.Node (replaceMin x (BraunTree.Node l₂ a₂ r₂)) a₂ l' := by
        simp [merge, hle, hdl]
      rw [hmerge]
      constructor
      · rw [braun_node]
        refine ⟨?_, ?_, delLeft_braun hdl hbl⟩
        · have h1 : size (replaceMin x (BraunTree.Node l₂ a₂ r₂))
              = size l₂ + size r₂ + 1 := by
            rw [hrep, size_siftDown hbraun2']
          have h2 : size l' + 1 = size (BraunTree.Node l₁ a₁ r₁) := by
            rw [← delLeft_size hdl]
          have h3 : size (BraunTree.Node l₁ a₁ r₁) = size l₁ + size r₁ + 1 := rfl
          have h4 : size (BraunTree.Node l₂ a₂ r₂) = size l₂ + size r₂ + 1 := rfl
          rcases hsize with hs | hs <;> omega
        · rw [hrep]
          exact braun_siftDown hbraun2'
      · have h1 : size (BraunTree.Node (replaceMin x (BraunTree.Node l₂ a₂ r₂)) a₂ l')
            = size (replaceMin x (BraunTree.Node l₂ a₂ r₂)) + size l' + 1 := rfl
        have h2 : size (replaceMin x (BraunTree.Node l₂ a₂ r₂))
            = size l₂ + size r₂ + 1 := by
          rw [hrep, size_siftDown hbraun2']
        have h3 : size l' + 1 = size (BraunTree.Node l₁ a₁ r₁) := by
          rw [← delLeft_size hdl]
        have h4 : size (BraunTree.Node l₁ a₁ r₁) = size l₁ + size r₁ + 1 := rfl
        have h5 : size (BraunTree.Node l₂ a₂ r₂) = size l₂ + size r₂ + 1 := rfl
        omega
  | case5 l₁ a₁ r₁ l₂ a₂ r₂ hle hdl =>
      obtain ⟨y, l'', hdl'⟩ := delLeft_some_of_ne_leaf
        (show (BraunTree.Node l₁ a₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
      rw [hdl'] at hdl
      contradiction

omit [DecidableLT α] [DecidableEq α] in
/-- Second deletion: `delMin2` preserves `Braun`. -/
theorem braun_delMin2 {t : BraunTree α} (ht : Braun t) : Braun (delMin2 t) := by
  cases t with
  | Leaf => exact trivial
  | Node l c r => exact (braun_size_merge ht).1

omit [DecidableLT α] [DecidableEq α] in
/-- Second deletion: `delMin2` preserves `Heap`. -/
theorem heap_delMin2 {t : BraunTree α} (hheap : Heap t) (hbraun : Braun t) :
    Heap (delMin2 t) := by
  cases t with
  | Leaf => exact trivial
  | Node l c r =>
      rw [heap_node] at hheap
      obtain ⟨_, _, hhl, hhr⟩ := hheap
      exact heap_merge hbraun hhl hhr

omit [DecidableLT α] in
/-- Second deletion: `delMin2` removes the minimum, in `Node` form. -/
theorem mset_delMin2 {l : BraunTree α} {a : α} {r : BraunTree α}
    (hbraun : Braun (BraunTree.Node l a r)) :
    msetTree (delMin2 (BraunTree.Node l a r)) =
      msetTree (BraunTree.Node l a r) - {a} := by
  have hm : msetTree (merge l r) = msetTree l + msetTree r := mset_merge hbraun
  have h1 : msetTree (BraunTree.Node l a r) = {a} + msetTree l + msetTree r := rfl
  change msetTree (merge l r) = msetTree (BraunTree.Node l a r) - {a}
  rw [hm, h1]
  rw [show ({a} + msetTree l + msetTree r) = {a} + (msetTree l + msetTree r) from by ac_rfl]
  rw [add_tsub_cancel_left]

/-- The second priority-queue interpretation (AFP `interpretation braun`
    in `Braun2`), with `delMin` replaced by `delMin2`; includes the
    `isEmpty` emptiness test. -/
theorem pq_spec2 :
    msetTree (BraunTree.Leaf : BraunTree α) = 0 ∧
    (Braun (BraunTree.Leaf : BraunTree α) ∧ Heap (BraunTree.Leaf : BraunTree α)) ∧
    (∀ (a : α) (t : BraunTree α), Braun t ∧ Heap t →
      msetTree (insert a t) = {a} + msetTree t ∧
      Braun (insert a t) ∧ Heap (insert a t)) ∧
    (∀ (l : BraunTree α) (a : α) (r : BraunTree α),
      Braun (BraunTree.Node l a r) ∧ Heap (BraunTree.Node l a r) →
      msetTree (delMin2 (BraunTree.Node l a r)) = msetTree (BraunTree.Node l a r) - {a} ∧
      Braun (delMin2 (BraunTree.Node l a r)) ∧ Heap (delMin2 (BraunTree.Node l a r))) ∧
    (∀ (t : BraunTree α), Braun t ∧ Heap t → msetTree t ≠ 0 →
      getMin t = Min_mset (msetTree t)) ∧
    (∀ (l : BraunTree α) (a : α) (r : BraunTree α), Heap (BraunTree.Node l a r) →
      ∀ y ∈ msetTree (BraunTree.Node l a r), a ≤ y) ∧
    (∀ (t : BraunTree α), isEmpty t = true ↔ msetTree t = 0) := by
  refine ⟨rfl, ⟨trivial, trivial⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro a t h
    exact ⟨mset_insert a t, braun_insert a h.1, heap_insert a h.2⟩
  · intro l a r h
    exact ⟨mset_delMin2 h.1, braun_delMin2 h.1, heap_delMin2 h.2 h.1⟩
  · intro t h hm
    exact getMin_eq_Min_mset h.2 (by
      intro hleaf; subst hleaf; simp [msetTree] at hm)
  · intro l a r h y hy
    exact heap_root_le h y hy
  · intro t
    exact isEmpty_iff_mset_eq_zero t

end Cslib.Algorithms.Lean.BraunTree.ReplaceMin
