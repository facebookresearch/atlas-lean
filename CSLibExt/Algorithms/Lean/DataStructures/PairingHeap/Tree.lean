/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.PriorityQueue
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic

/-!
# Pairing heaps: Fredman et al.'s original binary-tree version (`Pairing_Heap_Tree`)

Heaps *are* binary trees (book Chapter 4's `tree`): `del_min` and
`merge` are only specified for arguments that are roots
(`node _ _ leaf`) and are totalized here, as in the AFP. Includes the
functional-correctness proof and the `Priority_Queue_Merge`
specification in the locale's and the book's forms. The amortized
analysis (the simplified treatment: `len`, the `ΔΦ` lemmas, the `T_*`
functions, the `A_*` bounds, and the `Amortized` instantiation) lives
in `PairingHeap.Amortized`.

`getMin` is `Option`-valued: the book's `get_min` is partial on the
empty heap.

Ported from the Chapter 23 Lean conversion in
`converted_proofs/ch23/lean/Chapter23.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Pairing_Heap`
(`Pairing_Heap_Tree.thy`) and `Amortized_Complexity`
(`Pairing_Heap_Tree_Analysis2.thy`), and Tobias Nipkow (ed.),
*Functional Data Structures and Algorithms: A Proof Assistant Approach*,
Chapter 23 (Pairing Heaps, pp. 257–264). Isabelle-derived names are kept
for traceability to those sources.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace PairingHeap
namespace Tree

variable {α : Type u}

/-- Binary trees, the book's `'a tree` (Chapter 4): `leaf` is `⟨⟩`,
`node l a r` is `⟨l; a; r⟩`. -/
inductive BTree (α : Type u) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α
deriving DecidableEq

/-- The standard size function on binary trees (Chapter 4:
`|hi| = 0`, `|⟨l; _; r⟩| = |l| + |r| + 1`). -/
def sizeTree : BTree α → ℕ
  | .leaf => 0
  | .node l _ r => sizeTree l + sizeTree r + 1

theorem sizeTree_leaf : sizeTree (BTree.leaf : BTree α) = 0 := rfl

theorem sizeTree_node (l r : BTree α) (x : α) :
    sizeTree (BTree.node l x r) = sizeTree l + sizeTree r + 1 := rfl

/-- Strong induction on binary trees, by `sizeTree`. `Tree` is a simple
inductive type, so plain `induction` works for recursions that go to
immediate subtrees; but `pass1` recurses to a *grandchild*, so its proofs
need this strong principle. -/
theorem BTree_ind {P : BTree α → Prop}
    (step : ∀ t : BTree α, (∀ s : BTree α, sizeTree s < sizeTree t → P s) → P t)
    (t : BTree α) : P t := by
  have key : ∀ n : ℕ, ∀ t : BTree α, sizeTree t ≤ n → P t := by
    intro n
    induction n with
    | zero =>
      intro t hh
      apply step
      intro s hlt
      omega
    | succ n ih =>
      intro t hh
      apply step
      intro s hlt
      apply ih
      omega
  exact key (sizeTree t) t le_rfl

/-- The set of elements of a binary tree (Chapter 14's `set_tree`). -/
def setTree : BTree α → Set α
  | .leaf => ∅
  | .node l x r => {x} ∪ setTree l ∪ setTree r

theorem setTree_leaf : setTree (BTree.leaf : BTree α) = ∅ := by
  simp [setTree]

theorem setTree_node (l r : BTree α) (x : α) :
    setTree (BTree.node l x r) = {x} ∪ setTree l ∪ setTree r := by
  simp [setTree]

/-- The multiset of elements of a binary tree (Chapter 14's `mset_tree`). -/
def msetTree : BTree α → Multiset α
  | .leaf => 0
  | .node l x r => {x} + msetTree l + msetTree r

theorem msetTree_leaf : msetTree (BTree.leaf : BTree α) = 0 := by
  simp [msetTree]

theorem msetTree_node (l r : BTree α) (x : α) :
    msetTree (BTree.node l x r) = {x} + msetTree l + msetTree r := by
  simp [msetTree]

/-- Membership in the multiset is membership in the set (Chapter 14). -/
theorem msetTree_mem {y : α} {t : BTree α} :
    y ∈ msetTree t ↔ y ∈ setTree t := by
  induction t with
  | leaf => simp [msetTree, setTree]
  | node l x r ihl ihr =>
    simp only [msetTree, Multiset.mem_add, Multiset.mem_singleton,
      setTree, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ((rfl | hy) | hy)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (ihl.mp hy))
      · exact Or.inr (ihr.mp hy)
    · rintro ((rfl | hy) | hy)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (ihl.mpr hy))
      · exact Or.inr (ihr.mpr hy)

/-- `mset_tree t = 0 ↔ t = leaf` (used for the `Priority_Queue`
interpretation). -/
theorem msetTree_eq_zero_iff (t : BTree α) :
    msetTree t = 0 ↔ t = BTree.leaf := by
  cases t with
  | leaf => simp [msetTree_leaf]
  | node l x r =>
    constructor
    · intro hcontra
      have hc := congrArg Multiset.card hcontra
      simp only [msetTree_node, Multiset.card_add, Multiset.card_singleton,
        Multiset.card_zero] at hc
      omega
    · intro hcontra
      simp at hcontra

/-- `get_min` (Tree version): partial on `leaf`, totalized to `Option`. -/
def getMin : BTree α → Option α
  | .leaf => none
  | .node _ x _ => some x

theorem getMin_leaf : getMin (BTree.leaf : BTree α) = none := rfl

theorem getMin_node (l r : BTree α) (x : α) :
    getMin (BTree.node l x r) = some x := rfl

/-- AFP `get_min_in`, multiset form (the AFP states the set form; see
`getMin_mem_set`). -/
theorem getMin_mem (t : BTree α) (x : α) (hx : getMin t = some x) :
    x ∈ msetTree t := by
  cases t with
  | leaf => simp [getMin_leaf] at hx
  | node l y r =>
    simp only [getMin_node, Option.some.injEq] at hx
    subst hx
    simp [msetTree_node]

/-- AFP `get_min_in`: `get_min h ∈ set_tree h`. -/
theorem getMin_mem_set (t : BTree α) (x : α) (hx : getMin t = some x) :
    x ∈ setTree t :=
  msetTree_mem.mp (getMin_mem t x hx)

/-- `is_root` (Tree version): a root has `leaf` as its right child. -/
def isRoot : BTree α → Prop
  | .leaf => True
  | .node _ _ r => r = .leaf

theorem isRoot_leaf : isRoot (BTree.leaf : BTree α) ↔ True := Iff.rfl

theorem isRoot_node (l r : BTree α) (x : α) :
    isRoot (BTree.node l x r) ↔ r = .leaf := Iff.rfl

/-- `is_empty` of the `Priority_Queue` locale for the Tree variant:
`λh. h = leaf` in the AFP interpretation. -/
def isEmpty : BTree α → Prop := fun t => t = BTree.leaf

/-! ### Operations -/

/-- `link` (Tree version): links a pair of heaps encoded as
`node hsx x (node hsy y hs)`. -/
def link [LinearOrder α] : BTree α → BTree α
  | .node hsx x (.node hsy y hs) =>
    if x < y then .node (.node hsy y hsx) x hs else .node (.node hsx x hsy) y hs
  | t => t

theorem link_eq_pos [LinearOrder α] {hsx hsy hs : BTree α} {x y : α} (h : x < y) :
    link (.node hsx x (.node hsy y hs)) =
      .node (.node hsy y hsx) x hs := by simp [link, h]

theorem link_eq_neg [LinearOrder α] {hsx hsy hs : BTree α} {x y : α} (h : ¬ x < y) :
    link (.node hsx x (.node hsy y hs)) =
      .node (.node hsx x hsy) y hs := by simp [link, h]

theorem link_leaf [LinearOrder α] : link (BTree.leaf : BTree α) = BTree.leaf := rfl

theorem link_node_leaf [LinearOrder α] (l : BTree α) (x : α) :
    link (.node l x .leaf) = .node l x .leaf := rfl

/-- AFP `link_struct`: `link` of a two-level node keeps the right spine. -/
theorem link_struct [LinearOrder α] {hsx hsy hs : BTree α} {x y : α} :
    ∃ l a, link (.node hsx x (.node hsy y hs)) = .node l a hs := by
  by_cases hc : x < y
  · exact ⟨.node hsy y hsx, x, link_eq_pos hc⟩
  · exact ⟨.node hsx x hsy, y, link_eq_neg hc⟩

/-- `pass1` (Tree version). -/
def pass1 [LinearOrder α] : BTree α → BTree α
  | .node hsx x (.node hsy y hs) => link (.node hsx x (.node hsy y (pass1 hs)))
  | t => t

theorem pass1_leaf [LinearOrder α] : pass1 (BTree.leaf : BTree α) = BTree.leaf := rfl

theorem pass1_node_leaf [LinearOrder α] (l : BTree α) (x : α) :
    pass1 (.node l x .leaf) = .node l x .leaf := rfl

theorem pass1_cons2 [LinearOrder α] (hsx hsy hs : BTree α) (x y : α) :
    pass1 (.node hsx x (.node hsy y hs)) =
      link (.node hsx x (.node hsy y (pass1 hs))) := rfl

/-- AFP `pass1_struct`. -/
theorem pass1_struct [LinearOrder α] {hs1 : BTree α} (x : α) (hs : BTree α) :
    ∃ l a r, pass1 (.node hs1 x hs) = .node l a r := by
  cases hs with
  | leaf => exact ⟨hs1, x, BTree.leaf, pass1_node_leaf hs1 x⟩
  | node hsy y hs' =>
    rw [pass1_cons2]
    obtain ⟨l, a, h⟩ := link_struct (hsx := hs1) (x := x) (hsy := hsy) (y := y)
      (hs := pass1 hs')
    exact ⟨l, a, pass1 hs', h⟩

/-- `pass2` (Tree version). -/
def pass2 [LinearOrder α] : BTree α → BTree α
  | .node hsx x hs => link (.node hsx x (pass2 hs))
  | .leaf => .leaf

theorem pass2_leaf [LinearOrder α] : pass2 (BTree.leaf : BTree α) = BTree.leaf := rfl

theorem pass2_cons [LinearOrder α] (hsx hs : BTree α) (x : α) :
    pass2 (.node hsx x hs) = link (.node hsx x (pass2 hs)) := rfl

/-- AFP `pass2_struct`: `pass2` of a node is a root. -/
theorem pass2_struct [LinearOrder α] {hs1 : BTree α} (x : α) (hs : BTree α) :
    ∃ l a, pass2 (.node hs1 x hs) = .node l a .leaf := by
  induction hs generalizing hs1 x with
  | leaf =>
    rw [pass2_cons, pass2_leaf]
    exact ⟨hs1, x, link_node_leaf hs1 x⟩
  | node hsy y hs' _ ih =>
    rw [pass2_cons]
    obtain ⟨l, a, h⟩ := ih (hs1 := hsy) y
    rw [h]
    by_cases hc : x < a
    · rw [link_eq_pos hc]
      exact ⟨.node l a hs1, x, rfl⟩
    · rw [link_eq_neg hc]
      exact ⟨.node hs1 x l, a, rfl⟩

/-- `del_min` (Tree version). -/
def delMin [LinearOrder α] : BTree α → BTree α
  | .leaf => .leaf
  | .node hs _ _ => pass2 (pass1 hs)

theorem delMin_leaf [LinearOrder α] : delMin (BTree.leaf : BTree α) = BTree.leaf := rfl

theorem delMin_node [LinearOrder α] (hs : BTree α) (x : α) (r : BTree α) :
    delMin (.node hs x r) = pass2 (pass1 hs) := rfl

/-- `merge` (Tree version). -/
def merge [LinearOrder α] : BTree α → BTree α → BTree α
  | .leaf, hp => hp
  | hp, .leaf => hp
  | .node hsx x _, .node hsy y _ => link (.node hsx x (.node hsy y .leaf))

theorem merge_leaf_left [LinearOrder α] (hp : BTree α) : merge .leaf hp = hp := rfl

theorem merge_leaf_right [LinearOrder α] (hp : BTree α) : merge hp .leaf = hp := by
  cases hp <;> rfl

theorem merge_node_node [LinearOrder α] (hsx hsy : BTree α) (x y : α) (r1 r2 : BTree α) :
    merge (.node hsx x r1) (.node hsy y r2) =
      link (.node hsx x (.node hsy y .leaf)) := rfl

/-- `insert` (Tree version). -/
def insert [LinearOrder α] (x : α) : BTree α → BTree α
  | hp => merge (.node .leaf x .leaf) hp

theorem insert_eq [LinearOrder α] (x : α) (hp : BTree α) :
    insert x hp = merge (.node .leaf x .leaf) hp := rfl

/-- `pheap` (Tree version): the heap property on binary trees. -/
def pheap [LinearOrder α] : BTree α → Prop
  | .leaf => True
  | .node l x r => (∀ y ∈ setTree l, x ≤ y) ∧ pheap l ∧ pheap r

theorem pheap_leaf [LinearOrder α] : pheap (BTree.leaf : BTree α) ↔ True := by
  simp [pheap]

theorem pheap_node [LinearOrder α] (l r : BTree α) (x : α) :
    pheap (.node l x r) ↔ (∀ y ∈ setTree l, x ≤ y) ∧ pheap l ∧ pheap r := by
  simp [pheap]

/-- AFP `is_root_merge`. -/
theorem isRoot_merge [LinearOrder α] {h1 h2 : BTree α} (h1r : isRoot h1)
    (h2r : isRoot h2) : isRoot (merge h1 h2) := by
  cases h1 with
  | leaf => rw [merge_leaf_left]; exact h2r
  | node hsx x rx =>
    cases h2 with
    | leaf => rw [merge_leaf_right]; exact h1r
    | node hsy y ry =>
      rw [merge_node_node]
      obtain ⟨l, a, h⟩ := link_struct (hsx := hsx) (x := x) (hsy := hsy) (y := y)
        (hs := BTree.leaf)
      rw [h]
      simp [isRoot]

/-- AFP `is_root_insert`. -/
theorem isRoot_insert [LinearOrder α] {x : α} {h : BTree α} (hr : isRoot h) :
    isRoot (insert x h) := by
  rw [insert_eq]
  cases h with
  | leaf =>
    rw [merge_leaf_right]
    simp [isRoot]
  | node hs y ry =>
    rw [merge_node_node]
    obtain ⟨l, a, h⟩ := link_struct (hsx := BTree.leaf) (x := x) (hsy := hs) (y := y)
      (hs := BTree.leaf)
    rw [h]
    simp [isRoot]

/-- AFP `is_root_del_min`. -/
theorem isRoot_delMin [LinearOrder α] {h : BTree α} (hr : isRoot h) :
    isRoot (delMin h) := by
  cases h with
  | leaf =>
    rw [delMin_leaf]
    simp [isRoot]
  | node hs x rx =>
    rw [isRoot_node] at hr
    subst hr
    rw [delMin_node]
    cases hs with
    | leaf =>
      rw [pass1_leaf, pass2_leaf]
      simp [isRoot]
    | node ly y ry =>
      obtain ⟨la, a, ra, hpass1⟩ := pass1_struct (hs1 := ly) (x := y) (hs := ry)
      rw [hpass1]
      obtain ⟨lb, b, hpass2⟩ := pass2_struct (hs1 := la) (x := a) (hs := ra)
      rw [hpass2]
      simp [isRoot]

/-- AFP `pheap_link`. -/
theorem pheap_link [LinearOrder α] {t : BTree α} (hne : t ≠ .leaf) (hp : pheap t) :
    pheap (link t) := by
  cases t with
  | leaf => exact absurd rfl hne
  | node hsx x hs =>
    cases hs with
    | leaf =>
      rw [link_node_leaf]
      exact hp
    | node hsy y hs' =>
      by_cases hc : x < y
      · rw [link_eq_pos hc]
        rw [pheap_node, pheap_node] at hp ⊢
        obtain ⟨hA, hpsx, hB, hpsy, hps'⟩ := hp
        refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
        · intro z hz
          rw [setTree_node] at hz
          simp only [Set.mem_union, Set.mem_singleton_iff] at hz
          rcases hz with (rfl | hz) | hz
          · exact le_of_lt hc
          · exact le_trans (le_of_lt hc) (hB z hz)
          · exact hA z hz
        · intro z hz
          exact hB z hz
        · exact hpsy
        · exact hpsx
        · exact hps'
      · rw [link_eq_neg hc]
        have hyx : y ≤ x := le_of_not_gt hc
        rw [pheap_node, pheap_node] at hp ⊢
        obtain ⟨hA, hpsx, hB, hpsy, hps'⟩ := hp
        refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
        · intro z hz
          rw [setTree_node] at hz
          simp only [Set.mem_union, Set.mem_singleton_iff] at hz
          rcases hz with (rfl | hz) | hz
          · exact hyx
          · exact le_trans hyx (hA z hz)
          · exact hB z hz
        · intro z hz
          exact hA z hz
        · exact hpsx
        · exact hpsy
        · exact hps'

/-- AFP `pheap_pass1` (by strong induction: `pass1` recurses to a grandchild). -/
theorem pheap_pass1 [LinearOrder α] {t : BTree α} (hp : pheap t) :
    pheap (pass1 t) := by
  induction t using BTree_ind with
  | step t ih =>
    cases t with
    | leaf =>
      rw [pass1_leaf]
      exact hp
    | node l x r =>
      cases r with
      | leaf =>
        rw [pass1_node_leaf]
        exact hp
      | node m y r' =>
        rw [pass1_cons2]
        apply pheap_link (by simp)
        rw [pheap_node, pheap_node] at hp ⊢
        obtain ⟨hA, hpl, hB, hpm, hpr'⟩ := hp
        have hlt : sizeTree r' < sizeTree (BTree.node l x (BTree.node m y r')) := by
          rw [sizeTree_node, sizeTree_node]; omega
        have hpass := ih r' hlt hpr'
        exact ⟨hA, hpl, hB, hpm, hpass⟩

/-- AFP `pheap_pass2`. -/
theorem pheap_pass2 [LinearOrder α] {t : BTree α} (hp : pheap t) :
    pheap (pass2 t) := by
  induction t with
  | leaf => exact hp
  | node l x r ihl ihr =>
    rw [pass2_cons]
    apply pheap_link (by simp)
    rw [pheap_node] at hp ⊢
    obtain ⟨hA, hpl, hpr⟩ := hp
    exact ⟨hA, hpl, ihr hpr⟩

/-- AFP `pheap_del_min`. -/
theorem pheap_delMin [LinearOrder α] {t : BTree α} (hr : isRoot t) (hp : pheap t) :
    pheap (delMin t) := by
  cases t with
  | leaf =>
    rw [delMin_leaf]
    exact hp
  | node hs x rx =>
    rw [isRoot_node] at hr
    subst hr
    rw [delMin_node]
    rw [pheap_node] at hp
    exact pheap_pass2 (pheap_pass1 hp.2.1)

/-- AFP `pheap_merge`. -/
theorem pheap_merge [LinearOrder α] {h1 h2 : BTree α} (h1r : isRoot h1)
    (h2r : isRoot h2) (h1p : pheap h1) (h2p : pheap h2) :
    pheap (merge h1 h2) := by
  cases h1 with
  | leaf =>
    rw [merge_leaf_left]
    exact h2p
  | node hsx x rx =>
    cases h2 with
    | leaf =>
      rw [merge_leaf_right]
      exact h1p
    | node hsy y ry =>
      rw [isRoot_node] at h1r h2r
      subst h1r
      subst h2r
      rw [merge_node_node]
      apply pheap_link (by simp)
      rw [pheap_node] at h1p ⊢
      exact ⟨h1p.1, h1p.2.1, h2p⟩

/-- AFP `pheap_insert`. -/
theorem pheap_singleton [LinearOrder α] (x : α) : pheap (.node .leaf x .leaf) := by
  simp [pheap, setTree]

theorem pheap_insert [LinearOrder α] {x : α} {h : BTree α} (hr : isRoot h)
    (hp : pheap h) : pheap (insert x h) :=
  pheap_merge (by simp [isRoot]) hr (pheap_singleton x) hp

/-! ### Correctness: `getMin` lemmas -/

/-- AFP `get_min_min`. -/
theorem getMin_le [LinearOrder α] (t : BTree α) (x y : α) (hx : getMin t = some x)
    (hr : isRoot t) (hp : pheap t) (hy : y ∈ setTree t) : x ≤ y := by
  cases t with
  | leaf => simp [getMin_leaf] at hx
  | node l z r =>
    rw [isRoot_node] at hr
    subst hr
    simp only [getMin_node, Option.some.injEq] at hx
    subst hx
    rw [pheap_node] at hp
    rw [setTree_node, setTree_leaf] at hy
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      or_false] at hy
    rcases hy with rfl | hy
    · exact le_refl _
    · exact hp.1 y hy

/-- The `IsLeast` form of the AFP's `get_min` lemma
(`get_min h = Min_mset (mset_heap h)`). -/
theorem getMin_isLeast [LinearOrder α] (t : BTree α) (x : α)
    (hx : getMin t = some x) (hr : isRoot t) (hp : pheap t) :
    IsLeast {y | y ∈ msetTree t} x := by
  refine ⟨getMin_mem t x hx, ?_⟩
  intro y hy
  exact getMin_le t x y hx hr hp (msetTree_mem.mp hy)

/-- `getMin` is defined on every nonempty tree: the definedness clause
of the `Priority_Queue_Merge` specifications. -/
theorem getMin_defined (t : BTree α) (hne : msetTree t ≠ 0) :
    ∃ x, getMin t = some x := by
  cases t with
  | leaf => simp [msetTree] at hne
  | node l x r => exact ⟨x, rfl⟩

/-! ### Correctness: multiset lemmas -/

/-- AFP `mset_link`. -/
theorem mset_link [LinearOrder α] (t : BTree α) :
    msetTree (link t) = msetTree t := by
  cases t with
  | leaf => rfl
  | node hsx x hs =>
    cases hs with
    | leaf => rfl
    | node hsy y hs' =>
      by_cases hc : x < y
      · rw [link_eq_pos hc]
        simp only [msetTree_node]
        ac_rfl
      · rw [link_eq_neg hc]
        simp only [msetTree_node]
        ac_rfl

/-- AFP `mset_pass1`. -/
theorem mset_pass1 [LinearOrder α] (t : BTree α) :
    msetTree (pass1 t) = msetTree t := by
  induction t using BTree_ind with
  | step t ih =>
    cases t with
    | leaf => rfl
    | node l x r =>
      cases r with
      | leaf => rfl
      | node m y r' =>
        rw [pass1_cons2, mset_link]
        have hlt : sizeTree r' < sizeTree (BTree.node l x (BTree.node m y r')) := by
          rw [sizeTree_node, sizeTree_node]; omega
        simp only [msetTree_node]
        rw [ih r' hlt]

/-- AFP `mset_pass2`. -/
theorem mset_pass2 [LinearOrder α] (t : BTree α) :
    msetTree (pass2 t) = msetTree t := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    rw [pass2_cons, mset_link]
    simp only [msetTree_node]
    rw [ihr]

/-- AFP `mset_merge`. -/
theorem mset_merge [LinearOrder α] {h1 h2 : BTree α} (h1r : isRoot h1)
    (h2r : isRoot h2) : msetTree (merge h1 h2) = msetTree h1 + msetTree h2 := by
  cases h1 with
  | leaf =>
    rw [merge_leaf_left]
    simp [msetTree_leaf]
  | node hsx x rx =>
    cases h2 with
    | leaf =>
      rw [merge_leaf_right]
      simp [msetTree_leaf]
    | node hsy y ry =>
      rw [isRoot_node] at h1r h2r
      subst h1r
      subst h2r
      rw [merge_node_node, mset_link]
      simp only [msetTree_node]
      ac_rfl

/-- AFP `mset_del_min`. Note: the AFP statement reads `t ≠ Leaf` with `t`
unbound (a typo for `h`); the Lean statement uses the meaningful form
`getMin h = some x` together with `isRoot h` (without `isRoot`, the
statement is false, since `del_min` discards the right child). -/
theorem mset_delMin [LinearOrder α] {h : BTree α} (x : α) (hr : isRoot h)
    (hx : getMin h = some x) : msetTree (delMin h) = msetTree h - {x} := by
  cases h with
  | leaf => simp [getMin_leaf] at hx
  | node hs z rx =>
    rw [isRoot_node] at hr
    subst hr
    simp only [getMin_node, Option.some.injEq] at hx
    subst hx
    rw [delMin_node, mset_pass2, mset_pass1, msetTree_node]
    simp only [msetTree_leaf, add_zero]
    rw [Multiset.sub_singleton, Multiset.singleton_add, Multiset.erase_cons_head]

/-! ### The `Priority_Queue_Merge` specification -/

/-- The `Priority_Queue_Merge` specification for the Tree variant, in the
Isabelle locale's form (`pairing: Priority_Queue_Merge` in
`Pairing_Heap_Tree.thy`), with `invar = λh. is_root h ∧ pheap h` and
`mset = mset_tree`, plus the definedness clause. -/
theorem priority_queue_merge_locale [LinearOrder α] :
    PriorityQueueMergeSpec (BTree.leaf : BTree α) isEmpty merge insert delMin getMin
      (fun t => isRoot t ∧ pheap t) msetTree := by
  unfold PriorityQueueMergeSpec
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ⟨trivial, trivial⟩, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact (msetTree_eq_zero_iff t).symm
  · intro x t hinv
    obtain ⟨hr, hp⟩ := hinv
    have hroot : isRoot (BTree.node BTree.leaf x BTree.leaf) := by simp [isRoot]
    rw [insert_eq]
    rw [mset_merge hroot hr]
    simp only [msetTree_node, msetTree_leaf, add_zero]
    exact add_comm _ _
  · intro t x hinv _ hx
    obtain ⟨hr, -⟩ := hinv
    exact mset_delMin x hr hx
  · intro t x hinv _ hx
    obtain ⟨hr, hp⟩ := hinv
    exact getMin_isLeast t x hx hr hp
  · intro t hne
    exact getMin_defined t hne
  · intro x t hinv
    obtain ⟨hr, hp⟩ := hinv
    exact ⟨isRoot_insert hr, pheap_insert hr hp⟩
  · intro t hinv _
    obtain ⟨hr, hp⟩ := hinv
    exact ⟨isRoot_delMin hr, pheap_delMin hr hp⟩
  · intro t1 t2 hinv1 hinv2
    obtain ⟨hr1, -⟩ := hinv1
    obtain ⟨hr2, -⟩ := hinv2
    exact mset_merge hr1 hr2
  · intro t1 t2 hinv1 hinv2
    obtain ⟨hr1, hp1⟩ := hinv1
    obtain ⟨hr2, hp2⟩ := hinv2
    exact ⟨isRoot_merge hr1 hr2, pheap_merge hr1 hr2 hp1 hp2⟩

/-- The `Priority_Queue_Merge` specification for the Tree variant in the
book's form (Chapter 14, Figures 14.1–14.2): the book's 9 properties,
no `is_empty`, plus the definedness clause. -/
theorem priority_queue_merge_book [LinearOrder α] :
    PriorityQueueSpec (BTree.leaf : BTree α) merge insert delMin getMin
      (fun t => isRoot t ∧ pheap t) msetTree := by
  unfold PriorityQueueSpec
  refine ⟨rfl, ⟨trivial, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x t hinv
    obtain ⟨hr, hp⟩ := hinv
    have hroot : isRoot (BTree.node BTree.leaf x BTree.leaf) := by simp [isRoot]
    rw [insert_eq, mset_merge hroot hr]
    simp only [msetTree_node, msetTree_leaf, add_zero]
    exact add_comm _ _
  · intro x t hinv
    obtain ⟨hr, hp⟩ := hinv
    exact ⟨isRoot_insert hr, pheap_insert hr hp⟩
  · intro t x hinv _ hx
    obtain ⟨hr, -⟩ := hinv
    exact mset_delMin x hr hx
  · intro t hinv _
    obtain ⟨hr, hp⟩ := hinv
    exact ⟨isRoot_delMin hr, pheap_delMin hr hp⟩
  · intro t x hinv _ hx
    obtain ⟨hr, hp⟩ := hinv
    exact getMin_isLeast t x hx hr hp
  · intro t hne
    exact getMin_defined t hne
  · intro t1 t2 hinv1 hinv2
    obtain ⟨hr1, -⟩ := hinv1
    obtain ⟨hr2, -⟩ := hinv2
    exact mset_merge hr1 hr2
  · intro t1 t2 hinv1 hinv2
    obtain ⟨hr1, hp1⟩ := hinv1
    obtain ⟨hr2, hp2⟩ := hinv2
    exact ⟨isRoot_merge hr1 hr2, pheap_merge hr1 hr2 hp1 hp2⟩

end Tree

end PairingHeap

end Cslib.Algorithms.Lean
