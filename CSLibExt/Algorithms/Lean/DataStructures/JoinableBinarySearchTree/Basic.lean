/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`src/HOL/Data_Structures/Set2_Join.thy` (Isabelle/HOL, `HOL-Data_Structures`):
Copyright (c) 1986-2026, University of Cambridge, Technische Universitaet Muenchen,
and contributors. All rights reserved.
Licensed under the 3-clause BSD license in Isabelle's `COPYRIGHT` file
(https://github.com/isabelle-prover/mirror-isabelle/blob/master/COPYRIGHT).
Authors: Tobias Nipkow
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Set.Basic

/-!
# Joinable binary search trees: the generic join framework

The `Set2` interface of Chapter 10 of *Functional Data Structures and
Algorithms* (Nipkow, ed., book pp. 117–125, §10.1–§10.2): a binary search
tree type `Tree α β` carrying balancing information `β` in each node, the
Figure 10.2 `JoinData` specification of `join` and its invariant `inv`,
and the derived operations `split_min`, `join2`, `split`, `insert`,
`delete`, `union`, `inter`, `diff`, `diff1` (Exercise 10.2), `insert'` /
`delete'` (Exercise 10.1), each with `set` / `bst` / `inv` correctness.
`tsize` counts nodes. Exercise 10.3 (2–3-tree join), the red–black join,
the AVL join, and the strongly joinable instances live in separate
modules of this family.

## Provenance

Adapted from the Isabelle formalization of Chapter 10: `Set2_Join` in
Isabelle/HOL's bundled `HOL-Data_Structures` library (the `Set2_Join`
locale: the book's specification, proved for red–black trees in
`Set2_Join_RBT.thy`), as re-exported through the AFP entry
`Joinable_BST_Work_Bounds` (`StronglyJoinable.thy`, which extends the
`Set2_Join` locale with `BalancedTree`; the interpretations for the
stored-height red–black and AVL trees are in `StronglyJoinableRBT.thy`
and `StronglyJoinableAVL.thy`). The book's
Chapter 10 statements are the ground truth for *what* is proved; the
Isabelle sources are the formal reference for the definitions.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Cslib.Algorithms.Lean
namespace JoinableBinarySearchTree

variable {α : Type u} {β : Type v} [LinearOrder α] [Inhabited β]

/-- Binary search trees with balancing information `β` in each node.
`Tree α β` is the book's `(α × β) tree`. -/
public inductive Tree (α : Type u) (β : Type v) where
  | Leaf : Tree α β
  | Node : Tree α β → α × β → Tree α β → Tree α β
deriving DecidableEq


/-- `set_tree t`: the set of keys stored in `t` (book `set_tree`). -/
public def set_tree : Tree α β → Set α
  | .Leaf => ∅
  | .Node l (a, _) r => set_tree l ∪ {a} ∪ set_tree r

/-- `bst t`: `t` is a binary search tree. -/
public def bst : Tree α β → Prop
  | .Leaf => True
  | .Node l (a, _) r =>
      bst l ∧ bst r ∧ (∀ x ∈ set_tree l, x < a) ∧ (∀ y ∈ set_tree r, a < y)

omit [LinearOrder α] [Inhabited β] in
@[simp] public theorem set_tree_leaf : set_tree (Tree.Leaf : Tree α β) = ∅ := rfl
omit [LinearOrder α] [Inhabited β] in
@[simp] public theorem set_tree_node (l : Tree α β) (kv : α × β) (r : Tree α β) :
    set_tree (Tree.Node l kv r) = set_tree l ∪ {kv.1} ∪ set_tree r := rfl

omit [Inhabited β] in
public theorem bst_leaf : bst (Tree.Leaf : Tree α β) := trivial

omit [Inhabited β] in
public theorem bst_node {l r : Tree α β} {kv : α × β} :
    bst (Tree.Node l kv r) ↔
      bst l ∧ bst r ∧ (∀ x ∈ set_tree l, x < kv.1) ∧ (∀ y ∈ set_tree r, kv.1 < y) :=
  Iff.rfl

/-- The book's Figure 10.2 specification of `join` and `inv`, packaged as a
structure. The fields are *hypotheses* of the structure, not axioms:
instantiating `JoinData` requires proving them (see the red–black
instance `rbtJoinData` in `RedBlackJoin`). -/
public structure JoinData (α : Type u) (β : Type v) [LinearOrder α] [Inhabited β] where
  join : Tree α β → α → Tree α β → Tree α β
  inv : Tree α β → Prop
  /-- (Fig. 10.2) `inv ⟨⟩` -/
  inv_leaf : inv Tree.Leaf
  /-- (10.1) `set_tree (join l a r) = set_tree l ∪ {a} ∪ set_tree r` -/
  set_join : ∀ (l : Tree α β) (a : α) (r : Tree α β),
    set_tree (join l a r) = set_tree l ∪ {a} ∪ set_tree r
  /-- (10.2) `bst ⟨l; (a; _) ; r⟩ → bst (join l a r)` -/
  bst_join : ∀ (l : Tree α β) (a : α) (b : β) (r : Tree α β),
    bst (Tree.Node l (a, b) r) → bst (join l a r)
  /-- (10.3) `inv l ∧ inv r → inv (join l a r)` -/
  inv_join : ∀ (l : Tree α β) (a : α) (r : Tree α β),
    inv l → inv r → inv (join l a r)
  /-- (10.4) `inv ⟨l; (_; _) ; r⟩ → inv l ∧ inv r` -/
  inv_node : ∀ (l : Tree α β) (kv : α × β) (r : Tree α β),
    inv (Tree.Node l kv r) → inv l ∧ inv r

variable (J : JoinData α β)

/-- `split_min`: split off the leftmost (minimal) element, reassembling the
rest with `join` (book §10.2). `none` on the empty tree. -/
public def split_min : Tree α β → Option (α × Tree α β)
  | .Leaf => none
  | .Node .Leaf (a, _) r => some (a, r)
  | .Node (.Node ll kv' rl) (a, _) r =>
    match split_min (.Node ll kv' rl) with
    | none => none
    | some (m, l') => some (m, J.join l' a r)

/-- `join2 l r`: join two trees with no element in between, via `split_min`
(book §10.2). -/
public def join2 (l r : Tree α β) : Tree α β :=
  match split_min J r with
  | none => l
  | some (m, r') => J.join l m r'

/-- `split x t = (l, b, r)`: for a search tree `t` (the `bst t` premise of
`split_set`), `l` holds the elements `< x`, `r` the elements `> x`, and `b`
says whether `x` was present (book §10.2). The recursive result is bound
once with `let`, so each visited level makes one recursive call and at most
one `join` (calling it separately for each projection would be
exponential). `JoinData` bounds no cost of `join`, so this counts calls; it
is not a bound on the total work. -/
public def split (x : α) : Tree α β → Tree α β × Bool × Tree α β
  | .Leaf => (Tree.Leaf, false, Tree.Leaf)
  | .Node l (a, _) r =>
    if x < a then
      let s := split x l
      (s.1, s.2.1, J.join s.2.2 a r)
    else if x = a then (l, true, r)
    else
      let s := split x r
      (J.join l a s.1, s.2.1, s.2.2)

/-- `insert x t = join (split x t).1 x (split x t).2.2` (book §10.2).
The `split` result is shared with `let`. -/
public def insert (x : α) (t : Tree α β) : Tree α β :=
  let s := split J x t
  J.join s.1 x s.2.2

/-- `delete x t = join2 (split x t).1 (split x t).2.2` (book §10.2).
The `split` result is shared with `let`. -/
public def delete (x : α) (t : Tree α β) : Tree α β :=
  let s := split J x t
  join2 J s.1 s.2.2

/-- `union` (book Fig. 10.3): divide and conquer on the first tree,
splitting the second at each pivot. Both base cases of Fig. 10.3 are
equations: `union Leaf t₂ = t₂` *and* `union t₁ Leaf = t₁` (the second
one matters: without it `union t Leaf` would be rebuilt via `join`,
which need not return `t` — e.g. red–black `join` repaints the root). -/
public def union : Tree α β → Tree α β → Tree α β
  | .Leaf, t₂ => t₂
  | t₁, .Leaf => t₁
  | .Node l₁ (a, _) r₁, t₂ =>
    let s := split J a t₂
    J.join (union l₁ s.1) a (union r₁ s.2.2)

/-- `inter` (book Fig. 10.3). The `split` result is shared with `let`. -/
public def inter : Tree α β → Tree α β → Tree α β
  | .Leaf, _ => Tree.Leaf
  | _, .Leaf => Tree.Leaf
  | .Node l₁ (a, _) r₁, t₂ =>
    let s := split J a t₂
    if s.2.1 then
      J.join (inter l₁ s.1) a (inter r₁ s.2.2)
    else
      join2 J (inter l₁ s.1) (inter r₁ s.2.2)

/-- `diff` (book Fig. 10.3): divide and conquer on the *second* tree,
splitting the first at each pivot. Both base cases of Fig. 10.3 are
equations, in the book's order: `diff Leaf t₂ = Leaf` comes first, so the
recursion stops as soon as a split leaves the first tree empty, and then
`diff t₁ Leaf = t₁`. Structural recursion on the second argument; the
`split` result is shared with `let`. -/
public def diff : Tree α β → Tree α β → Tree α β
  | .Leaf, _ => Tree.Leaf
  | t₁, .Leaf => t₁
  | t₁, .Node l₂ (a, _) r₂ =>
    let s := split J a t₁
    join2 J (diff s.1 l₂) (diff s.2.2 r₂)

/-! ### Auxiliary lemmas about `set_tree` and `bst` -/

omit [LinearOrder α] [Inhabited β] in
public theorem mem_set_tree_node {l r : Tree α β} {kv : α × β} {x : α} :
    x ∈ set_tree (Tree.Node l kv r) ↔ x ∈ set_tree l ∨ x = kv.1 ∨ x ∈ set_tree r := by
  simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]
  tauto

-- split_min correctness (book §10.2.1, three statements)
public theorem split_min_set {t : Tree α β} {m : α} {t' : Tree α β}
    (h : split_min J t = some (m, t')) (hne : t ≠ Tree.Leaf) :
    m ∈ set_tree t ∧ set_tree t = {m} ∪ set_tree t' := by
  revert h hne
  induction t generalizing m t' with
  | Leaf =>
    intro h hne
    exact absurd rfl hne
  | Node l kv r ihl ihr =>
    intro h hne
    obtain ⟨a, b⟩ := kv
    cases l with
    | Leaf =>
      simp only [split_min] at h
      cases h
      constructor
      · simp
      · simp [set_tree_node]
    | Node ll kv' rl =>
      simp only [split_min] at h
      obtain ⟨m₁, l', hsplit⟩ : ∃ m₁ l', split_min J (Tree.Node ll kv' rl) = some (m₁, l') := by
        cases h2 : split_min J (Tree.Node ll kv' rl) with
        | none => simp [h2] at h
        | some p =>
          obtain ⟨m₁, l'⟩ := p
          exact ⟨m₁, l', rfl⟩
      have hmem := ihl hsplit (by simp)
      simp only [hsplit] at h
      cases h
      constructor
      · have hm : m ∈ set_tree (Tree.Node ll kv' rl) := hmem.1
        rw [mem_set_tree_node] at hm
        simp only [mem_set_tree_node]
        tauto
      · rw [set_tree_node, hmem.2, J.set_join]
        ext y
        simp only [Set.mem_union, Set.mem_singleton_iff]
        tauto

public theorem split_min_bst {t : Tree α β} {m : α} {t' : Tree α β}
    (h : split_min J t = some (m, t')) (hbst : bst t) (hne : t ≠ Tree.Leaf) :
    bst t' ∧ ∀ x ∈ set_tree t', m < x := by
  revert h hne
  induction t generalizing m t' with
  | Leaf =>
    intro h hne
    exact absurd rfl hne
  | Node l kv r ihl ihr =>
    intro h hne
    obtain ⟨a, b⟩ := kv
    have hbst' : bst l ∧ bst r ∧ (∀ x ∈ set_tree l, x < a) ∧ (∀ y ∈ set_tree r, a < y) := hbst
    cases l with
    | Leaf =>
      simp only [split_min] at h
      cases h
      exact ⟨hbst'.2.1, hbst'.2.2.2⟩
    | Node ll kv' rl =>
      simp only [split_min] at h
      obtain ⟨m₁, l', hsplit⟩ : ∃ m₁ l', split_min J (Tree.Node ll kv' rl) = some (m₁, l') := by
        cases h2 : split_min J (Tree.Node ll kv' rl) with
        | none => simp [h2] at h
        | some p =>
          obtain ⟨m₁, l'⟩ := p
          exact ⟨m₁, l', rfl⟩
      have hset_l := (split_min_set J hsplit (by simp)).2
      have ih := ihl hbst'.1 hsplit (by simp)
      simp only [hsplit] at h
      cases h
      have hnode : bst (Tree.Node l' (a, b) r) := by
        refine ⟨ih.1, hbst'.2.1, ?_, hbst'.2.2.2⟩
        intro x hx
        have hx_l : x ∈ set_tree (Tree.Node ll kv' rl) := by
          rw [hset_l]; exact Set.mem_union_right _ hx
        exact hbst'.2.2.1 x hx_l
      refine ⟨J.bst_join l' a b r hnode, ?_⟩
      intro x hx
      rw [J.set_join] at hx
      simp only [Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with (hx | hx) | hx
      · exact ih.2 x hx
      · subst hx
        have hm₁ : m ∈ set_tree (Tree.Node ll kv' rl) := by
          rw [hset_l]; exact Set.mem_union_left _ rfl
        exact hbst'.2.2.1 m hm₁
      · have hm₁ : m ∈ set_tree (Tree.Node ll kv' rl) := by
          rw [hset_l]; exact Set.mem_union_left _ rfl
        exact lt_trans (hbst'.2.2.1 m hm₁) (hbst'.2.2.2 x hx)

public theorem split_min_inv {t : Tree α β} {m : α} {t' : Tree α β}
    (h : split_min J t = some (m, t')) (hinv : J.inv t) (hne : t ≠ Tree.Leaf) :
    J.inv t' := by
  revert h hne
  induction t generalizing m t' with
  | Leaf =>
    intro h hne
    exact absurd rfl hne
  | Node l kv r ihl ihr =>
    intro h hne
    obtain ⟨a, b⟩ := kv
    cases l with
    | Leaf =>
      simp only [split_min] at h
      cases h
      exact (J.inv_node Tree.Leaf (m, b) r hinv).2
    | Node ll kv' rl =>
      simp only [split_min] at h
      obtain ⟨m₁, l', hsplit⟩ : ∃ m₁ l', split_min J (Tree.Node ll kv' rl) = some (m₁, l') := by
        cases h2 : split_min J (Tree.Node ll kv' rl) with
        | none => simp [h2] at h
        | some p =>
          obtain ⟨m₁, l'⟩ := p
          exact ⟨m₁, l', rfl⟩
      simp only [hsplit] at h
      cases h
      have hinv_l : J.inv (Tree.Node ll kv' rl) := (J.inv_node _ (a, b) r hinv).1
      have hinv_r : J.inv r := (J.inv_node _ (a, b) r hinv).2
      exact J.inv_join l' a r (ihl hinv_l hsplit (by simp)) hinv_r


/-- `split_min` is defined (is `some`) on every non-empty tree. -/
public theorem split_min_some {t : Tree α β} (hne : t ≠ Tree.Leaf) :
    ∃ m t', split_min J t = some (m, t') := by
  induction t with
  | Leaf => exact absurd rfl hne
  | Node l kv r ihl ihr =>
    obtain ⟨a, b⟩ := kv
    cases l with
    | Leaf => exact ⟨a, r, rfl⟩
    | Node ll kv' rl =>
      obtain ⟨m₁, l', hs⟩ := ihl (by simp)
      exact ⟨m₁, J.join l' a r, by simp only [split_min, hs]⟩

/-- `join2` correctness (book §10.2.1, (10.5) and the two preservation
properties). -/
public theorem join2_set (l r : Tree α β) :
    set_tree (join2 J l r) = set_tree l ∪ set_tree r := by
  unfold join2
  cases hsp : split_min J r with
  | none =>
    have hr : r = Tree.Leaf := by
      by_contra hne
      obtain ⟨_, _, hs⟩ := split_min_some J hne
      rw [hs] at hsp
      cases hsp
    rw [hr]
    simp
  | some p =>
    obtain ⟨m, r'⟩ := p
    have hne : r ≠ Tree.Leaf := by
      intro hr
      rw [hr] at hsp
      simp [split_min] at hsp
    have hset := (split_min_set J hsp hne).2
    rw [J.set_join, hset]
    ext y
    simp only [Set.mem_union, Set.mem_singleton_iff]
    tauto

public theorem join2_bst {l r : Tree α β} (hbst_l : bst l) (hbst_r : bst r)
    (hsep : ∀ x ∈ set_tree l, ∀ y ∈ set_tree r, x < y) :
    bst (join2 J l r) := by
  unfold join2
  cases hsp : split_min J r with
  | none =>
    have hr : r = Tree.Leaf := by
      by_contra hne
      obtain ⟨_, _, hs⟩ := split_min_some J hne
      rw [hs] at hsp
      cases hsp
    exact hbst_l
  | some p =>
    obtain ⟨m, r'⟩ := p
    have hne : r ≠ Tree.Leaf := by
      intro hr
      rw [hr] at hsp
      simp [split_min] at hsp
    have hset := (split_min_set J hsp hne).2
    have hbst := split_min_bst J hsp hbst_r hne
    apply J.bst_join l m default r'
    refine ⟨hbst_l, hbst.1, ?_, ?_⟩
    · intro x hx
      exact hsep x hx m (by rw [hset]; exact Set.mem_union_left _ rfl)
    · intro y hy
      exact hbst.2 y hy

public theorem join2_inv {l r : Tree α β} (hinv_l : J.inv l) (hinv_r : J.inv r) :
    J.inv (join2 J l r) := by
  unfold join2
  cases hsp : split_min J r with
  | none =>
    have hr : r = Tree.Leaf := by
      by_contra hne
      obtain ⟨_, _, hs⟩ := split_min_some J hne
      rw [hs] at hsp
      cases hsp
    exact hinv_l
  | some p =>
    obtain ⟨m, r'⟩ := p
    have hne : r ≠ Tree.Leaf := by
      intro hr
      rw [hr] at hsp
      simp [split_min] at hsp
    exact J.inv_join l m r' hinv_l (split_min_inv J hsp hinv_r hne)

/-- `split` set/boolean properties (book §10.2.1, (10.6)); needs `bst` only. -/
public theorem split_set (t : Tree α β) (x : α) (hbst : bst t) :
    set_tree (split J x t).1 = {y ∈ set_tree t | y < x} ∧
    set_tree (split J x t).2.2 = {y ∈ set_tree t | x < y} ∧
    ((split J x t).2.1 = true ↔ x ∈ set_tree t) := by
  revert hbst
  induction t with
  | Leaf =>
    intro hbst
    refine ⟨by simp [split], by simp [split], by simp [split]⟩
  | Node l kv r ihl ihr =>
    intro hbst
    obtain ⟨a, b⟩ := kv
    have hbst' : bst l ∧ bst r ∧ (∀ x ∈ set_tree l, x < a) ∧ (∀ y ∈ set_tree r, a < y) := hbst
    rcases lt_trichotomy x a with hlt | heq | hgt
    · have ih := ihl hbst'.1
      simp only [split, ite_eq_left hlt]
      refine ⟨?_, ?_, ?_⟩
      · rw [ih.1]
        ext y
        constructor
        · intro hy
          obtain ⟨hy1, hy2⟩ := hy
          exact ⟨Or.inl (Or.inl hy1), hy2⟩
        · intro hy
          simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
          obtain ⟨hN, hyx⟩ := hy
          rcases hN with (h | h) | h
          · exact ⟨h, hyx⟩
          · exact absurd (h ▸ hyx) (not_lt_of_ge (le_of_lt hlt))
          · exact absurd (lt_trans (hbst'.2.2.2 y h) hyx) (not_lt_of_ge (le_of_lt hlt))
      · rw [J.set_join, ih.2.1]
        ext y
        constructor
        · intro hy
          simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff] at hy
          rcases hy with (hy | hy) | hy
          · exact ⟨Or.inl (Or.inl hy.1), hy.2⟩
          · exact ⟨Or.inl (Or.inr hy), hy.symm ▸ hlt⟩
          · exact ⟨Or.inr hy, lt_trans hlt (hbst'.2.2.2 y hy)⟩
        · intro hy
          simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
          obtain ⟨hN, hxy⟩ := hy
          rcases hN with (h | h) | h
          · exact Or.inl (Or.inl ⟨h, hxy⟩)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
      · rw [ih.2.2]
        constructor
        · intro hx
          exact Or.inl (Or.inl hx)
        · intro hx
          simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hx
          rcases hx with (hx | hx) | hx
          · exact hx
          · rw [hx] at hlt
            exact absurd hlt (lt_irrefl a)
          · exact absurd (lt_trans hlt (hbst'.2.2.2 x hx)) (lt_irrefl x)
    · subst heq
      simp only [split, lt_irrefl, ite_false, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · ext y
        constructor
        · intro hy
          exact ⟨Or.inl (Or.inl hy), hbst'.2.2.1 y hy⟩
        · intro hy
          simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
          obtain ⟨hN, hyx⟩ := hy
          rcases hN with (h | h) | h
          · exact h
          · exact absurd (h ▸ hyx) (lt_irrefl x)
          · exact absurd (lt_trans hyx (hbst'.2.2.2 y h)) (lt_irrefl y)
      · ext y
        constructor
        · intro hy
          exact ⟨Or.inr hy, hbst'.2.2.2 y hy⟩
        · intro hy
          simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
          obtain ⟨hN, hyx⟩ := hy
          rcases hN with (h | h) | h
          · exact absurd (lt_trans (hbst'.2.2.1 y h) hyx) (lt_irrefl y)
          · exact absurd (h ▸ hyx) (lt_irrefl x)
          · exact h
      · constructor
        · intro _
          exact Or.inl (Or.inr rfl)
        · intro _
          trivial
    · have ih := ihr hbst'.2.1
      simp only [split, ite_eq_right (not_lt_of_ge (le_of_lt hgt)), ite_eq_right (Ne.symm (ne_of_lt hgt))]
      refine ⟨?_, ?_, ?_⟩
      · rw [J.set_join, ih.1]
        ext y
        constructor
        · intro hy
          simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff] at hy
          rcases hy with (hy | hy) | hy
          · exact ⟨Or.inl (Or.inl hy), lt_trans (hbst'.2.2.1 y hy) hgt⟩
          · exact ⟨Or.inl (Or.inr hy), hy.symm ▸ hgt⟩
          · exact ⟨Or.inr hy.1, hy.2⟩
        · intro hy
          simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
          obtain ⟨hN, hyx⟩ := hy
          rcases hN with (h | h) | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨h, hyx⟩
      · rw [ih.2.1]
        ext y
        constructor
        · intro hy
          obtain ⟨hy1, hy2⟩ := hy
          exact ⟨Or.inr hy1, hy2⟩
        · intro hy
          simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
          obtain ⟨hN, hyx⟩ := hy
          rcases hN with (h | h) | h
          · exact absurd (lt_trans hyx (hbst'.2.2.1 y h)) (not_lt_of_ge (le_of_lt hgt))
          · exact absurd (h ▸ hyx) (not_lt_of_ge (le_of_lt hgt))
          · exact ⟨h, hyx⟩
      · rw [ih.2.2]
        constructor
        · intro hx
          exact Or.inr hx
        · intro hx
          simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hx
          rcases hx with (hx | hx) | hx
          · exact absurd (lt_trans (hbst'.2.2.1 x hx) hgt) (lt_irrefl x)
          · rw [hx] at hgt
            exact absurd hgt (lt_irrefl a)
          · exact hx

/-- `split` preserves `bst` (book §10.2.1, (10.6)); needs `bst` only. -/
public theorem split_bst (t : Tree α β) (x : α) (hbst : bst t) :
    bst (split J x t).1 ∧ bst (split J x t).2.2 := by
  revert hbst
  induction t with
  | Leaf =>
    intro hbst
    exact ⟨trivial, trivial⟩
  | Node l kv r ihl ihr =>
    intro hbst
    obtain ⟨a, b⟩ := kv
    have hbst' : bst l ∧ bst r ∧ (∀ x ∈ set_tree l, x < a) ∧ (∀ y ∈ set_tree r, a < y) := hbst
    have hset := split_set J (Tree.Node l (a, b) r) x hbst
    rcases lt_trichotomy x a with hlt | heq | hgt
    · have ih := ihl hbst'.1
      simp only [split, ite_eq_left hlt]
      refine ⟨ih.1, ?_⟩
      exact J.bst_join (split J x l).2.2 a b r
        ⟨ih.2, hbst'.2.1, by
          intro y hy
          have hs := (split_set J l x hbst'.1).2.1
          rw [hs] at hy
          simp only [Set.mem_sep_iff] at hy
          exact hbst'.2.2.1 y hy.1, hbst'.2.2.2⟩
    · subst heq
      simp only [split, lt_irrefl, ite_false, ite_true]
      exact ⟨hbst'.1, hbst'.2.1⟩
    · have ih := ihr hbst'.2.1
      simp only [split, ite_eq_right (not_lt_of_ge (le_of_lt hgt)), ite_eq_right (Ne.symm (ne_of_lt hgt))]
      refine ⟨?_, ih.2⟩
      exact J.bst_join l a b (split J x r).1
        ⟨hbst'.1, ih.1, hbst'.2.2.1, by
          intro y hy
          have hs := (split_set J r x hbst'.2.1).1
          rw [hs] at hy
          simp only [Set.mem_sep_iff] at hy
          exact hbst'.2.2.2 y hy.1⟩

/-- `split` preserves `inv` (book §10.2.1); needs `inv` only. -/
public theorem split_inv (t : Tree α β) (x : α) (hinv : J.inv t) :
    J.inv (split J x t).1 ∧ J.inv (split J x t).2.2 := by
  revert hinv
  induction t with
  | Leaf =>
    intro hinv
    exact ⟨J.inv_leaf, J.inv_leaf⟩
  | Node l kv r ihl ihr =>
    intro hinv
    obtain ⟨a, b⟩ := kv
    have hinv_l : J.inv l := (J.inv_node l (a, b) r hinv).1
    have hinv_r : J.inv r := (J.inv_node l (a, b) r hinv).2
    rcases lt_trichotomy x a with hlt | heq | hgt
    · have ih := ihl hinv_l
      simp only [split, ite_eq_left hlt]
      exact ⟨ih.1, J.inv_join _ _ _ ih.2 hinv_r⟩
    · subst heq
      simp only [split, lt_irrefl, ite_false, ite_true]
      exact ⟨hinv_l, hinv_r⟩
    · have ih := ihr hinv_r
      simp only [split, ite_eq_right (not_lt_of_ge (le_of_lt hgt)), ite_eq_right (Ne.symm (ne_of_lt hgt))]
      exact ⟨J.inv_join _ _ _ hinv_l ih.1, ih.2⟩

/-- `split` correctness, all together (book §10.2.1, (10.6) and preservation). -/
public theorem split_spec (t : Tree α β) (x : α) (hbst : bst t) (hinv : J.inv t) :
    set_tree (split J x t).1 = {y ∈ set_tree t | y < x} ∧
    set_tree (split J x t).2.2 = {y ∈ set_tree t | x < y} ∧
    ((split J x t).2.1 = true ↔ x ∈ set_tree t) ∧
    bst (split J x t).1 ∧ bst (split J x t).2.2 ∧
    J.inv (split J x t).1 ∧ J.inv (split J x t).2.2 := by
  obtain ⟨h1, h2, h3⟩ := split_set J t x hbst
  obtain ⟨h4, h5⟩ := split_bst J t x hbst
  obtain ⟨h6, h7⟩ := split_inv J t x hinv
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩



/-- `union` set property (book §10.2.1). Only `bst t₂` is needed. -/
public theorem union_set (t₁ t₂ : Tree α β) (hbst₂ : bst t₂) :
    set_tree (union J t₁ t₂) = set_tree t₁ ∪ set_tree t₂ := by
  induction t₁ generalizing t₂ with
  | Leaf => simp [union]
  | Node l₁ kv r₁ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    cases t₂ with
    | Leaf => simp [union]
    | Node l₂ kv₂ r₂ =>
      have hsp := split_set J (Tree.Node l₂ kv₂ r₂) a hbst₂
      have hspb := split_bst J (Tree.Node l₂ kv₂ r₂) a hbst₂
      simp only [union, J.set_join, ihl (split J a (Tree.Node l₂ kv₂ r₂)).1 hspb.1,
        ihr (split J a (Tree.Node l₂ kv₂ r₂)).2.2 hspb.2, hsp.1, hsp.2.1, set_tree_node]
      ext y
      simp only [Set.mem_union, Set.mem_singleton_iff]
      have htri : y < a ∨ y = a ∨ a < y := lt_trichotomy y a
      aesop

/-- `union` preserves `bst` (book §10.2.1). -/
public theorem union_bst (t₁ t₂ : Tree α β) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (union J t₁ t₂) := by
  induction t₁ generalizing t₂ with
  | Leaf => exact hbst₂
  | Node l₁ kv r₁ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    have hbst₁' : bst l₁ ∧ bst r₁ ∧ (∀ x ∈ set_tree l₁, x < a) ∧ (∀ y ∈ set_tree r₁, a < y) := hbst₁
    cases t₂ with
    | Leaf => simpa [union] using hbst₁
    | Node l₂ kv₂ r₂ =>
      have hsp := split_set J (Tree.Node l₂ kv₂ r₂) a hbst₂
      have hspb := split_bst J (Tree.Node l₂ kv₂ r₂) a hbst₂
      simp only [union]
      exact J.bst_join _ a b _
        ⟨ihl (split J a (Tree.Node l₂ kv₂ r₂)).1 hbst₁'.1 hspb.1,
         ihr (split J a (Tree.Node l₂ kv₂ r₂)).2.2 hbst₁'.2.1 hspb.2, by
          intro x hx
          have hs := union_set J l₁ (split J a (Tree.Node l₂ kv₂ r₂)).1 hspb.1
          rw [hs] at hx
          simp only [Set.mem_union] at hx
          rcases hx with hx | hx
          · exact hbst₁'.2.2.1 x hx
          · have hss := hsp.1
            rw [hss] at hx
            simp only [Set.mem_sep_iff] at hx
            exact hx.2, by
          intro y hy
          have hs := union_set J r₁ (split J a (Tree.Node l₂ kv₂ r₂)).2.2 hspb.2
          rw [hs] at hy
          simp only [Set.mem_union] at hy
          rcases hy with hy | hy
          · exact hbst₁'.2.2.2 y hy
          · have hss := hsp.2.1
            rw [hss] at hy
            simp only [Set.mem_sep_iff] at hy
            exact hy.2⟩

/-- `union` preserves `inv` (book §10.2.1). -/
public theorem union_inv (t₁ t₂ : Tree α β) (hinv₁ : J.inv t₁) (hinv₂ : J.inv t₂) :
    J.inv (union J t₁ t₂) := by
  induction t₁ generalizing t₂ with
  | Leaf => exact hinv₂
  | Node l₁ kv r₁ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    have hinv₁' : J.inv l₁ ∧ J.inv r₁ := J.inv_node l₁ (a, b) r₁ hinv₁
    cases t₂ with
    | Leaf => simpa [union] using hinv₁
    | Node l₂ kv₂ r₂ =>
      have hspi := split_inv J (Tree.Node l₂ kv₂ r₂) a hinv₂
      simp only [union]
      exact J.inv_join _ _ _
        (ihl (split J a (Tree.Node l₂ kv₂ r₂)).1 hinv₁'.1 hspi.1)
        (ihr (split J a (Tree.Node l₂ kv₂ r₂)).2.2 hinv₁'.2 hspi.2)

/-- Book Fig. 10.3, first base case for `union`. -/
public theorem union_left_leaf (t : Tree α β) : union J Tree.Leaf t = t := rfl

/-- Book Fig. 10.3, second base case for `union`. -/
public theorem union_right_leaf (t : Tree α β) : union J t Tree.Leaf = t := by
  cases t with
  | Leaf => rfl
  | Node l kv r => rfl

/-- Book Fig. 10.3, first base case for `diff` (the first equation of its
definition). -/
public theorem diff_leaf (t₂ : Tree α β) : diff J Tree.Leaf t₂ = Tree.Leaf := by
  cases t₂ <;> rfl

/-- Book Fig. 10.3, second base case for `diff`. -/
private theorem diff_right_leaf (t₁ : Tree α β) : diff J t₁ Tree.Leaf = t₁ := by
  cases t₁ <;> rfl

/-- The recursive equation of `diff` holds for every first tree: when it is
empty, both sides are empty. -/
private theorem diff_node (t₁ l₂ r₂ : Tree α β) (a : α) (b : β) :
    diff J t₁ (Tree.Node l₂ (a, b) r₂) =
      join2 J (diff J (split J a t₁).1 l₂) (diff J (split J a t₁).2.2 r₂) := by
  cases t₁ with
  | Leaf =>
    rw [diff_leaf]
    change Tree.Leaf = join2 J (diff J Tree.Leaf l₂) (diff J Tree.Leaf r₂)
    rw [diff_leaf, diff_leaf]
    rfl
  | Node l₁ kv₁ r₁ => rfl

/-- `inter` set property (book §10.2.1). -/
public theorem inter_set (t₁ t₂ : Tree α β) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    set_tree (inter J t₁ t₂) = set_tree t₁ ∩ set_tree t₂ := by
  induction t₁ generalizing t₂ with
  | Leaf => simp [inter]
  | Node l₁ kv r₁ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    have hbst₁' : bst l₁ ∧ bst r₁ ∧ (∀ x ∈ set_tree l₁, x < a) ∧ (∀ y ∈ set_tree r₁, a < y) := hbst₁
    cases t₂ with
    | Leaf => simp [inter]
    | Node l₂ kv₂ r₂ =>
      obtain ⟨a₂, b₂⟩ := kv₂
      have hsp := split_set J (Tree.Node l₂ (a₂, b₂) r₂) a hbst₂
      have hspb := split_bst J (Tree.Node l₂ (a₂, b₂) r₂) a hbst₂
      by_cases hb : (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.1 = true
      · have ha : a ∈ set_tree (Tree.Node l₂ (a₂, b₂) r₂) := hsp.2.2.mp hb
        simp only [inter, ite_eq_left hb, J.set_join, ihl (split J a (Tree.Node l₂ (a₂, b₂) r₂)).1 hbst₁'.1 hspb.1,
          ihr (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.2 hbst₁'.2.1 hspb.2, hsp.1, hsp.2.1, set_tree_node]
        ext y
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_inter_iff]
        have h1 : y ∈ set_tree l₁ → y < a := hbst₁'.2.2.1 y
        have h2 : y ∈ set_tree r₁ → a < y := hbst₁'.2.2.2 y
        aesop
      · have hna : a ∉ set_tree (Tree.Node l₂ (a₂, b₂) r₂) := by
          intro ha
          exact hb (hsp.2.2.mpr ha)
        simp only [inter, ite_eq_right hb, join2_set, ihl (split J a (Tree.Node l₂ (a₂, b₂) r₂)).1 hbst₁'.1 hspb.1,
          ihr (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.2 hbst₁'.2.1 hspb.2, hsp.1, hsp.2.1, set_tree_node]
        ext y
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_inter_iff]
        have h1 : y ∈ set_tree l₁ → y < a := hbst₁'.2.2.1 y
        have h2 : y ∈ set_tree r₁ → a < y := hbst₁'.2.2.2 y
        have h3 : y = a → y ∈ set_tree (Tree.Node l₂ (a₂, b₂) r₂) → False := fun h hT => hna (h ▸ hT)
        aesop


/-- `inter` preserves `bst` (book §10.2.1). -/
public theorem inter_bst (t₁ t₂ : Tree α β) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (inter J t₁ t₂) := by
  induction t₁ generalizing t₂ with
  | Leaf => exact trivial
  | Node l₁ kv r₁ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    have hbst₁' : bst l₁ ∧ bst r₁ ∧ (∀ x ∈ set_tree l₁, x < a) ∧ (∀ y ∈ set_tree r₁, a < y) := hbst₁
    cases t₂ with
    | Leaf => exact trivial
    | Node l₂ kv₂ r₂ =>
      obtain ⟨a₂, b₂⟩ := kv₂
      have hspb := split_bst J (Tree.Node l₂ (a₂, b₂) r₂) a hbst₂
      by_cases hb : (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.1 = true
      · simp only [inter, ite_eq_left hb]
        exact J.bst_join (inter J l₁ (split J a (Tree.Node l₂ (a₂, b₂) r₂)).1) a b
          (inter J r₁ (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.2)
          ⟨ihl (split J a (Tree.Node l₂ (a₂, b₂) r₂)).1 hbst₁'.1 hspb.1,
           ihr (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.2 hbst₁'.2.1 hspb.2, by
            intro x hx
            have hs := inter_set J l₁ (split J a (Tree.Node l₂ (a₂, b₂) r₂)).1 hbst₁'.1 hspb.1
            rw [hs] at hx
            simp only [Set.mem_inter_iff] at hx
            exact hbst₁'.2.2.1 x hx.1, by
            intro y hy
            have hs := inter_set J r₁ (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.2 hbst₁'.2.1 hspb.2
            rw [hs] at hy
            simp only [Set.mem_inter_iff] at hy
            exact hbst₁'.2.2.2 y hy.1⟩
      · simp only [inter, ite_eq_right hb]
        exact join2_bst J (ihl (split J a (Tree.Node l₂ (a₂, b₂) r₂)).1 hbst₁'.1 hspb.1)
          (ihr (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.2 hbst₁'.2.1 hspb.2) (by
            intro x hx y hy
            have hs₁ := inter_set J l₁ (split J a (Tree.Node l₂ (a₂, b₂) r₂)).1 hbst₁'.1 hspb.1
            have hs₂ := inter_set J r₁ (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.2 hbst₁'.2.1 hspb.2
            rw [hs₁] at hx
            rw [hs₂] at hy
            simp only [Set.mem_inter_iff] at hx hy
            exact lt_trans (hbst₁'.2.2.1 x hx.1) (hbst₁'.2.2.2 y hy.1))

/-- `inter` preserves `inv` (book §10.2.1). -/
public theorem inter_inv (t₁ t₂ : Tree α β) (hinv₁ : J.inv t₁) (hinv₂ : J.inv t₂) :
    J.inv (inter J t₁ t₂) := by
  induction t₁ generalizing t₂ with
  | Leaf => exact J.inv_leaf
  | Node l₁ kv r₁ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    have hinv₁' : J.inv l₁ ∧ J.inv r₁ := J.inv_node l₁ (a, b) r₁ hinv₁
    cases t₂ with
    | Leaf => exact J.inv_leaf
    | Node l₂ kv₂ r₂ =>
      obtain ⟨a₂, b₂⟩ := kv₂
      have hspi := split_inv J (Tree.Node l₂ (a₂, b₂) r₂) a hinv₂
      by_cases hb : (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.1 = true
      · simp only [inter, ite_eq_left hb]
        exact J.inv_join _ _ _
          (ihl (split J a (Tree.Node l₂ (a₂, b₂) r₂)).1 hinv₁'.1 hspi.1)
          (ihr (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.2 hinv₁'.2 hspi.2)
      · simp only [inter, ite_eq_right hb]
        exact join2_inv J
          (ihl (split J a (Tree.Node l₂ (a₂, b₂) r₂)).1 hinv₁'.1 hspi.1)
          (ihr (split J a (Tree.Node l₂ (a₂, b₂) r₂)).2.2 hinv₁'.2 hspi.2)

/-- `diff` set property (book §10.2.1). -/
public theorem diff_set (t₁ t₂ : Tree α β) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    set_tree (diff J t₁ t₂) = set_tree t₁ \ set_tree t₂ := by
  induction t₂ generalizing t₁ with
  | Leaf => simp [diff_right_leaf, set_tree]
  | Node l₂ kv r₂ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    have hbst₂' : bst l₂ ∧ bst r₂ ∧ (∀ x ∈ set_tree l₂, x < a) ∧ (∀ y ∈ set_tree r₂, a < y) := hbst₂
    have hsp := split_set J t₁ a hbst₁
    have hspb := split_bst J t₁ a hbst₁
    have hdiff : diff J t₁ (Tree.Node l₂ (a, b) r₂) =
        join2 J (diff J (split J a t₁).1 l₂) (diff J (split J a t₁).2.2 r₂) :=
      diff_node J t₁ l₂ r₂ a b
    rw [hdiff, join2_set, ihl (split J a t₁).1 hspb.1 hbst₂'.1, ihr (split J a t₁).2.2 hspb.2 hbst₂'.2.1,
      hsp.1, hsp.2.1, set_tree_node]
    ext y
    rcases lt_trichotomy y a with hlt | heq | hgt
    · have hna : ¬ a < y := not_lt_of_ge (le_of_lt hlt)
      have hne : y ≠ a := ne_of_lt hlt
      have hnr : y ∉ set_tree r₂ := fun h => absurd (lt_trans hlt (hbst₂'.2.2.2 y h)) (lt_irrefl y)
      simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff, hlt, hna, hne, hnr] ; tauto
    · subst heq
      simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff, lt_irrefl] ; tauto
    · have hna : ¬ y < a := not_lt_of_ge (le_of_lt hgt)
      have hne : y ≠ a := ne_of_gt hgt
      have hnl : y ∉ set_tree l₂ := fun h => absurd (lt_trans (hbst₂'.2.2.1 y h) hgt) (lt_irrefl y)
      simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff, hgt, hna, hne, hnl] ; tauto

/-- `diff` preserves `bst` (book §10.2.1). -/
public theorem diff_bst (t₁ t₂ : Tree α β) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (diff J t₁ t₂) := by
  induction t₂ generalizing t₁ with
  | Leaf => rw [diff_right_leaf]; exact hbst₁
  | Node l₂ kv r₂ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    have hbst₂' : bst l₂ ∧ bst r₂ ∧ (∀ x ∈ set_tree l₂, x < a) ∧ (∀ y ∈ set_tree r₂, a < y) := hbst₂
    have hsp := split_set J t₁ a hbst₁
    have hspb := split_bst J t₁ a hbst₁
    have hdiff : diff J t₁ (Tree.Node l₂ (a, b) r₂) =
        join2 J (diff J (split J a t₁).1 l₂) (diff J (split J a t₁).2.2 r₂) :=
      diff_node J t₁ l₂ r₂ a b
    rw [hdiff]
    exact join2_bst J (ihl (split J a t₁).1 hspb.1 hbst₂'.1) (ihr (split J a t₁).2.2 hspb.2 hbst₂'.2.1) (by
      intro x hx y hy
      have hs₁ := diff_set J (split J a t₁).1 l₂ hspb.1 hbst₂'.1
      have hs₂ := diff_set J (split J a t₁).2.2 r₂ hspb.2 hbst₂'.2.1
      rw [hs₁] at hx
      rw [hs₂] at hy
      simp only [Set.mem_sdiff] at hx hy
      have hx' : x ∈ set_tree t₁ ∧ x < a := by
        have hss := hsp.1
        rw [hss] at hx
        simp only [Set.mem_sep_iff] at hx
        exact hx.1
      have hy' : y ∈ set_tree t₁ ∧ a < y := by
        have hss := hsp.2.1
        rw [hss] at hy
        simp only [Set.mem_sep_iff] at hy
        exact hy.1
      exact lt_trans hx'.2 hy'.2)

/-- `diff` preserves `inv` (book §10.2.1). -/
public theorem diff_inv (t₁ t₂ : Tree α β) (hinv₁ : J.inv t₁) (hinv₂ : J.inv t₂) :
    J.inv (diff J t₁ t₂) := by
  induction t₂ generalizing t₁ with
  | Leaf => rw [diff_right_leaf]; exact hinv₁
  | Node l₂ kv r₂ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    have hinv₂' : J.inv l₂ ∧ J.inv r₂ := J.inv_node l₂ (a, b) r₂ hinv₂
    have hspi := split_inv J t₁ a hinv₁
    have hdiff : diff J t₁ (Tree.Node l₂ (a, b) r₂) =
        join2 J (diff J (split J a t₁).1 l₂) (diff J (split J a t₁).2.2 r₂) :=
      diff_node J t₁ l₂ r₂ a b
    rw [hdiff]
    exact join2_inv J (ihl (split J a t₁).1 hspi.1 hinv₂'.1) (ihr (split J a t₁).2.2 hspi.2 hinv₂'.2)

/-- `insert` via `split` + `join`: set property. -/
public theorem insert_set (x : α) (t : Tree α β) (hbst : bst t) :
    set_tree (insert J x t) = set_tree t ∪ {x} := by
  have hsp := split_set J t x hbst
  simp only [insert, J.set_join, hsp.1, hsp.2.1]
  ext y
  simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff]
  have htri : y < x ∨ y = x ∨ x < y := lt_trichotomy y x
  aesop

/-- `insert` preserves `bst`. -/
public theorem insert_bst (x : α) (t : Tree α β) (hbst : bst t) :
    bst (insert J x t) := by
  have hspb := split_bst J t x hbst
  have hsp := split_set J t x hbst
  simp only [insert]
  exact J.bst_join (split J x t).1 x default (split J x t).2.2
    ⟨hspb.1, hspb.2, by
      intro y hy
      rw [hsp.1] at hy
      simp only [Set.mem_sep_iff] at hy
      exact hy.2, by
      intro y hy
      rw [hsp.2.1] at hy
      simp only [Set.mem_sep_iff] at hy
      exact hy.2⟩

/-- `insert` preserves `inv`. -/
public theorem insert_inv (x : α) (t : Tree α β) (hinv : J.inv t) :
    J.inv (insert J x t) := by
  have hspi := split_inv J t x hinv
  simp only [insert]
  exact J.inv_join _ _ _ hspi.1 hspi.2

/-- `delete` via `split` + `join2`: set property. -/
public theorem delete_set (x : α) (t : Tree α β) (hbst : bst t) :
    set_tree (delete J x t) = set_tree t \ {x} := by
  have hsp := split_set J t x hbst
  simp only [delete, join2_set, hsp.1, hsp.2.1]
  ext y
  simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff]
  have htri : y < x ∨ y = x ∨ x < y := lt_trichotomy y x
  aesop

/-- `delete` preserves `bst`. -/
public theorem delete_bst (x : α) (t : Tree α β) (hbst : bst t) :
    bst (delete J x t) := by
  have hspb := split_bst J t x hbst
  have hsp := split_set J t x hbst
  simp only [delete]
  exact join2_bst J hspb.1 hspb.2 (by
    intro y hy z hz
    rw [hsp.1] at hy
    rw [hsp.2.1] at hz
    simp only [Set.mem_sep_iff] at hy hz
    exact lt_trans hy.2 hz.2)

/-- `delete` preserves `inv`. -/
public theorem delete_inv (x : α) (t : Tree α β) (hinv : J.inv t) :
    J.inv (delete J x t) := by
  have hspi := split_inv J t x hinv
  simp only [delete]
  exact join2_inv J hspi.1 hspi.2

/-- Singleton tree `join ⟨⟩ x ⟨⟩` (used in Exercise 10.1). -/
public def singleton (x : α) : Tree α β := J.join Tree.Leaf x Tree.Leaf

public theorem singleton_set (x : α) : set_tree (singleton J x) = {x} := by
  simp [singleton, J.set_join]

public theorem singleton_bst (x : α) : bst (singleton J x) := by
  exact J.bst_join _ _ default _
    ⟨trivial, trivial, by simp, by simp⟩

public theorem singleton_inv (x : α) : J.inv (singleton J x) :=
  J.inv_join _ _ _ J.inv_leaf J.inv_leaf

/-- Exercise 10.1: `insert'` via `union` and `join`. The singleton comes
first: `union` recurses on its first argument, so this walks only the
singleton (one `split` of `t`), instead of traversing all of `t`. -/
public def insert' (x : α) (t : Tree α β) : Tree α β := union J (singleton J x) t

public theorem insert'_set (x : α) (t : Tree α β) (hbst : bst t) :
    set_tree (insert' J x t) = set_tree t ∪ {x} := by
  simp only [insert', union_set J (singleton J x) t hbst, singleton_set]
  exact Set.union_comm _ _

public theorem insert'_bst (x : α) (t : Tree α β) (hbst : bst t) :
    bst (insert' J x t) :=
  union_bst J (singleton J x) t (singleton_bst J x) hbst

public theorem insert'_inv (x : α) (t : Tree α β) (hinv : J.inv t) :
    J.inv (insert' J x t) :=
  union_inv J (singleton J x) t (singleton_inv J x) hinv

/-- Exercise 10.1: `delete'` via `diff`. -/
public def delete' (x : α) (t : Tree α β) : Tree α β := diff J t (singleton J x)

public theorem delete'_set (x : α) (t : Tree α β) (hbst : bst t) :
    set_tree (delete' J x t) = set_tree t \ {x} := by
  simp [delete', diff_set J t (singleton J x) hbst (singleton_bst J x), singleton_set]

public theorem delete'_bst (x : α) (t : Tree α β) (hbst : bst t) :
    bst (delete' J x t) :=
  diff_bst J t (singleton J x) hbst (singleton_bst J x)

public theorem delete'_inv (x : α) (t : Tree α β) (hinv : J.inv t) :
    J.inv (delete' J x t) :=
  diff_inv J t (singleton J x) hinv (singleton_inv J x)

/-- Exercise 10.2: `diff1` — pattern-match on `t₁`, split `t₂`. Unlike
`diff` (whose pivot comes from `t₂`, so it is always present), the pivot
`a` here comes from `t₁` and may or may not be in `t₂`: include it via
`join` when it is absent (`b = false`), exclude it via `join2` when
present (`b = true`). The exercise changes only the recursive equation of
Fig. 10.3, so both base cases stay: `diff1 Leaf t₂ = Leaf` and
`diff1 t₁ Leaf = t₁` (without the second, `diff1 t Leaf` would rebuild `t`
with `join`, which need not return `t`: red–black `join` repaints a red
root). -/
public def diff1 : Tree α β → Tree α β → Tree α β
  | .Leaf, _ => Tree.Leaf
  | t₁, .Leaf => t₁
  | .Node l₁ (a, _) r₁, t₂ =>
    let s := split J a t₂
    if s.2.1 then
      join2 J (diff1 l₁ s.1) (diff1 r₁ s.2.2)
    else
      J.join (diff1 l₁ s.1) a (diff1 r₁ s.2.2)

/-- Fig. 10.3's second base case, kept by Exercise 10.2's `diff1`. -/
private theorem diff1_right_leaf (t₁ : Tree α β) : diff1 J t₁ Tree.Leaf = t₁ := by
  cases t₁ <;> rfl

/-- The recursive equation of `diff1`, for a nonempty second tree. -/
private theorem diff1_node (l₁ r₁ t₂ : Tree α β) (a : α) (b : β) (h₂ : t₂ ≠ Tree.Leaf) :
    diff1 J (Tree.Node l₁ (a, b) r₁) t₂ =
      if (split J a t₂).2.1 then
        join2 J (diff1 J l₁ (split J a t₂).1) (diff1 J r₁ (split J a t₂).2.2)
      else J.join (diff1 J l₁ (split J a t₂).1) a (diff1 J r₁ (split J a t₂).2.2) := by
  cases t₂ with
  | Leaf => exact absurd rfl h₂
  | Node l₂ kv₂ r₂ => rfl

public theorem diff1_set (t₁ t₂ : Tree α β) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    set_tree (diff1 J t₁ t₂) = set_tree t₁ \ set_tree t₂ := by
  induction t₁ generalizing t₂ with
  | Leaf => simp [diff1]
  | Node l₁ kv r₁ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    by_cases h₂ : t₂ = Tree.Leaf
    · subst h₂
      rw [diff1_right_leaf]
      simp [set_tree]
    have hbst₁' : bst l₁ ∧ bst r₁ ∧ (∀ x ∈ set_tree l₁, x < a) ∧ (∀ y ∈ set_tree r₁, a < y) := hbst₁
    have hsp := split_set J t₂ a hbst₂
    have hspb := split_bst J t₂ a hbst₂
    by_cases hb : (split J a t₂).2.1 = true
    · have ha : a ∈ set_tree t₂ := hsp.2.2.mp hb
      rw [diff1_node J l₁ r₁ t₂ a b h₂]
      simp only [ite_eq_left hb, join2_set, ihl (split J a t₂).1 hbst₁'.1 hspb.1,
        ihr (split J a t₂).2.2 hbst₁'.2.1 hspb.2, hsp.1, hsp.2.1, set_tree_node]
      ext y
      rcases lt_trichotomy y a with hlt | heq | hgt
      · have hna : ¬ a < y := not_lt_of_ge (le_of_lt hlt)
        have hne : y ≠ a := ne_of_lt hlt
        have hnr : y ∉ set_tree r₁ := fun h => absurd (lt_trans hlt (hbst₁'.2.2.2 y h)) (lt_irrefl y)
        simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff, hlt, hna, hne, hnr] ; tauto
      · subst heq
        have hnl : y ∉ set_tree l₁ := fun h => absurd (hbst₁'.2.2.1 y h) (lt_irrefl y)
        have hnr : y ∉ set_tree r₁ := fun h => absurd (hbst₁'.2.2.2 y h) (lt_irrefl y)
        simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff, lt_irrefl,
          hnl, hnr, ha] ; tauto
      · have hna : ¬ y < a := not_lt_of_ge (le_of_lt hgt)
        have hne : y ≠ a := ne_of_gt hgt
        have hnl : y ∉ set_tree l₁ := fun h => absurd (lt_trans (hbst₁'.2.2.1 y h) hgt) (lt_irrefl y)
        simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff, hgt, hna, hne, hnl] ; tauto
    · have hna2 : a ∉ set_tree t₂ := by
        intro ha
        exact hb (hsp.2.2.mpr ha)
      rw [diff1_node J l₁ r₁ t₂ a b h₂]
      simp only [ite_eq_right hb, J.set_join, ihl (split J a t₂).1 hbst₁'.1 hspb.1,
        ihr (split J a t₂).2.2 hbst₁'.2.1 hspb.2, hsp.1, hsp.2.1, set_tree_node]
      ext y
      rcases lt_trichotomy y a with hlt | heq | hgt
      · have hna : ¬ a < y := not_lt_of_ge (le_of_lt hlt)
        have hne : y ≠ a := ne_of_lt hlt
        have hnr : y ∉ set_tree r₁ := fun h => absurd (lt_trans hlt (hbst₁'.2.2.2 y h)) (lt_irrefl y)
        simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff, hlt, hna, hne, hnr] ; tauto
      · subst heq
        have hnl : y ∉ set_tree l₁ := fun h => absurd (hbst₁'.2.2.1 y h) (lt_irrefl y)
        have hnr : y ∉ set_tree r₁ := fun h => absurd (hbst₁'.2.2.2 y h) (lt_irrefl y)
        simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff, lt_irrefl,
          hnl, hnr, hna2] ; tauto
      · have hna : ¬ y < a := not_lt_of_ge (le_of_lt hgt)
        have hne : y ≠ a := ne_of_gt hgt
        have hnl : y ∉ set_tree l₁ := fun h => absurd (lt_trans (hbst₁'.2.2.1 y h) hgt) (lt_irrefl y)
        simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff, Set.mem_sdiff, hgt, hna, hne, hnl] ; tauto

public theorem diff1_bst (t₁ t₂ : Tree α β) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (diff1 J t₁ t₂) := by
  induction t₁ generalizing t₂ with
  | Leaf => exact trivial
  | Node l₁ kv r₁ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    by_cases h₂ : t₂ = Tree.Leaf
    · subst h₂
      rw [diff1_right_leaf]
      exact hbst₁
    have hbst₁' : bst l₁ ∧ bst r₁ ∧ (∀ x ∈ set_tree l₁, x < a) ∧ (∀ y ∈ set_tree r₁, a < y) := hbst₁
    have hspb := split_bst J t₂ a hbst₂
    by_cases hb : (split J a t₂).2.1 = true
    · rw [diff1_node J l₁ r₁ t₂ a b h₂]
      simp only [ite_eq_left hb]
      exact join2_bst J (ihl (split J a t₂).1 hbst₁'.1 hspb.1) (ihr (split J a t₂).2.2 hbst₁'.2.1 hspb.2) (by
        intro x hx y hy
        have hs₁ := diff1_set J l₁ (split J a t₂).1 hbst₁'.1 hspb.1
        have hs₂ := diff1_set J r₁ (split J a t₂).2.2 hbst₁'.2.1 hspb.2
        rw [hs₁] at hx
        rw [hs₂] at hy
        simp only [Set.mem_sdiff] at hx hy
        exact lt_trans (hbst₁'.2.2.1 x hx.1) (hbst₁'.2.2.2 y hy.1))
    · rw [diff1_node J l₁ r₁ t₂ a b h₂]
      simp only [ite_eq_right hb]
      exact J.bst_join (diff1 J l₁ (split J a t₂).1) a b (diff1 J r₁ (split J a t₂).2.2)
        ⟨ihl (split J a t₂).1 hbst₁'.1 hspb.1, ihr (split J a t₂).2.2 hbst₁'.2.1 hspb.2, by
          intro x hx
          have hs₁ := diff1_set J l₁ (split J a t₂).1 hbst₁'.1 hspb.1
          rw [hs₁] at hx
          simp only [Set.mem_sdiff] at hx
          exact hbst₁'.2.2.1 x hx.1, by
          intro y hy
          have hs₂ := diff1_set J r₁ (split J a t₂).2.2 hbst₁'.2.1 hspb.2
          rw [hs₂] at hy
          simp only [Set.mem_sdiff] at hy
          exact hbst₁'.2.2.2 y hy.1⟩

/-- `diff1` preserves `inv` (Exercise 10.2). -/
public theorem diff1_inv (t₁ t₂ : Tree α β) (hinv₁ : J.inv t₁) (hinv₂ : J.inv t₂) :
    J.inv (diff1 J t₁ t₂) := by
  induction t₁ generalizing t₂ with
  | Leaf => exact J.inv_leaf
  | Node l₁ kv r₁ ihl ihr =>
    obtain ⟨a, b⟩ := kv
    by_cases h₂ : t₂ = Tree.Leaf
    · subst h₂
      rw [diff1_right_leaf]
      exact hinv₁
    have hinv₁' : J.inv l₁ ∧ J.inv r₁ := J.inv_node l₁ (a, b) r₁ hinv₁
    have hspi := split_inv J t₂ a hinv₂
    by_cases hb : (split J a t₂).2.1 = true
    · rw [diff1_node J l₁ r₁ t₂ a b h₂]
      simp only [ite_eq_left hb]
      exact join2_inv J (ihl (split J a t₂).1 hinv₁'.1 hspi.1)
        (ihr (split J a t₂).2.2 hinv₁'.2 hspi.2)
    · rw [diff1_node J l₁ r₁ t₂ a b h₂]
      simp only [ite_eq_right hb]
      exact J.inv_join _ _ _ (ihl (split J a t₂).1 hinv₁'.1 hspi.1)
        (ihr (split J a t₂).2.2 hinv₁'.2 hspi.2)



/-- Number of nodes (Isabelle `size`). Named `tsize` to avoid clashing with
generic `size` lemmas. -/
public def tsize : Tree α β → ℕ
  | .Leaf => 0
  | .Node l _ r => tsize l + tsize r + 1

end JoinableBinarySearchTree

end Cslib.Algorithms.Lean
