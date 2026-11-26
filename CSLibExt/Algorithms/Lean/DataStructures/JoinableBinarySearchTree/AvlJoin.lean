/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Joinable_BST_Work_Bounds/StronglyJoinableAVL.thy` (Archive of Formal Proofs, entry
`Joinable_BST_Work_Bounds`, https://www.isa-afp.org/entries/Joinable_BST_Work_Bounds.html):
Copyright (c) 2004, Gerwin Klein, Tobias Nipkow, Lawrence C. Paulson
Copyright (c) 2004, contributing authors (see author notice in individual files)
All rights reserved.
Licensed under the BSD License of the Archive of Formal Proofs (https://isa-afp.org/LICENSE).
Authors: Marco Haucke

`src/HOL/Data_Structures/AVL_Set_Code.thy` (Isabelle/HOL, `HOL-Data_Structures`):
Copyright (c) 1986-2026, University of Cambridge, Technische Universitaet Muenchen,
and contributors. All rights reserved.
Licensed under the 3-clause BSD license in Isabelle's `COPYRIGHT` file
(https://github.com/isabelle-prover/mirror-isabelle/blob/master/COPYRIGHT).
Authors: Tobias Nipkow, Daniel Stüwe

`src/HOL/Data_Structures/AVL_Set.thy` (Isabelle/HOL, `HOL-Data_Structures`):
Copyright (c) 1986-2026, University of Cambridge, Technische Universitaet Muenchen,
and contributors. All rights reserved.
Licensed under the 3-clause BSD license in Isabelle's `COPYRIGHT` file
(https://github.com/isabelle-prover/mirror-isabelle/blob/master/COPYRIGHT).
Authors: Tobias Nipkow
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.Basic
public import Mathlib.Tactic

/-!
# Joinable binary search trees: AVL join

The AVL `join` of Chapter 10 (§10.3 is red–black only; the AVL
instantiation lives in the AFP entry): the Chapter 9 AVL prerequisites
`ht` / `height` / `node` / `avl` / `balL` / `balR`, the spine-descent
`avlJoinR` / `avlJoinL` / `avlJoin`, with `set` / `bst` / `avl` + height
correctness, the `JoinData` instance `avlJoinData`, and the `avlUnion` /
`avlInter` / `avlDiff` / `avlInsert` / `avlDelete` corollaries of the
generic framework.

## Provenance

The AVL prerequisites (the AVL trees of book Chapter 9) follow Isabelle/HOL's
bundled `HOL-Data_Structures` library: `ht` / `node` / `balL` / `balR` follow
`AVL_Set_Code.thy`, and `avl`, `ht_height`, `height_node` and `balL_avl` /
`balR_avl` (Isabelle `avl_balL` / `avl_balR`) follow `AVL_Set.thy`.
`avlJoinR` / `avlJoinL` / `avlJoin`, the `set` / `bst` lemmas for `balL` /
`balR` and the `join` lemmas follow `StronglyJoinableAVL.thy` in the AFP
entry `Joinable_BST_Work_Bounds`. In the docstrings below, names cited as
Isabelle lemmas are from that AFP theory, except `ht_height` (`AVL_Set.thy`).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace JoinableBinarySearchTree

variable {α : Type u} [LinearOrder α]

/-! ### AVL join (book Ch. 9 + `StronglyJoinableAVL.thy`)

AVL trees are height-augmented binary trees: `Tree α Nat`, where the `Nat`
stored in each node is the cached height of the subtree. `ht` reads the
cached height, `height` recomputes it from the structure, and `avl` says
the cached heights are correct and sibling heights differ by at most one
(book Ch. 9, §9.2). The `join` here is the one from
`StronglyJoinableAVL.thy` (spine descent + `balL` / `balR`, following
Blelloch et al. 2022). -/

/-- Stored height accessor (`ht`, book Ch. 9). -/
public def ht : Tree α Nat → Nat
  | .Leaf => 0
  | .Node _ (_, n) _ => n

/-- Computed height (`h`, book Ch. 9; Isabelle `height`). -/
public def height : Tree α Nat → Nat
  | .Leaf => 0
  | .Node l _ r => max (height l) (height r) + 1

/-- Smart constructor: the height field is set to `max (ht l) (ht r) + 1`
(book Ch. 9, `node`). -/
public def node (l : Tree α Nat) (a : α) (r : Tree α Nat) : Tree α Nat :=
  Tree.Node l (a, max (ht l) (ht r) + 1) r

/-- The AVL invariant (book Ch. 9, `avl`): cached heights are correct and
sibling (computed) heights differ by at most one. -/
public def avl : Tree α Nat → Prop
  | .Leaf => True
  | .Node l (_, n) r =>
      ((height l : ℤ) - (height r : ℤ)).natAbs ≤ 1 ∧
        n = max (height l) (height r) + 1 ∧ avl l ∧ avl r

/-- `balL`: readjust after an insertion into the left child (book Fig. 9.1).
The `Leaf` branches are dead code: `ht AB = ht C + 2` is impossible for
`AB = Leaf` (it would need `0 = ht C + 2`), and in the `else` branch
`ht B > ht A ≥ 0` is impossible for `B = Leaf`. -/
public def balL (AB : Tree α Nat) (c : α) (C : Tree α Nat) : Tree α Nat :=
  if ht AB = ht C + 2 then
    match AB with
    | .Node A (a, _) B =>
      if ht B ≤ ht A then node A a (node B c C)
      else match B with
        | .Node B1 (b, _) B2 => node (node A a B1) b (node B2 c C)
        | .Leaf => node AB c C
    | .Leaf => node AB c C
  else node AB c C

/-- `balR`: mirror of `balL` (book Fig. 9.2). -/
public def balR (A : Tree α Nat) (a : α) (BC : Tree α Nat) : Tree α Nat :=
  if ht BC = ht A + 2 then
    match BC with
    | .Node B (c, _) C =>
      if ht B ≤ ht C then node (node A a B) c C
      else match B with
        | .Node B1 (b, _) B2 => node (node A a B1) b (node B2 c C)
        | .Leaf => node A a BC
    | .Leaf => node A a BC
  else node A a BC

/-- AVL `joinR` (`StronglyJoinableAVL.thy`): descend the right spine of `l`.
The `Leaf` case is dead code: `joinR` is only called when
`ht l > ht r + 1`, which `Leaf` cannot satisfy. -/
public def avlJoinR : Tree α Nat → α → Tree α Nat → Tree α Nat
  | .Leaf, a, R => node .Leaf a R
  | .Node l (k, _) r, a, R =>
    if ht r ≤ ht R + 1 then balR l k (node r a R)
    else balR l k (avlJoinR r a R)

/-- AVL `joinL` (`StronglyJoinableAVL.thy`): descend the left spine of `r`. -/
public def avlJoinL : Tree α Nat → α → Tree α Nat → Tree α Nat
  | L, a, .Leaf => node L a .Leaf
  | L, a, .Node l (k, _) r =>
    if ht l ≤ ht L + 1 then balL (node L a l) k r
    else balL (avlJoinL L a l) k r

/-- AVL `join` (`StronglyJoinableAVL.thy`). -/
public def avlJoin (l : Tree α Nat) (a : α) (r : Tree α Nat) : Tree α Nat :=
  if ht l > ht r + 1 then avlJoinR l a r
  else if ht r > ht l + 1 then avlJoinL l a r
  else node l a r

public theorem set_node (l r : Tree α Nat) (a : α) :
    set_tree (node l a r) = set_tree l ∪ {a} ∪ set_tree r := rfl

public theorem ht_node (l r : Tree α Nat) (a : α) :
    ht (node l a r) = max (ht l) (ht r) + 1 := rfl

public theorem height_node (l r : Tree α Nat) (a : α) :
    height (node l a r) = max (height l) (height r) + 1 := rfl

/-- For an AVL tree the cached height equals the computed height
(Isabelle `ht_height`). -/
public theorem ht_height (t : Tree α Nat) (h : avl t) : ht t = height t := by
  cases t with
  | Leaf => rfl
  | Node l kv r =>
    obtain ⟨a, n⟩ := kv
    exact h.2.1

/-- `set` for `balL` (Isabelle `balL_set`). -/
public theorem balL_set (l : Tree α Nat) (a : α) (r : Tree α Nat) :
    set_tree (balL l a r) = set_tree l ∪ {a} ∪ set_tree r := by
  fun_cases balL l a r <;> ext y <;> simp only [node, set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> tauto

/-- `set` for `balR` (Isabelle `balR_set`). -/
public theorem balR_set (l : Tree α Nat) (a : α) (r : Tree α Nat) :
    set_tree (balR l a r) = set_tree l ∪ {a} ∪ set_tree r := by
  fun_cases balR l a r <;> ext y <;> simp only [node, set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> tauto

/-- `bst` for `balL` (Isabelle `balL_bst`). -/
public theorem balL_bst (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (hbst_l : bst l) (hbst_r : bst r)
    (hl : ∀ x ∈ set_tree l, x < a) (hr : ∀ y ∈ set_tree r, a < y) :
    bst (balL l a r) := by
  fun_cases balL l a r <;> simp_all [bst, node, set_tree] <;> aesop (add unsafe lt_trans)

/-- `bst` for `balR` (Isabelle `balR_bst`). -/
public theorem balR_bst (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (hbst_l : bst l) (hbst_r : bst r)
    (hl : ∀ x ∈ set_tree l, x < a) (hr : ∀ y ∈ set_tree r, a < y) :
    bst (balR l a r) := by
  fun_cases balR l a r <;> simp_all [bst, node, set_tree] <;> aesop (add unsafe lt_trans)



/-- `avl` for `node`: the AVL invariant for a smart-constructed node. -/
public theorem avl_node (l r : Tree α Nat) (a : α) (h₁ : avl l) (h₂ : avl r)
    (hbal : ((height l : ℤ) - (height r : ℤ)).natAbs ≤ 1) : avl (node l a r) := by
  refine ⟨hbal, ?_, h₁, h₂⟩
  rw [ht_height l h₁, ht_height r h₂]

/-- `balL` preserves `avl` (book Ch. 9, §9.2.2). The side conditions are
the book's, with truncated subtraction on `ℕ`. -/
public theorem balL_avl (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (havl_l : avl l) (havl_r : avl r)
    (h1 : height r - 1 ≤ height l) (h2 : height l ≤ height r + 2) :
    avl (balL l a r) := by
  have ht_l : ht l = height l := ht_height l havl_l
  have ht_r : ht r = height r := ht_height r havl_r
  by_cases hcond : ht l = ht r + 2
  · cases l with
    | Leaf =>
      simp only [ht] at hcond
      exact absurd hcond (by omega)
    | Node A kv B =>
      obtain ⟨a', n⟩ := kv
      have hA : avl A := havl_l.2.2.1
      have hB : avl B := havl_l.2.2.2
      have hAB : ((height A : ℤ) - (height B : ℤ)).natAbs ≤ 1 := havl_l.1
      have htA : ht A = height A := ht_height A hA
      have htB : ht B = height B := ht_height B hB
      have hNode : height (Tree.Node A (a', n) B) = max (height A) (height B) + 1 := rfl
      by_cases hle : ht B ≤ ht A
      · rw [show balL (Tree.Node A (a', n) B) a r = node A a' (node B a r) from
          by simp [balL, hcond, hle]]
        have hnodeBC : height (node B a r) = max (height B) (height r) + 1 := rfl
        exact avl_node A (node B a r) a' hA
          (avl_node B r a hB havl_r (by omega)) (by omega)
      · cases B with
        | Leaf =>
          simp only [ht] at hle
          exact absurd (Nat.zero_le (ht A)) hle
        | Node B1 kv2 B2 =>
          obtain ⟨b, n2⟩ := kv2
          have hB1 : avl B1 := hB.2.2.1
          have hB2 : avl B2 := hB.2.2.2
          have hBalB : ((height B1 : ℤ) - (height B2 : ℤ)).natAbs ≤ 1 := hB.1
          have htB1 : ht B1 = height B1 := ht_height B1 hB1
          have htB2 : ht B2 = height B2 := ht_height B2 hB2
          have hNodeB : height (Tree.Node B1 (b, n2) B2) = max (height B1) (height B2) + 1 := rfl
          rw [show balL (Tree.Node A (a', n) (Tree.Node B1 (b, n2) B2)) a r =
              node (node A a' B1) b (node B2 a r) from by simp [balL, hcond, hle]]
          have hnodeL : height (node A a' B1) = max (height A) (height B1) + 1 := rfl
          have hnodeR : height (node B2 a r) = max (height B2) (height r) + 1 := rfl
          exact avl_node (node A a' B1) (node B2 a r) b
            (avl_node A B1 a' hA hB1 (by omega)) (avl_node B2 r a hB2 havl_r (by omega)) (by omega)
  · rw [show balL l a r = node l a r from by simp [balL, hcond]]
    refine avl_node l r a havl_l havl_r ?_
    omega

/-- `balR` preserves `avl` (book Ch. 9, §9.2.2). -/
public theorem balR_avl (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (havl_l : avl l) (havl_r : avl r)
    (h1 : height l - 1 ≤ height r) (h2 : height r ≤ height l + 2) :
    avl (balR l a r) := by
  have ht_l : ht l = height l := ht_height l havl_l
  have ht_r : ht r = height r := ht_height r havl_r
  by_cases hcond : ht r = ht l + 2
  · cases r with
    | Leaf =>
      simp only [ht] at hcond
      exact absurd hcond (by omega)
    | Node B kv C =>
      obtain ⟨c, n⟩ := kv
      have hB : avl B := havl_r.2.2.1
      have hC : avl C := havl_r.2.2.2
      have hBC : ((height B : ℤ) - (height C : ℤ)).natAbs ≤ 1 := havl_r.1
      have htB : ht B = height B := ht_height B hB
      have htC : ht C = height C := ht_height C hC
      have hNode : height (Tree.Node B (c, n) C) = max (height B) (height C) + 1 := rfl
      by_cases hle : ht B ≤ ht C
      · rw [show balR l a (Tree.Node B (c, n) C) = node (node l a B) c C from
          by simp [balR, hcond, hle]]
        have hnodeLB : height (node l a B) = max (height l) (height B) + 1 := rfl
        exact avl_node (node l a B) C c
          (avl_node l B a havl_l hB (by omega)) hC (by omega)
      · cases B with
        | Leaf =>
          simp only [ht] at hle
          exact absurd (Nat.zero_le (ht C)) hle
        | Node B1 kv2 B2 =>
          obtain ⟨b, n2⟩ := kv2
          have hB1 : avl B1 := hB.2.2.1
          have hB2 : avl B2 := hB.2.2.2
          have hBalB : ((height B1 : ℤ) - (height B2 : ℤ)).natAbs ≤ 1 := hB.1
          have htB1 : ht B1 = height B1 := ht_height B1 hB1
          have htB2 : ht B2 = height B2 := ht_height B2 hB2
          have hNodeB : height (Tree.Node B1 (b, n2) B2) = max (height B1) (height B2) + 1 := rfl
          rw [show balR l a (Tree.Node (Tree.Node B1 (b, n2) B2) (c, n) C) =
              node (node l a B1) b (node B2 c C) from by simp [balR, hcond, hle]]
          have hnodeL : height (node l a B1) = max (height l) (height B1) + 1 := rfl
          have hnodeR : height (node B2 c C) = max (height B2) (height C) + 1 := rfl
          exact avl_node (node l a B1) (node B2 c C) b
            (avl_node l B1 a havl_l hB1 (by omega)) (avl_node B2 C c hB2 hC (by omega)) (by omega)
  · rw [show balR l a r = node l a r from by simp [balR, hcond]]
    refine avl_node l r a havl_l havl_r ?_
    omega



/-- `set` for AVL `joinR` (Isabelle `joinR_set`). -/
public theorem avlJoinR_set (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (hgt : ht l > ht r + 1) :
    set_tree (avlJoinR l a r) = set_tree l ∪ {a} ∪ set_tree r := by
  induction l generalizing r with
  | Leaf => simp [ht] at hgt
  | Node l' kv r' ihl ihr =>
    obtain ⟨k, k2⟩ := kv
    by_cases hb : ht r' ≤ ht r + 1
    · simp only [avlJoinR, ite_eq_left hb]
      rw [balR_set, set_node]
      ext y
      simp only [Set.mem_union, Set.mem_singleton_iff, set_tree_node]
      tauto
    · simp only [avlJoinR, ite_eq_right hb]
      have hgt' : ht r' > ht r + 1 := by omega
      rw [balR_set, ihr r hgt']
      ext y
      simp only [Set.mem_union, Set.mem_singleton_iff, set_tree_node]
      tauto

/-- `set` for AVL `joinL` (Isabelle `joinL_set`). -/
public theorem avlJoinL_set (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (hgt : ht r > ht l + 1) :
    set_tree (avlJoinL l a r) = set_tree l ∪ {a} ∪ set_tree r := by
  induction r generalizing l with
  | Leaf => simp [ht] at hgt
  | Node l' kv r' ihl ihr =>
    obtain ⟨k, k2⟩ := kv
    by_cases hb : ht l' ≤ ht l + 1
    · simp only [avlJoinL, ite_eq_left hb]
      rw [balL_set, set_node]
      ext y
      simp only [Set.mem_union, Set.mem_singleton_iff, set_tree_node]
      tauto
    · simp only [avlJoinL, ite_eq_right hb]
      have hgt' : ht l' > ht l + 1 := by omega
      rw [balL_set, ihl l hgt']
      ext y
      simp only [Set.mem_union, Set.mem_singleton_iff, set_tree_node]
      tauto

/-- `set` for AVL `join` (Isabelle `set_join`). -/
public theorem set_avlJoin (l : Tree α Nat) (a : α) (r : Tree α Nat) :
    set_tree (avlJoin l a r) = set_tree l ∪ {a} ∪ set_tree r := by
  simp only [avlJoin]
  by_cases h1 : ht l > ht r + 1
  · rw [ite_eq_left h1]; exact avlJoinR_set l a r h1
  · rw [ite_eq_right h1]
    by_cases h2 : ht r > ht l + 1
    · rw [ite_eq_left h2]; exact avlJoinL_set l a r h2
    · rw [ite_eq_right h2]; exact set_node l r a

/-- `bst` for AVL `joinR` (Isabelle `joinR_bst`). -/
public theorem avlJoinR_bst (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (hgt : ht l > ht r + 1) (hbst_l : bst l) (hbst_r : bst r)
    (hl : ∀ x ∈ set_tree l, x < a) (hr : ∀ y ∈ set_tree r, a < y) :
    bst (avlJoinR l a r) := by
  induction l generalizing r with
  | Leaf => simp [ht] at hgt
  | Node l' kv r' ihl ihr =>
    obtain ⟨k, k2⟩ := kv
    have hbst_l' : bst l' ∧ bst r' ∧ (∀ x ∈ set_tree l', x < k) ∧ (∀ y ∈ set_tree r', k < y) := hbst_l
    have hk_a : k < a := hl k (by simp [set_tree_node])
    have hnode_bst : bst (node r' a r) := by
      refine ⟨hbst_l'.2.1, hbst_r, ?_, ?_⟩
      · intro y hy
        exact hl y (by simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]; exact Or.inr hy)
      · intro y hy
        exact hr y hy
    by_cases hb : ht r' ≤ ht r + 1
    · simp only [avlJoinR, ite_eq_left hb]
      exact balR_bst l' k (node r' a r) hbst_l'.1 hnode_bst hbst_l'.2.2.1 (by
        intro y hy
        rw [set_node] at hy
        simp only [Set.mem_union, Set.mem_singleton_iff] at hy
        rcases hy with (hy | rfl) | hy
        · exact hbst_l'.2.2.2 y hy
        · exact hk_a
        · exact lt_trans hk_a (hr y hy))
    · simp only [avlJoinR, ite_eq_right hb]
      have hgt' : ht r' > ht r + 1 := by omega
      have hrec : bst (avlJoinR r' a r) :=
        ihr r hgt' hbst_l'.2.1 hbst_r (by
          intro x hx
          exact hl x (by simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]; exact Or.inr hx)) hr
      have hrec_set : set_tree (avlJoinR r' a r) = set_tree r' ∪ {a} ∪ set_tree r :=
        avlJoinR_set r' a r hgt'
      exact balR_bst l' k (avlJoinR r' a r) hbst_l'.1 hrec hbst_l'.2.2.1 (by
        intro y hy
        rw [hrec_set] at hy
        simp only [Set.mem_union, Set.mem_singleton_iff] at hy
        rcases hy with (hy | rfl) | hy
        · exact hbst_l'.2.2.2 y hy
        · exact hk_a
        · exact lt_trans hk_a (hr y hy))

/-- `bst` for AVL `joinL` (Isabelle `joinL_bst`). -/
public theorem avlJoinL_bst (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (hgt : ht r > ht l + 1) (hbst_l : bst l) (hbst_r : bst r)
    (hl : ∀ x ∈ set_tree l, x < a) (hr : ∀ y ∈ set_tree r, a < y) :
    bst (avlJoinL l a r) := by
  induction r generalizing l with
  | Leaf => simp [ht] at hgt
  | Node l' kv r' ihl ihr =>
    obtain ⟨k, k2⟩ := kv
    have hbst_r' : bst l' ∧ bst r' ∧ (∀ x ∈ set_tree l', x < k) ∧ (∀ y ∈ set_tree r', k < y) := hbst_r
    have ha_k : a < k := hr k (by simp [set_tree_node])
    have hnode_bst : bst (node l a l') := by
      refine ⟨hbst_l, hbst_r'.1, ?_, ?_⟩
      · intro y hy
        exact hl y hy
      · intro y hy
        exact hr y (by simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]; exact Or.inl (Or.inl hy))
    by_cases hb : ht l' ≤ ht l + 1
    · simp only [avlJoinL, ite_eq_left hb]
      exact balL_bst (node l a l') k r' hnode_bst hbst_r'.2.1 (by
        intro y hy
        rw [set_node] at hy
        simp only [Set.mem_union, Set.mem_singleton_iff] at hy
        rcases hy with (hy | rfl) | hy
        · exact lt_trans (hl y hy) ha_k
        · exact ha_k
        · exact hbst_r'.2.2.1 y hy) hbst_r'.2.2.2
    · simp only [avlJoinL, ite_eq_right hb]
      have hgt' : ht l' > ht l + 1 := by omega
      have hrec : bst (avlJoinL l a l') :=
        ihl l hgt' hbst_l hbst_r'.1 hl (by
          intro x hx
          exact hr x (by simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]; exact Or.inl (Or.inl hx)))
      have hrec_set : set_tree (avlJoinL l a l') = set_tree l ∪ {a} ∪ set_tree l' :=
        avlJoinL_set l a l' hgt'
      exact balL_bst (avlJoinL l a l') k r' hrec hbst_r'.2.1 (by
        intro y hy
        rw [hrec_set] at hy
        simp only [Set.mem_union, Set.mem_singleton_iff] at hy
        rcases hy with (hy | rfl) | hy
        · exact lt_trans (hl y hy) ha_k
        · exact ha_k
        · exact hbst_r'.2.2.1 y hy) hbst_r'.2.2.2

/-- `bst` for AVL `join` (Isabelle `bst_join`). -/
public theorem bst_avlJoin (l : Tree α Nat) (a : α) (r : Tree α Nat) (b : Nat)
    (h : bst (Tree.Node l (a, b) r)) : bst (avlJoin l a r) := by
  simp only [avlJoin]
  by_cases h1 : ht l > ht r + 1
  · rw [ite_eq_left h1]
    exact avlJoinR_bst l a r h1 h.1 h.2.1 h.2.2.1 h.2.2.2
  · rw [ite_eq_right h1]
    by_cases h2 : ht r > ht l + 1
    · rw [ite_eq_left h2]
      exact avlJoinL_bst l a r h2 h.1 h.2.1 h.2.2.1 h.2.2.2
    · rw [ite_eq_right h2]
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩



/-- Height of a `balL` result: between the max of the argument heights
and one more (rotation vs no rotation). Stated as an interval, which
`omega` can use directly in the `join` height proofs. -/
public theorem balL_height_mem (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (havl_l : avl l) (havl_r : avl r)
    (h1 : height r - 1 ≤ height l) (h2 : height l ≤ height r + 2) :
    max (height l) (height r) ≤ height (balL l a r) ∧
      height (balL l a r) ≤ max (height l) (height r) + 1 := by
  have ht_l : ht l = height l := ht_height l havl_l
  have ht_r : ht r = height r := ht_height r havl_r
  by_cases hcond : ht l = ht r + 2
  · cases l with
    | Leaf =>
      simp only [ht] at hcond
      exact absurd hcond (by omega)
    | Node A kv B =>
      obtain ⟨a', n⟩ := kv
      have hA : avl A := havl_l.2.2.1
      have hB : avl B := havl_l.2.2.2
      have hAB : ((height A : ℤ) - (height B : ℤ)).natAbs ≤ 1 := havl_l.1
      have htA : ht A = height A := ht_height A hA
      have htB : ht B = height B := ht_height B hB
      have hNode : height (Tree.Node A (a', n) B) = max (height A) (height B) + 1 := rfl
      by_cases hle : ht B ≤ ht A
      · rw [show balL (Tree.Node A (a', n) B) a r = node A a' (node B a r) from
          by simp [balL, hcond, hle]]
        have hheight : height (node A a' (node B a r)) =
            max (height A) (max (height B) (height r) + 1) + 1 := rfl
        exact ⟨by omega, by omega⟩
      · cases B with
        | Leaf =>
          simp only [ht] at hle
          exact absurd (Nat.zero_le (ht A)) hle
        | Node B1 kv2 B2 =>
          obtain ⟨b, n2⟩ := kv2
          have hB1 : avl B1 := hB.2.2.1
          have hB2 : avl B2 := hB.2.2.2
          have hBalB : ((height B1 : ℤ) - (height B2 : ℤ)).natAbs ≤ 1 := hB.1
          have htB1 : ht B1 = height B1 := ht_height B1 hB1
          have htB2 : ht B2 = height B2 := ht_height B2 hB2
          have hNodeB : height (Tree.Node B1 (b, n2) B2) = max (height B1) (height B2) + 1 := rfl
          rw [show balL (Tree.Node A (a', n) (Tree.Node B1 (b, n2) B2)) a r =
              node (node A a' B1) b (node B2 a r) from by simp [balL, hcond, hle]]
          have hheight : height (node (node A a' B1) b (node B2 a r)) =
              max (max (height A) (height B1) + 1) (max (height B2) (height r) + 1) + 1 := rfl
          exact ⟨by omega, by omega⟩
  · rw [show balL l a r = node l a r from by simp [balL, hcond]]
    have hheight : height (node l a r) = max (height l) (height r) + 1 := rfl
    exact ⟨by omega, by omega⟩

/-- Height of a `balR` result (mirror of `balL_height_mem`). -/
public theorem balR_height_mem (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (havl_l : avl l) (havl_r : avl r)
    (h1 : height l - 1 ≤ height r) (h2 : height r ≤ height l + 2) :
    max (height l) (height r) ≤ height (balR l a r) ∧
      height (balR l a r) ≤ max (height l) (height r) + 1 := by
  have ht_l : ht l = height l := ht_height l havl_l
  have ht_r : ht r = height r := ht_height r havl_r
  by_cases hcond : ht r = ht l + 2
  · cases r with
    | Leaf =>
      simp only [ht] at hcond
      exact absurd hcond (by omega)
    | Node B kv C =>
      obtain ⟨c, n⟩ := kv
      have hB : avl B := havl_r.2.2.1
      have hC : avl C := havl_r.2.2.2
      have hBC : ((height B : ℤ) - (height C : ℤ)).natAbs ≤ 1 := havl_r.1
      have htB : ht B = height B := ht_height B hB
      have htC : ht C = height C := ht_height C hC
      have hNode : height (Tree.Node B (c, n) C) = max (height B) (height C) + 1 := rfl
      by_cases hle : ht B ≤ ht C
      · rw [show balR l a (Tree.Node B (c, n) C) = node (node l a B) c C from
          by simp [balR, hcond, hle]]
        have hheight : height (node (node l a B) c C) =
            max (max (height l) (height B) + 1) (height C) + 1 := rfl
        exact ⟨by omega, by omega⟩
      · cases B with
        | Leaf =>
          simp only [ht] at hle
          exact absurd (Nat.zero_le (ht C)) hle
        | Node B1 kv2 B2 =>
          obtain ⟨b, n2⟩ := kv2
          have hB1 : avl B1 := hB.2.2.1
          have hB2 : avl B2 := hB.2.2.2
          have hBalB : ((height B1 : ℤ) - (height B2 : ℤ)).natAbs ≤ 1 := hB.1
          have htB1 : ht B1 = height B1 := ht_height B1 hB1
          have htB2 : ht B2 = height B2 := ht_height B2 hB2
          have hNodeB : height (Tree.Node B1 (b, n2) B2) = max (height B1) (height B2) + 1 := rfl
          rw [show balR l a (Tree.Node (Tree.Node B1 (b, n2) B2) (c, n) C) =
              node (node l a B1) b (node B2 c C) from by simp [balR, hcond, hle]]
          have hheight : height (node (node l a B1) b (node B2 c C)) =
              max (max (height l) (height B1) + 1) (max (height B2) (height C) + 1) + 1 := rfl
          exact ⟨by omega, by omega⟩
  · rw [show balR l a r = node l a r from by simp [balR, hcond]]
    have hheight : height (node l a r) = max (height l) (height r) + 1 := rfl
    exact ⟨by omega, by omega⟩



/-- `avl` and height of AVL `joinR` (Isabelle `avl_joinR_height`). -/
public theorem avlJoinR_height (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (havl_l : avl l) (havl_r : avl r) (hgt : height l > height r + 1) :
    avl (avlJoinR l a r) ∧
      (height (avlJoinR l a r) = height l ∨ height (avlJoinR l a r) = height l + 1) := by
  induction l generalizing r with
  | Leaf =>
    have h0 : height (Tree.Leaf : Tree α Nat) = 0 := rfl
    exact absurd hgt (by omega)
  | Node l' kv r' ihl ihr =>
    obtain ⟨k, k2⟩ := kv
    have havl_l' : avl l' := havl_l.2.2.1
    have havl_r' : avl r' := havl_l.2.2.2
    have hBal : ((height l' : ℤ) - (height r' : ℤ)).natAbs ≤ 1 := havl_l.1
    have htL : ht (Tree.Node l' (k, k2) r') = height (Tree.Node l' (k, k2) r') :=
      ht_height _ havl_l
    have hNode : height (Tree.Node l' (k, k2) r') = max (height l') (height r') + 1 := rfl
    have htL' : ht l' = height l' := ht_height l' havl_l'
    have htR' : ht r' = height r' := ht_height r' havl_r'
    have htR : ht r = height r := ht_height r havl_r
    by_cases hb : ht r' ≤ ht r + 1
    · -- Descend stops here: `avlJoinR = balR l' k (node r' a r)`.
      have hjoin : avlJoinR (Tree.Node l' (k, k2) r') a r = balR l' k (node r' a r) := by
        simp [avlJoinR, hb]
      rw [hjoin]
      have hnode_avl : avl (node r' a r) := avl_node r' r a havl_r' havl_r (by omega)
      have hnodeH : height (node r' a r) = max (height r') (height r) + 1 := rfl
      have hside1 : height l' - 1 ≤ height (node r' a r) := by omega
      have hside2 : height (node r' a r) ≤ height l' + 2 := by omega
      have havl_bal : avl (balR l' k (node r' a r)) :=
        balR_avl l' k (node r' a r) havl_l' hnode_avl hside1 hside2
      refine ⟨havl_bal, ?_⟩
      by_cases hcond2 : ht (node r' a r) = ht l' + 2
      · by_cases hle2 : ht r' ≤ ht r
        · have hheight : height (balR l' k (node r' a r)) =
              height (Tree.Node l' (k, k2) r') ∨
              height (balR l' k (node r' a r)) =
                height (Tree.Node l' (k, k2) r') + 1 := by
            rw [show balR l' k (node r' a r) = node (node l' k r') a r from by
              have hnode : node r' a r = Tree.Node r' (a, max (ht r') (ht r) + 1) r := rfl
              have hmax : max (ht r') (ht r) = ht r := by omega
              have hcond2'' : ht (Tree.Node r' (a, ht r + 1) r) = ht l' + 2 := by
                rw [← hmax]
                exact hcond2
              rw [hnode]
              simp [balR, hcond2'', hle2]]
            simp only [height, node]
            omega
          exact hheight
        · cases r' with
          | Leaf =>
            simp only [ht] at hle2
            exact absurd (Nat.zero_le (ht r)) hle2
          | Node B1 kv2 B2 =>
            obtain ⟨b, n2⟩ := kv2
            have hB1 : avl B1 := havl_r'.2.2.1
            have hB2 : avl B2 := havl_r'.2.2.2
            have hBalB : ((height B1 : ℤ) - (height B2 : ℤ)).natAbs ≤ 1 := havl_r'.1
            have htB1 : ht B1 = height B1 := ht_height B1 hB1
            have htB2 : ht B2 = height B2 := ht_height B2 hB2
            have hNodeB : height (Tree.Node B1 (b, n2) B2) = max (height B1) (height B2) + 1 := rfl
            have hheight : height (balR l' k (node (Tree.Node B1 (b, n2) B2) a r)) =
                  height (Tree.Node l' (k, k2) (Tree.Node B1 (b, n2) B2)) ∨
                  height (balR l' k (node (Tree.Node B1 (b, n2) B2) a r)) =
                    height (Tree.Node l' (k, k2) (Tree.Node B1 (b, n2) B2)) + 1 := by
              rw [show balR l' k (node (Tree.Node B1 (b, n2) B2) a r) =
                  node (node l' k B1) b (node B2 a r) from by
                have hnode : node (Tree.Node B1 (b, n2) B2) a r =
                    Tree.Node (Tree.Node B1 (b, n2) B2)
                      (a, max (ht (Tree.Node B1 (b, n2) B2)) (ht r) + 1) r := rfl
                have hcond2' : ht (Tree.Node (Tree.Node B1 (b, n2) B2)
                    (a, max (ht (Tree.Node B1 (b, n2) B2)) (ht r) + 1) r) = ht l' + 2 := hcond2
                rw [hnode]
                simp [balR, hcond2', hle2]]
              simp only [height, node]
              omega
            exact hheight
      · have hheight : height (balR l' k (node r' a r)) =
            height (Tree.Node l' (k, k2) r') ∨
            height (balR l' k (node r' a r)) =
              height (Tree.Node l' (k, k2) r') + 1 := by
          rw [show balR l' k (node r' a r) = node l' k (node r' a r) from
            by simp [balR, hcond2]]
          simp only [height, node]
          omega
        exact hheight
    · -- Descend further: `avlJoinR = balR l' k (avlJoinR r' a r)`.
      have hgt' : height r' > height r + 1 := by omega
      obtain ⟨havl_rec, hheight_rec⟩ := ihr r havl_r' havl_r hgt'
      have hjoin : avlJoinR (Tree.Node l' (k, k2) r') a r = balR l' k (avlJoinR r' a r) := by
        simp [avlJoinR, hb]
      rw [hjoin]
      have ht_rec : ht (avlJoinR r' a r) = height (avlJoinR r' a r) :=
        ht_height _ havl_rec
      have hside1 : height l' - 1 ≤ height (avlJoinR r' a r) := by
        rcases hheight_rec with h | h <;> omega
      have hside2 : height (avlJoinR r' a r) ≤ height l' + 2 := by
        rcases hheight_rec with h | h <;> omega
      have havl_bal : avl (balR l' k (avlJoinR r' a r)) :=
        balR_avl l' k (avlJoinR r' a r) havl_l' havl_rec hside1 hside2
      refine ⟨havl_bal, ?_⟩
      by_cases hcond2 : ht (avlJoinR r' a r) = ht l' + 2
      · obtain ⟨hlo, hhi⟩ := balR_height_mem l' k (avlJoinR r' a r) havl_l' havl_rec hside1 hside2
        have hmax : max (height l') (height (avlJoinR r' a r)) =
            height (Tree.Node l' (k, k2) r') := by
          rcases hheight_rec with h | h <;> omega
        omega
      · have hheight : height (balR l' k (avlJoinR r' a r)) =
            height (Tree.Node l' (k, k2) r') ∨
            height (balR l' k (avlJoinR r' a r)) =
              height (Tree.Node l' (k, k2) r') + 1 := by
          rw [show balR l' k (avlJoinR r' a r) = node l' k (avlJoinR r' a r) from
            by simp [balR, hcond2]]
          rcases hheight_rec with h | h <;> simp only [height, node] <;> omega
        exact hheight



/-- `avl` and height of AVL `joinL` (Isabelle `avl_joinL_height`). -/
public theorem avlJoinL_height (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (havl_l : avl l) (havl_r : avl r) (hgt : height r > height l + 1) :
    avl (avlJoinL l a r) ∧
      (height (avlJoinL l a r) = height r ∨ height (avlJoinL l a r) = height r + 1) := by
  induction r generalizing l with
  | Leaf =>
    have h0 : height (Tree.Leaf : Tree α Nat) = 0 := rfl
    exact absurd hgt (by omega)
  | Node l' kv r' ihl ihr =>
    obtain ⟨k, k2⟩ := kv
    have havl_l' : avl l' := havl_r.2.2.1
    have havl_r' : avl r' := havl_r.2.2.2
    have hBal : ((height l' : ℤ) - (height r' : ℤ)).natAbs ≤ 1 := havl_r.1
    have htR : ht (Tree.Node l' (k, k2) r') = height (Tree.Node l' (k, k2) r') :=
      ht_height _ havl_r
    have hNode : height (Tree.Node l' (k, k2) r') = max (height l') (height r') + 1 := rfl
    have htL : ht l = height l := ht_height l havl_l
    have htL' : ht l' = height l' := ht_height l' havl_l'
    have htR' : ht r' = height r' := ht_height r' havl_r'
    by_cases hb : ht l' ≤ ht l + 1
    · -- Descend stops here: `avlJoinL = balL (node l a l') k r'`.
      have hjoin : avlJoinL l a (Tree.Node l' (k, k2) r') = balL (node l a l') k r' := by
        simp [avlJoinL, hb]
      rw [hjoin]
      have hnode_avl : avl (node l a l') := avl_node l l' a havl_l havl_l' (by omega)
      have hnodeH : height (node l a l') = max (height l) (height l') + 1 := rfl
      have hside1 : height r' - 1 ≤ height (node l a l') := by omega
      have hside2 : height (node l a l') ≤ height r' + 2 := by omega
      have havl_bal : avl (balL (node l a l') k r') :=
        balL_avl (node l a l') k r' hnode_avl havl_r' hside1 hside2
      refine ⟨havl_bal, ?_⟩
      by_cases hcond2 : ht (node l a l') = ht r' + 2
      · by_cases hle2 : ht l' ≤ ht l
        · have hheight : height (balL (node l a l') k r') =
              height (Tree.Node l' (k, k2) r') ∨
              height (balL (node l a l') k r') =
                height (Tree.Node l' (k, k2) r') + 1 := by
            rw [show balL (node l a l') k r' = node l a (node l' k r') from by
              have hnode : node l a l' = Tree.Node l (a, max (ht l) (ht l') + 1) l' := rfl
              have hmax : max (ht l) (ht l') = ht l := by omega
              have hcond2'' : ht (Tree.Node l (a, ht l + 1) l') = ht r' + 2 := by
                rw [← hmax]
                exact hcond2
              rw [hnode]
              simp [balL, hcond2'', hle2]]
            simp only [height, node]
            omega
          exact hheight
        · cases l' with
          | Leaf =>
            simp only [ht] at hle2
            exact absurd (Nat.zero_le (ht l)) hle2
          | Node B1 kv2 B2 =>
            obtain ⟨b, n2⟩ := kv2
            have hB1 : avl B1 := havl_l'.2.2.1
            have hB2 : avl B2 := havl_l'.2.2.2
            have hBalB : ((height B1 : ℤ) - (height B2 : ℤ)).natAbs ≤ 1 := havl_l'.1
            have htB1 : ht B1 = height B1 := ht_height B1 hB1
            have htB2 : ht B2 = height B2 := ht_height B2 hB2
            have hNodeB : height (Tree.Node B1 (b, n2) B2) = max (height B1) (height B2) + 1 := rfl
            have ht_node : ht (node l a (Tree.Node B1 (b, n2) B2)) =
                height (node l a (Tree.Node B1 (b, n2) B2)) := ht_height _ hnode_avl
            have hheight : height (balL (node l a (Tree.Node B1 (b, n2) B2)) k r') =
                  height (Tree.Node (Tree.Node B1 (b, n2) B2) (k, k2) r') ∨
                  height (balL (node l a (Tree.Node B1 (b, n2) B2)) k r') =
                    height (Tree.Node (Tree.Node B1 (b, n2) B2) (k, k2) r') + 1 := by
              rw [show balL (node l a (Tree.Node B1 (b, n2) B2)) k r' =
                  node (node l a B1) b (node B2 k r') from by
                have hnode : node l a (Tree.Node B1 (b, n2) B2) =
                    Tree.Node l (a, max (ht l) (ht (Tree.Node B1 (b, n2) B2)) + 1)
                      (Tree.Node B1 (b, n2) B2) := rfl
                have hcond2' : ht (Tree.Node l
                    (a, max (ht l) (ht (Tree.Node B1 (b, n2) B2)) + 1)
                    (Tree.Node B1 (b, n2) B2)) = ht r' + 2 := hcond2
                rw [hnode]
                simp [balL, hcond2', hle2]]
              simp only [height, node]
              omega
            exact hheight
      · have hheight : height (balL (node l a l') k r') =
            height (Tree.Node l' (k, k2) r') ∨
            height (balL (node l a l') k r') =
              height (Tree.Node l' (k, k2) r') + 1 := by
          rw [show balL (node l a l') k r' = node (node l a l') k r' from
            by simp [balL, hcond2]]
          simp only [height, node]
          omega
        exact hheight
    · -- Descend further: `avlJoinL = balL (avlJoinL l a l') k r'`.
      have hgt' : height l' > height l + 1 := by omega
      obtain ⟨havl_rec, hheight_rec⟩ := ihl l havl_l havl_l' hgt'
      have hjoin : avlJoinL l a (Tree.Node l' (k, k2) r') = balL (avlJoinL l a l') k r' := by
        simp [avlJoinL, hb]
      rw [hjoin]
      have ht_rec : ht (avlJoinL l a l') = height (avlJoinL l a l') := ht_height _ havl_rec
      have hside1 : height r' - 1 ≤ height (avlJoinL l a l') := by
        rcases hheight_rec with h | h <;> omega
      have hside2 : height (avlJoinL l a l') ≤ height r' + 2 := by
        rcases hheight_rec with h | h <;> omega
      have havl_bal : avl (balL (avlJoinL l a l') k r') :=
        balL_avl (avlJoinL l a l') k r' havl_rec havl_r' hside1 hside2
      refine ⟨havl_bal, ?_⟩
      by_cases hcond2 : ht (avlJoinL l a l') = ht r' + 2
      · obtain ⟨hlo, hhi⟩ := balL_height_mem (avlJoinL l a l') k r' havl_rec havl_r' hside1 hside2
        have hmax : max (height (avlJoinL l a l')) (height r') =
            height (Tree.Node l' (k, k2) r') := by
          rcases hheight_rec with h | h <;> omega
        omega
      · have hheight : height (balL (avlJoinL l a l') k r') =
            height (Tree.Node l' (k, k2) r') ∨
            height (balL (avlJoinL l a l') k r') =
              height (Tree.Node l' (k, k2) r') + 1 := by
          rw [show balL (avlJoinL l a l') k r' = node (avlJoinL l a l') k r' from
            by simp [balL, hcond2]]
          rcases hheight_rec with h | h <;> simp only [height, node] <;> omega
        exact hheight



/-- AVL `join` preserves `avl` (Isabelle `inv_join`). -/
public theorem inv_avlJoin (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (havl_l : avl l) (havl_r : avl r) : avl (avlJoin l a r) := by
  have htL : ht l = height l := ht_height l havl_l
  have htR : ht r = height r := ht_height r havl_r
  by_cases h1 : ht l > ht r + 1
  · have hgt : height l > height r + 1 := by omega
    have h := (avlJoinR_height l a r havl_l havl_r hgt).1
    have hjoin : avlJoin l a r = avlJoinR l a r := by simp [avlJoin, h1]
    rwa [hjoin]
  · by_cases h2 : ht r > ht l + 1
    · have hgt : height r > height l + 1 := by omega
      have h := (avlJoinL_height l a r havl_l havl_r hgt).1
      have hjoin : avlJoin l a r = avlJoinL l a r := by simp [avlJoin, h1, h2]
      rwa [hjoin]
    · have hjoin : avlJoin l a r = node l a r := by simp [avlJoin, h1, h2]
      rw [hjoin]
      exact avl_node l r a havl_l havl_r (by omega)

/-- Height of AVL `join` (Isabelle `join_height`). -/
public theorem join_height (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (havl_l : avl l) (havl_r : avl r) :
    height (avlJoin l a r) = max (height l) (height r) ∨
      height (avlJoin l a r) = max (height l) (height r) + 1 := by
  have htL : ht l = height l := ht_height l havl_l
  have htR : ht r = height r := ht_height r havl_r
  by_cases h1 : ht l > ht r + 1
  · have hgt : height l > height r + 1 := by omega
    have h := (avlJoinR_height l a r havl_l havl_r hgt).2
    have hjoin : avlJoin l a r = avlJoinR l a r := by simp [avlJoin, h1]
    rw [hjoin]
    rcases h with h | h <;> omega
  · by_cases h2 : ht r > ht l + 1
    · have hgt : height r > height l + 1 := by omega
      have h := (avlJoinL_height l a r havl_l havl_r hgt).2
      have hjoin : avlJoin l a r = avlJoinL l a r := by simp [avlJoin, h1, h2]
      rw [hjoin]
      rcases h with h | h <;> omega
    · have hjoin : avlJoin l a r = node l a r := by simp [avlJoin, h1, h2]
      rw [hjoin]
      exact Or.inr rfl

/-- The AVL instantiation of the generic `Set2_Join` framework
(Isabelle `interpretation tree_ht: Set2_Join where join = join and inv = avl`). -/
public def avlJoinData : JoinData α Nat where
  join := avlJoin
  inv := avl
  inv_leaf := trivial
  set_join := fun l x r => set_avlJoin l x r
  bst_join := fun l x b r h => bst_avlJoin l x r b h
  inv_join := fun l x r hl hr => inv_avlJoin l x r hl hr
  inv_node := fun l kv r h => ⟨h.2.2.1, h.2.2.2⟩

/-- AVL `union` via the generic framework (Isabelle `union` under `tree_ht`). -/
public def avlUnion (t₁ t₂ : Tree α Nat) : Tree α Nat := union avlJoinData t₁ t₂

public theorem avlUnion_set (t₁ t₂ : Tree α Nat) (hbst₂ : bst t₂) :
    set_tree (avlUnion t₁ t₂) = set_tree t₁ ∪ set_tree t₂ :=
  union_set (J := avlJoinData) t₁ t₂ hbst₂

public theorem avlUnion_bst (t₁ t₂ : Tree α Nat) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (avlUnion t₁ t₂) := union_bst (J := avlJoinData) t₁ t₂ hbst₁ hbst₂

public theorem avlUnion_inv (t₁ t₂ : Tree α Nat) (hinv₁ : avl t₁) (hinv₂ : avl t₂) :
    avl (avlUnion t₁ t₂) := union_inv (J := avlJoinData) t₁ t₂ hinv₁ hinv₂

/-- AVL `inter` via the generic framework. -/
public def avlInter (t₁ t₂ : Tree α Nat) : Tree α Nat := inter avlJoinData t₁ t₂

public theorem avlInter_set (t₁ t₂ : Tree α Nat) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    set_tree (avlInter t₁ t₂) = set_tree t₁ ∩ set_tree t₂ :=
  inter_set (J := avlJoinData) t₁ t₂ hbst₁ hbst₂

public theorem avlInter_bst (t₁ t₂ : Tree α Nat) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (avlInter t₁ t₂) := inter_bst (J := avlJoinData) t₁ t₂ hbst₁ hbst₂

public theorem avlInter_inv (t₁ t₂ : Tree α Nat) (hinv₁ : avl t₁) (hinv₂ : avl t₂) :
    avl (avlInter t₁ t₂) := inter_inv (J := avlJoinData) t₁ t₂ hinv₁ hinv₂

/-- AVL `diff` via the generic framework. -/
public def avlDiff (t₁ t₂ : Tree α Nat) : Tree α Nat := diff avlJoinData t₁ t₂

public theorem avlDiff_set (t₁ t₂ : Tree α Nat) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    set_tree (avlDiff t₁ t₂) = set_tree t₁ \ set_tree t₂ :=
  diff_set (J := avlJoinData) t₁ t₂ hbst₁ hbst₂

public theorem avlDiff_bst (t₁ t₂ : Tree α Nat) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (avlDiff t₁ t₂) := diff_bst (J := avlJoinData) t₁ t₂ hbst₁ hbst₂

public theorem avlDiff_inv (t₁ t₂ : Tree α Nat) (hinv₁ : avl t₁) (hinv₂ : avl t₂) :
    avl (avlDiff t₁ t₂) := diff_inv (J := avlJoinData) t₁ t₂ hinv₁ hinv₂

/-- AVL `insert` via the generic framework. -/
public def avlInsert (x : α) (t : Tree α Nat) : Tree α Nat := insert avlJoinData x t

public theorem avlInsert_set (x : α) (t : Tree α Nat) (hbst : bst t) :
    set_tree (avlInsert x t) = set_tree t ∪ {x} :=
  insert_set (J := avlJoinData) x t hbst

public theorem avlInsert_bst (x : α) (t : Tree α Nat) (hbst : bst t) :
    bst (avlInsert x t) := insert_bst (J := avlJoinData) x t hbst

public theorem avlInsert_inv (x : α) (t : Tree α Nat) (hinv : avl t) :
    avl (avlInsert x t) := insert_inv (J := avlJoinData) x t hinv

/-- AVL `delete` via the generic framework. -/
public def avlDelete (x : α) (t : Tree α Nat) : Tree α Nat := delete avlJoinData x t

public theorem avlDelete_set (x : α) (t : Tree α Nat) (hbst : bst t) :
    set_tree (avlDelete x t) = set_tree t \ {x} :=
  delete_set (J := avlJoinData) x t hbst

public theorem avlDelete_bst (x : α) (t : Tree α Nat) (hbst : bst t) :
    bst (avlDelete x t) := delete_bst (J := avlJoinData) x t hbst

public theorem avlDelete_inv (x : α) (t : Tree α Nat) (hinv : avl t) :
    avl (avlDelete x t) := delete_inv (J := avlJoinData) x t hinv

end JoinableBinarySearchTree

end Cslib.Algorithms.Lean
