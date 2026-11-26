/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`src/HOL/Data_Structures/Set2_Join_RBT.thy`, `src/HOL/Data_Structures/RBT.thy` and
`src/HOL/Data_Structures/RBT_Set.thy` (Isabelle/HOL, `HOL-Data_Structures`):
Copyright (c) 1986-2026, University of Cambridge, Technische Universitaet Muenchen,
and contributors. All rights reserved.
Licensed under the 3-clause BSD license in Isabelle's `COPYRIGHT` file
(https://github.com/isabelle-prover/mirror-isabelle/blob/master/COPYRIGHT).
Authors: Tobias Nipkow

`thys/Joinable_BST_Work_Bounds/StronglyJoinableRBT.thy` (Archive of Formal Proofs, entry
`Joinable_BST_Work_Bounds`, https://www.isa-afp.org/entries/Joinable_BST_Work_Bounds.html):
Copyright (c) 2004, Gerwin Klein, Tobias Nipkow, Lawrence C. Paulson
Copyright (c) 2004, contributing authors (see author notice in individual files)
All rights reserved.
Licensed under the BSD License of the Archive of Formal Proofs (https://isa-afp.org/LICENSE).
Authors: Marco Haucke
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.Basic
public import Mathlib.Tactic

/-!
# Joinable binary search trees: red–black join

The red–black `join` of Chapter 10, §10.3 (Figure 10.4): colors, black
height, the color invariants `invc` / `invc2`, the height invariant
`invh`, the rebalancing helpers `baliL` / `baliR` (book Chapter 8),
`paint`, and the spine-descent `joinL` / `joinR` / `rbtJoin`, with
`set` / `bst` / `inv` correctness, the Figure 10.2 `JoinData` instance
`rbtJoinData` (invariant `invc ∧ invh`), and the `rbtUnion` / `rbtInter` /
`rbtDiff` / `rbtInsert` / `rbtDelete` corollaries of the generic
framework, plus `inorder` and node-count (`tsize`) lemmas. Both the
book's combined §10.3.1 proposition and the finer Isabelle splits are
proved.

## Provenance

`Set2_Join_RBT.thy` in Isabelle/HOL's bundled `HOL-Data_Structures`
library (the `Set2_Join` interpretation for red–black trees: `joinL` /
`joinR` / `rbtJoin` and most lemmas about them), built on that library's
red–black trees (book Chapter 8): `Color`, `RNode` / `BNode` (Isabelle
`R` / `B`), `baliL` / `baliR` and `paint` from `RBT.thy`, and `col`
(Isabelle `color`), `bheight`, `invc`, `invc2`, `invh` and the invariant
and `inorder` lemmas for `baliL` / `baliR` from `RBT_Set.thy`. In the
docstrings below, names cited as Isabelle lemmas are from these three
theories. This is the book's Figure 10.4 join, whose result always has a
black root (`paint Black` after a spine descent, a black node for equal
black heights), not the stored-black-height variant of AFP
`StronglyJoinableRBT.thy` (see `StronglyJoinableRBT`). That AFP theory
supplies the defining equations of `invc2` and the statements, restated
here for these trees, of `col_joinL` / `col_joinR` and of the node-count
lemmas `tsize_baliL` / `tsize_baliR` / `tsize_joinL` / `tsize_joinR` /
`tsize_rbtJoin`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace JoinableBinarySearchTree

variable {α : Type u} [LinearOrder α]

/-! ### §10.3 — Joining red–black trees

Red–black trees are `Tree α Color` (`β = Color`). The `join` here is
the book's Fig. 10.4 version as in `Set2_Join_RBT.thy` (Isabelle/HOL,
`HOL-Data_Structures`): it recomputes `bheight` on every step. The invariant used for Fig. 10.2
is `inv t = invc t ∧ invh t`; `rbt` itself does *not* satisfy (10.4),
which is why the weaker invariant is used (book §10.3.1). -/

/-- Colors of red–black tree nodes. -/
public inductive Color where
  | Red : Color
  | Black : Color
deriving DecidableEq, Repr

/-- Color of the root (`Black` for the empty tree). -/
public def col : Tree α Color → Color
  | .Leaf => .Black
  | .Node _ (_, c) _ => c

/-- Black height: number of black nodes on any root-to-leaf path. -/
public def bheight : Tree α Color → ℕ
  | .Leaf => 0
  | .Node l (_, c) _ => if c = .Black then bheight l + 1 else bheight l

/-- Color invariant: red nodes have black children. -/
public def invc : Tree α Color → Prop
  | .Leaf => True
  | .Node l (_, c) r =>
      (c = .Red → col l = .Black ∧ col r = .Black) ∧ invc l ∧ invc r

/-- Weaker color invariant: both children satisfy `invc` (a red root
with a red child is allowed). -/
public def invc2 : Tree α Color → Prop
  | .Leaf => True
  | .Node l _ r => invc l ∧ invc r

/-- Height invariant: sibling subtrees have equal black height. -/
public def invh : Tree α Color → Prop
  | .Leaf => True
  | .Node l _ r => bheight l = bheight r ∧ invh l ∧ invh r

/-- Smart constructors `R` (red node) and `B` (black node). -/
public def RNode (l : Tree α Color) (a : α) (r : Tree α Color) : Tree α Color :=
  Tree.Node l (a, .Red) r

public def BNode (l : Tree α Color) (a : α) (r : Tree α Color) : Tree α Color :=
  Tree.Node l (a, .Black) r

/-- `baliL`: rebalance after inserting on the left (book Ch. 8). -/
public def baliL : Tree α Color → α → Tree α Color → Tree α Color
  | .Node (.Node t1 (a, .Red) t2) (b, .Red) t3, c, t4 =>
      RNode (BNode t1 a t2) b (BNode t3 c t4)
  | .Node t1 (a, .Red) (.Node t2 (b, .Red) t3), c, t4 =>
      RNode (BNode t1 a t2) b (BNode t3 c t4)
  | t1, a, t2 => BNode t1 a t2

/-- `baliR`: mirror of `baliL`. -/
public def baliR : Tree α Color → α → Tree α Color → Tree α Color
  | t1, a, .Node t2 (b, .Red) (.Node t3 (c, .Red) t4) =>
      RNode (BNode t1 a t2) b (BNode t3 c t4)
  | t1, a, .Node (.Node t2 (b, .Red) t3) (c, .Red) t4 =>
      RNode (BNode t1 a t2) b (BNode t3 c t4)
  | t1, a, t2 => BNode t1 a t2

/-- Regression test: a tree matching *both* `baliL` patterns takes the
first one, as in Isabelle's `fun` equation order. -/
public example : baliL
    (Tree.Node (Tree.Node Tree.Leaf (1, Color.Red) Tree.Leaf) (2, Color.Red)
      (Tree.Node Tree.Leaf (3, Color.Red) Tree.Leaf)) 4 Tree.Leaf
    = RNode (BNode Tree.Leaf 1 Tree.Leaf) 2
        (BNode (Tree.Node Tree.Leaf (3, Color.Red) Tree.Leaf) 4 Tree.Leaf) := rfl

/-- Regression test: a tree matching *both* `baliR` patterns takes the
first one, as in Isabelle's `fun` equation order. -/
public example : baliR Tree.Leaf 0
    (Tree.Node (Tree.Node Tree.Leaf (1, Color.Red) Tree.Leaf) (2, Color.Red)
      (Tree.Node Tree.Leaf (3, Color.Red) Tree.Leaf))
    = RNode (BNode Tree.Leaf 0 (Tree.Node Tree.Leaf (1, Color.Red) Tree.Leaf)) 2
        (BNode Tree.Leaf 3 Tree.Leaf) := rfl

/-- Repaint the root with color `c`, keeping subtrees. -/
public def paint (c : Color) : Tree α Color → Tree α Color
  | .Leaf => .Leaf
  | .Node l (a, _) r => .Node l (a, c) r

/-- `joinL` (book Fig. 10.4): descend the left spine of `r`. -/
public def joinL : Tree α Color → α → Tree α Color → Tree α Color
  | l, x, r =>
    if bheight l ≥ bheight r then RNode l x r
    else match r with
      | .Leaf => RNode l x .Leaf
      | .Node l' (x', c) r' =>
        if c = .Black then baliL (joinL l x l') x' r'
        else RNode (joinL l x l') x' r'
termination_by l x r => r

/-- `joinR` (book Fig. 10.4): mirror of `joinL`. -/
public def joinR : Tree α Color → α → Tree α Color → Tree α Color
  | l, x, r =>
    if bheight l ≤ bheight r then RNode l x r
    else match l with
      | .Leaf => RNode .Leaf x r
      | .Node l' (x', c) r' =>
        if c = .Black then baliR l' x' (joinR r' x r)
        else RNode l' x' (joinR r' x r)
termination_by l x r => l

/-- `join` for red–black trees (book Fig. 10.4). -/
public def rbtJoin (l : Tree α Color) (x : α) (r : Tree α Color) : Tree α Color :=
  if bheight l > bheight r then paint .Black (joinR l x r)
  else if bheight l < bheight r then paint .Black (joinL l x r)
  else BNode l x r



-- Helpers for `RNode` / `BNode`.
public theorem set_RNode (l r : Tree α Color) (a : α) :
    set_tree (RNode l a r) = set_tree l ∪ {a} ∪ set_tree r := rfl
public theorem set_BNode (l r : Tree α Color) (a : α) :
    set_tree (BNode l a r) = set_tree l ∪ {a} ∪ set_tree r := rfl
public theorem col_RNode (l r : Tree α Color) (a : α) : col (RNode l a r) = .Red := rfl
public theorem col_BNode (l r : Tree α Color) (a : α) : col (BNode l a r) = .Black := rfl
public theorem bheight_RNode (l r : Tree α Color) (a : α) : bheight (RNode l a r) = bheight l := rfl
public theorem bheight_BNode (l r : Tree α Color) (a : α) : bheight (BNode l a r) = bheight l + 1 := rfl

public theorem baliL_set (l : Tree α Color) (a : α) (r : Tree α Color) :
    set_tree (baliL l a r) = set_tree l ∪ {a} ∪ set_tree r := by
  cases l with
  | Leaf => simp [baliL, BNode]
  | Node ll kv rl =>
    obtain ⟨a', c⟩ := kv
    cases ll with
    | Leaf =>
      cases c with
      | Red =>
        cases rl with
        | Leaf => simp [baliL, BNode]
        | Node t2 kv2 t3 =>
          obtain ⟨b, c2⟩ := kv2
          cases c2 with
          | Red => simp only [baliL, RNode, BNode, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
          | Black => simp [baliL, BNode]
      | Black => simp [baliL, BNode]
    | Node t1 kv1 t2 =>
      obtain ⟨a1, c1⟩ := kv1
      cases c with
      | Red =>
        cases c1 with
        | Red => simp only [baliL, RNode, BNode, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
        | Black =>
          cases rl with
          | Leaf => simp [baliL, BNode]
          | Node t2 kv2 t3 =>
            obtain ⟨b, c2⟩ := kv2
            cases c2 with
            | Red => simp only [baliL, RNode, BNode, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
            | Black => simp [baliL, BNode]
      | Black => simp [baliL, BNode]

public theorem baliR_set (l : Tree α Color) (a : α) (r : Tree α Color) :
    set_tree (baliR l a r) = set_tree l ∪ {a} ∪ set_tree r := by
  cases r with
  | Leaf => simp [baliR, BNode]
  | Node rl kv rr =>
    obtain ⟨b, c⟩ := kv
    cases rr with
    | Leaf =>
      cases c with
      | Red =>
        cases rl with
        | Leaf => simp [baliR, BNode]
        | Node t2 kv2 t3 =>
          obtain ⟨b2, c2⟩ := kv2
          cases c2 with
          | Red => simp only [baliR, RNode, BNode, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
          | Black => simp [baliR, BNode]
      | Black => simp [baliR, BNode]
    | Node t3 kv3 t4 =>
      obtain ⟨c3, c4⟩ := kv3
      cases c with
      | Red =>
        cases c4 with
        | Red => simp only [baliR, RNode, BNode, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
        | Black =>
          cases rl with
          | Leaf => simp [baliR, BNode]
          | Node t2 kv2 t3' =>
            obtain ⟨b2, c2⟩ := kv2
            cases c2 with
            | Red => simp only [baliR, RNode, BNode, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
            | Black => simp [baliR, BNode]
      | Black => simp [baliR, BNode]



/-- `bst` of a node from the `bst` of its children and the bound conditions. -/
public theorem bst_N (l r : Tree α Color) (a : α) (c : Color)
    (h1 : bst l) (h2 : bst r) (hl : ∀ x ∈ set_tree l, x < a)
    (hr : ∀ y ∈ set_tree r, a < y) : bst (Tree.Node l (a, c) r) :=
  ⟨h1, h2, hl, hr⟩

public theorem baliL_bst (l : Tree α Color) (a : α) (r : Tree α Color)
    (hbl : bst l) (hbr : bst r) (hl : ∀ x ∈ set_tree l, x < a)
    (hr : ∀ y ∈ set_tree r, a < y) : bst (baliL l a r) := by
  fun_cases baliL l a r <;> simp_all [bst, RNode, BNode, set_tree] <;> aesop (add unsafe lt_trans)



public theorem baliR_bst (l : Tree α Color) (a : α) (r : Tree α Color)
    (hbl : bst l) (hbr : bst r) (hl : ∀ x ∈ set_tree l, x < a)
    (hr : ∀ y ∈ set_tree r, a < y) : bst (baliR l a r) := by
  fun_cases baliR l a r <;> simp_all [bst, RNode, BNode, set_tree] <;> aesop (add unsafe lt_trans)

/-- `baliL` invariant property (book Ch. 8, used in §10.3.1). -/
public theorem baliL_inv (l : Tree α Color) (a : α) (r : Tree α Color)
    (hinvh_l : invh l) (hinvh_r : invh r) (hinvc2 : invc2 l) (hinvc : invc r)
    (hbh : bheight l = bheight r) :
    invc (baliL l a r) ∧ invh (baliL l a r) ∧ bheight (baliL l a r) = bheight l + 1 := by
  cases l with
  | Leaf =>
    have heq : baliL (Tree.Leaf : Tree α Color) a r = BNode Tree.Leaf a r := rfl
    rw [heq]
    simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
  | Node ll kv rl =>
    obtain ⟨b, c⟩ := kv
    cases ll with
    | Leaf =>
      cases c with
      | Red =>
        cases rl with
        | Leaf =>
          have heq : baliL (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) a r = BNode (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) a r := rfl
          rw [heq]
          simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliL (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Red) t3)) a r =
                RNode (BNode Tree.Leaf b t2) b' (BNode t3 a r) := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliL (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Black) t3)) a r = BNode (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Black) t3)) a r := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
      | Black =>
        have heq : baliL (Tree.Node Tree.Leaf (b, .Black) rl) a r = BNode (Tree.Node Tree.Leaf (b, .Black) rl) a r := rfl
        rw [heq]
        simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
    | Node t1 kv1 t2 =>
      obtain ⟨a1, c1⟩ := kv1
      cases c with
      | Red =>
        cases c1 with
        | Red =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Red) rl) a r =
              RNode (BNode t1 a1 t2) b (BNode rl a r) := rfl
          rw [heq]
          simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
        | Black =>
          cases rl with
          | Leaf =>
            have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) Tree.Leaf) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) Tree.Leaf) a r := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Red) t3')) a r =
                  RNode (BNode (Tree.Node t1 (a1, .Black) t2) b t2') b' (BNode t3' a r) := rfl
              rw [heq]
              simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Black) t3')) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Black) t3')) a r := rfl
              rw [heq]
              simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
      | Black =>
        cases c1 with
        | Red =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Black) rl) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Black) rl) a r := rfl
          rw [heq]
          simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
        | Black =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Black) rl) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Black) rl) a r := rfl
          rw [heq]
          simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega




/-- `invc` for `baliL` (Isabelle `invc_baliL`). -/
public theorem invc_baliL (l : Tree α Color) (a : α) (r : Tree α Color) (hinvc2 : invc2 l) (hinvc : invc r) :
    invc (baliL l a r) := by
  cases l with
  | Leaf =>
    have heq : baliL (Tree.Leaf : Tree α Color) a r = BNode Tree.Leaf a r := rfl
    rw [heq]
    simp_all [invc, invc2, col, RNode, BNode] <;> try omega
  | Node ll kv rl =>
    obtain ⟨b, c⟩ := kv
    cases ll with
    | Leaf =>
      cases c with
      | Red =>
        cases rl with
        | Leaf =>
          have heq : baliL (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) a r = BNode (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) a r := rfl
          rw [heq]
          simp_all [invc, invc2, col, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliL (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Red) t3)) a r =
                RNode (BNode Tree.Leaf b t2) b' (BNode t3 a r) := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliL (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Black) t3)) a r = BNode (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Black) t3)) a r := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
      | Black =>
        have heq : baliL (Tree.Node Tree.Leaf (b, .Black) rl) a r = BNode (Tree.Node Tree.Leaf (b, .Black) rl) a r := rfl
        rw [heq]
        simp_all [invc, invc2, col, RNode, BNode] <;> try omega
    | Node t1 kv1 t2 =>
      obtain ⟨a1, c1⟩ := kv1
      cases c with
      | Red =>
        cases c1 with
        | Red =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Red) rl) a r =
              RNode (BNode t1 a1 t2) b (BNode rl a r) := rfl
          rw [heq]
          simp_all [invc, invc2, col, RNode, BNode] <;> try omega
        | Black =>
          cases rl with
          | Leaf =>
            have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) Tree.Leaf) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) Tree.Leaf) a r := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Red) t3')) a r =
                  RNode (BNode (Tree.Node t1 (a1, .Black) t2) b t2') b' (BNode t3' a r) := rfl
              rw [heq]
              simp_all [invc, invc2, col, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Black) t3')) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Black) t3')) a r := rfl
              rw [heq]
              simp_all [invc, invc2, col, RNode, BNode] <;> try omega
      | Black =>
        cases c1 with
        | Red =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Black) rl) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Black) rl) a r := rfl
          rw [heq]
          simp_all [invc, invc2, col, RNode, BNode] <;> try omega
        | Black =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Black) rl) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Black) rl) a r := rfl
          rw [heq]
          simp_all [invc, invc2, col, RNode, BNode] <;> try omega




/-- `invh` for `baliL` (Isabelle `invh_baliL`). -/
public theorem invh_baliL (l : Tree α Color) (a : α) (r : Tree α Color) (hinvh_l : invh l) (hinvh_r : invh r) (hbh : bheight l = bheight r) :
    invh (baliL l a r) := by
  cases l with
  | Leaf =>
    have heq : baliL (Tree.Leaf : Tree α Color) a r = BNode Tree.Leaf a r := rfl
    rw [heq]
    simp_all [invh, bheight, RNode, BNode] <;> try omega
  | Node ll kv rl =>
    obtain ⟨b, c⟩ := kv
    cases ll with
    | Leaf =>
      cases c with
      | Red =>
        cases rl with
        | Leaf =>
          have heq : baliL (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) a r = BNode (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) a r := rfl
          rw [heq]
          simp_all [invh, bheight, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliL (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Red) t3)) a r =
                RNode (BNode Tree.Leaf b t2) b' (BNode t3 a r) := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliL (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Black) t3)) a r = BNode (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Black) t3)) a r := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
      | Black =>
        have heq : baliL (Tree.Node Tree.Leaf (b, .Black) rl) a r = BNode (Tree.Node Tree.Leaf (b, .Black) rl) a r := rfl
        rw [heq]
        simp_all [invh, bheight, RNode, BNode] <;> try omega
    | Node t1 kv1 t2 =>
      obtain ⟨a1, c1⟩ := kv1
      cases c with
      | Red =>
        cases c1 with
        | Red =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Red) rl) a r =
              RNode (BNode t1 a1 t2) b (BNode rl a r) := rfl
          rw [heq]
          simp_all [invh, bheight, RNode, BNode] <;> try omega
        | Black =>
          cases rl with
          | Leaf =>
            have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) Tree.Leaf) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) Tree.Leaf) a r := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Red) t3')) a r =
                  RNode (BNode (Tree.Node t1 (a1, .Black) t2) b t2') b' (BNode t3' a r) := rfl
              rw [heq]
              simp_all [invh, bheight, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Black) t3')) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Black) t3')) a r := rfl
              rw [heq]
              simp_all [invh, bheight, RNode, BNode] <;> try omega
      | Black =>
        cases c1 with
        | Red =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Black) rl) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Black) rl) a r := rfl
          rw [heq]
          simp_all [invh, bheight, RNode, BNode] <;> try omega
        | Black =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Black) rl) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Black) rl) a r := rfl
          rw [heq]
          simp_all [invh, bheight, RNode, BNode] <;> try omega




/-- Black height of `baliL` (Isabelle `bheight_baliL`). -/
public theorem bheight_baliL (l : Tree α Color) (a : α) (r : Tree α Color) (hbh : bheight l = bheight r) :
    bheight (baliL l a r) = bheight l + 1 := by
  cases l with
  | Leaf =>
    have heq : baliL (Tree.Leaf : Tree α Color) a r = BNode Tree.Leaf a r := rfl
    rw [heq]
    simp_all [bheight, RNode, BNode] <;> try omega
  | Node ll kv rl =>
    obtain ⟨b, c⟩ := kv
    cases ll with
    | Leaf =>
      cases c with
      | Red =>
        cases rl with
        | Leaf =>
          have heq : baliL (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) a r = BNode (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) a r := rfl
          rw [heq]
          simp_all [bheight, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliL (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Red) t3)) a r =
                RNode (BNode Tree.Leaf b t2) b' (BNode t3 a r) := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliL (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Black) t3)) a r = BNode (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t2 (b', .Black) t3)) a r := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
      | Black =>
        have heq : baliL (Tree.Node Tree.Leaf (b, .Black) rl) a r = BNode (Tree.Node Tree.Leaf (b, .Black) rl) a r := rfl
        rw [heq]
        simp_all [bheight, RNode, BNode] <;> try omega
    | Node t1 kv1 t2 =>
      obtain ⟨a1, c1⟩ := kv1
      cases c with
      | Red =>
        cases c1 with
        | Red =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Red) rl) a r =
              RNode (BNode t1 a1 t2) b (BNode rl a r) := rfl
          rw [heq]
          simp_all [bheight, RNode, BNode] <;> try omega
        | Black =>
          cases rl with
          | Leaf =>
            have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) Tree.Leaf) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) Tree.Leaf) a r := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Red) t3')) a r =
                  RNode (BNode (Tree.Node t1 (a1, .Black) t2) b t2') b' (BNode t3' a r) := rfl
              rw [heq]
              simp_all [bheight, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Black) t3')) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Red) (Tree.Node t2' (b', .Black) t3')) a r := rfl
              rw [heq]
              simp_all [bheight, RNode, BNode] <;> try omega
      | Black =>
        cases c1 with
        | Red =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Black) rl) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Red) t2) (b, .Black) rl) a r := rfl
          rw [heq]
          simp_all [bheight, RNode, BNode] <;> try omega
        | Black =>
          have heq : baliL (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Black) rl) a r = BNode (Tree.Node (Tree.Node t1 (a1, .Black) t2) (b, .Black) rl) a r := rfl
          rw [heq]
          simp_all [bheight, RNode, BNode] <;> try omega




/-- `baliR` invariant property (mirror of `baliL_inv`). -/
public theorem baliR_inv (l : Tree α Color) (a : α) (r : Tree α Color)
    (hinvh_l : invh l) (hinvh_r : invh r) (hinvc : invc l) (hinvc2 : invc2 r)
    (hbh : bheight l = bheight r) :
    invc (baliR l a r) ∧ invh (baliR l a r) ∧ bheight (baliR l a r) = bheight l + 1 := by
  cases r with
  | Leaf =>
    have heq : baliR l a (Tree.Leaf : Tree α Color) = BNode l a Tree.Leaf := rfl
    rw [heq]
    simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
  | Node lr kv rr =>
    obtain ⟨b, c⟩ := kv
    cases rr with
    | Leaf =>
      cases c with
      | Red =>
        cases lr with
        | Leaf =>
          have heq : baliR l a (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) = BNode l a (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) := rfl
          rw [heq]
          simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Red) Tree.Leaf) =
                RNode (BNode l a t2) b' (BNode t3 b Tree.Leaf) := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Red) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Red) Tree.Leaf) := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
      | Black =>
        cases lr with
        | Leaf =>
          have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) Tree.Leaf) = BNode l a (Tree.Node Tree.Leaf (b, .Black) Tree.Leaf) := rfl
          rw [heq]
          simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Black) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Black) Tree.Leaf) := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Black) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Black) Tree.Leaf) := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
    | Node t3 kv1 t4 =>
      obtain ⟨d, dc⟩ := kv1
      cases c with
      | Red =>
        cases dc with
        | Red =>
          have heq : baliR l a (Tree.Node lr (b, .Red) (Tree.Node t3 (d, .Red) t4)) =
              RNode (BNode l a lr) b (BNode t3 d t4) := rfl
          rw [heq]
          simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
        | Black =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t3 (d, .Black) t4)) := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) =
                  RNode (BNode l a t2') b' (BNode t3' b (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
      | Black =>
        cases dc with
        | Red =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
        | Black =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
            rw [heq]
            simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, invh, bheight, col, RNode, BNode] <;> try omega




/-- `invc` for `baliR` (Isabelle `invc_baliR`). -/
public theorem invc_baliR (l : Tree α Color) (a : α) (r : Tree α Color) (hinvc : invc l) (hinvc2 : invc2 r) :
    invc (baliR l a r) := by
  cases r with
  | Leaf =>
    have heq : baliR l a (Tree.Leaf : Tree α Color) = BNode l a Tree.Leaf := rfl
    rw [heq]
    simp_all [invc, invc2, col, RNode, BNode] <;> try omega
  | Node lr kv rr =>
    obtain ⟨b, c⟩ := kv
    cases rr with
    | Leaf =>
      cases c with
      | Red =>
        cases lr with
        | Leaf =>
          have heq : baliR l a (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) = BNode l a (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) := rfl
          rw [heq]
          simp_all [invc, invc2, col, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Red) Tree.Leaf) =
                RNode (BNode l a t2) b' (BNode t3 b Tree.Leaf) := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Red) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Red) Tree.Leaf) := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
      | Black =>
        cases lr with
        | Leaf =>
          have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) Tree.Leaf) = BNode l a (Tree.Node Tree.Leaf (b, .Black) Tree.Leaf) := rfl
          rw [heq]
          simp_all [invc, invc2, col, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Black) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Black) Tree.Leaf) := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Black) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Black) Tree.Leaf) := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
    | Node t3 kv1 t4 =>
      obtain ⟨d, dc⟩ := kv1
      cases c with
      | Red =>
        cases dc with
        | Red =>
          have heq : baliR l a (Tree.Node lr (b, .Red) (Tree.Node t3 (d, .Red) t4)) =
              RNode (BNode l a lr) b (BNode t3 d t4) := rfl
          rw [heq]
          simp_all [invc, invc2, col, RNode, BNode] <;> try omega
        | Black =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t3 (d, .Black) t4)) := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) =
                  RNode (BNode l a t2') b' (BNode t3' b (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, col, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, col, RNode, BNode] <;> try omega
      | Black =>
        cases dc with
        | Red =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, col, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, col, RNode, BNode] <;> try omega
        | Black =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
            rw [heq]
            simp_all [invc, invc2, col, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, col, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invc, invc2, col, RNode, BNode] <;> try omega




/-- `invh` for `baliR` (Isabelle `invh_baliR`). -/
public theorem invh_baliR (l : Tree α Color) (a : α) (r : Tree α Color) (hinvh_l : invh l) (hinvh_r : invh r) (hbh : bheight l = bheight r) :
    invh (baliR l a r) := by
  cases r with
  | Leaf =>
    have heq : baliR l a (Tree.Leaf : Tree α Color) = BNode l a Tree.Leaf := rfl
    rw [heq]
    simp_all [invh, bheight, RNode, BNode] <;> try omega
  | Node lr kv rr =>
    obtain ⟨b, c⟩ := kv
    cases rr with
    | Leaf =>
      cases c with
      | Red =>
        cases lr with
        | Leaf =>
          have heq : baliR l a (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) = BNode l a (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) := rfl
          rw [heq]
          simp_all [invh, bheight, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Red) Tree.Leaf) =
                RNode (BNode l a t2) b' (BNode t3 b Tree.Leaf) := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Red) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Red) Tree.Leaf) := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
      | Black =>
        cases lr with
        | Leaf =>
          have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) Tree.Leaf) = BNode l a (Tree.Node Tree.Leaf (b, .Black) Tree.Leaf) := rfl
          rw [heq]
          simp_all [invh, bheight, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Black) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Black) Tree.Leaf) := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Black) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Black) Tree.Leaf) := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
    | Node t3 kv1 t4 =>
      obtain ⟨d, dc⟩ := kv1
      cases c with
      | Red =>
        cases dc with
        | Red =>
          have heq : baliR l a (Tree.Node lr (b, .Red) (Tree.Node t3 (d, .Red) t4)) =
              RNode (BNode l a lr) b (BNode t3 d t4) := rfl
          rw [heq]
          simp_all [invh, bheight, RNode, BNode] <;> try omega
        | Black =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t3 (d, .Black) t4)) := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) =
                  RNode (BNode l a t2') b' (BNode t3' b (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invh, bheight, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invh, bheight, RNode, BNode] <;> try omega
      | Black =>
        cases dc with
        | Red =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
              rw [heq]
              simp_all [invh, bheight, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
              rw [heq]
              simp_all [invh, bheight, RNode, BNode] <;> try omega
        | Black =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
            rw [heq]
            simp_all [invh, bheight, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invh, bheight, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [invh, bheight, RNode, BNode] <;> try omega




/-- Black height of `baliR` (Isabelle `bheight_baliR`). -/
public theorem bheight_baliR (l : Tree α Color) (a : α) (r : Tree α Color) (hbh : bheight l = bheight r) :
    bheight (baliR l a r) = bheight l + 1 := by
  cases r with
  | Leaf =>
    have heq : baliR l a (Tree.Leaf : Tree α Color) = BNode l a Tree.Leaf := rfl
    rw [heq]
    simp_all [bheight, RNode, BNode] <;> try omega
  | Node lr kv rr =>
    obtain ⟨b, c⟩ := kv
    cases rr with
    | Leaf =>
      cases c with
      | Red =>
        cases lr with
        | Leaf =>
          have heq : baliR l a (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) = BNode l a (Tree.Node Tree.Leaf (b, .Red) Tree.Leaf) := rfl
          rw [heq]
          simp_all [bheight, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Red) Tree.Leaf) =
                RNode (BNode l a t2) b' (BNode t3 b Tree.Leaf) := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Red) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Red) Tree.Leaf) := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
      | Black =>
        cases lr with
        | Leaf =>
          have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) Tree.Leaf) = BNode l a (Tree.Node Tree.Leaf (b, .Black) Tree.Leaf) := rfl
          rw [heq]
          simp_all [bheight, RNode, BNode] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', c2⟩ := kv2
          cases c2 with
          | Red =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Black) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Red) t3) (b, .Black) Tree.Leaf) := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
          | Black =>
            have heq : baliR l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Black) Tree.Leaf) = BNode l a (Tree.Node (Tree.Node t2 (b', .Black) t3) (b, .Black) Tree.Leaf) := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
    | Node t3 kv1 t4 =>
      obtain ⟨d, dc⟩ := kv1
      cases c with
      | Red =>
        cases dc with
        | Red =>
          have heq : baliR l a (Tree.Node lr (b, .Red) (Tree.Node t3 (d, .Red) t4)) =
              RNode (BNode l a lr) b (BNode t3 d t4) := rfl
          rw [heq]
          simp_all [bheight, RNode, BNode] <;> try omega
        | Black =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Red) (Tree.Node t3 (d, .Black) t4)) := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) =
                  RNode (BNode l a t2') b' (BNode t3' b (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [bheight, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Red) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [bheight, RNode, BNode] <;> try omega
      | Black =>
        cases dc with
        | Red =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
              rw [heq]
              simp_all [bheight, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Red) t4)) := rfl
              rw [heq]
              simp_all [bheight, RNode, BNode] <;> try omega
        | Black =>
          cases lr with
          | Leaf =>
            have heq : baliR l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node Tree.Leaf (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
            rw [heq]
            simp_all [bheight, RNode, BNode] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', c2'⟩ := kv2'
            cases c2' with
            | Red =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Red) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [bheight, RNode, BNode] <;> try omega
            | Black =>
              have heq : baliR l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) = BNode l a (Tree.Node (Tree.Node t2' (b', .Black) t3') (b, .Black) (Tree.Node t3 (d, .Black) t4)) := rfl
              rw [heq]
              simp_all [bheight, RNode, BNode] <;> try omega




public theorem set_joinL (l : Tree α Color) (x : α) (r : Tree α Color) :
    set_tree (joinL l x r) = set_tree l ∪ {x} ∪ set_tree r := by
  induction r generalizing l with
  | Leaf =>
    simp [joinL, RNode, set_tree]
  | Node l' kv r' ih =>
    obtain ⟨x', c⟩ := kv
    by_cases hb : bheight l ≥ bheight (Tree.Node l' (x', c) r')
    · simp only [joinL, ite_eq_left hb]
      ext y; simp only [RNode, set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto
    · simp only [joinL, ite_eq_right hb]
      cases c with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        rw [baliL_set, ih]
        ext y; simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto
      | Red =>
        simp only [reduceCtorEq, ite_false]
        rw [set_RNode, ih]
        ext y; simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto

public theorem set_joinR (l : Tree α Color) (x : α) (r : Tree α Color) :
    set_tree (joinR l x r) = set_tree l ∪ {x} ∪ set_tree r := by
  induction l generalizing r with
  | Leaf =>
    simp [joinR, RNode, set_tree]
  | Node l' kv r' ihl ihr =>
    obtain ⟨x', c⟩ := kv
    by_cases hb : bheight (Tree.Node l' (x', c) r') ≤ bheight r
    · simp only [joinR, ite_eq_left hb]
      ext y; simp only [RNode, set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto
    · simp only [joinR, ite_eq_right hb]
      cases c with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        rw [baliR_set, ihr]
        ext y; simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto
      | Red =>
        simp only [reduceCtorEq, ite_false]
        rw [set_RNode, ihr]
        ext y; simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto



/-- `invc` implies the weaker `invc2`. -/
public theorem invc2_of_invc (t : Tree α Color) (h : invc t) : invc2 t := by
  cases t with
  | Leaf => trivial
  | Node l kv r => exact ⟨h.2.1, h.2.2⟩

/-- `paint Black` restores `invc` from `invc2` (root color becomes `Black`). -/
public theorem invc_paint_Black (t : Tree α Color) (h : invc2 t) : invc (paint .Black t) := by
  cases t with
  | Leaf => trivial
  | Node l kv r => exact ⟨by simp, h.1, h.2⟩

/-- `paint` does not affect `invh` (it only changes the root color). -/
public theorem invh_paint (c : Color) (t : Tree α Color) : invh (paint c t) = invh t := by
  cases t with
  | Leaf => rfl
  | Node l kv r => rfl

/-- `paint` does not affect `bst` (it only changes the root color). -/
public theorem bst_paint (c : Color) (t : Tree α Color) : bst (paint c t) = bst t := by
  cases t with
  | Leaf => rfl
  | Node l kv r => rfl

/-- `paint` does not affect `set_tree`. -/
public theorem set_paint (c : Color) (t : Tree α Color) : set_tree (paint c t) = set_tree t := by
  cases t with
  | Leaf => rfl
  | Node l kv r => rfl

/-- `bst` for `joinL` (Isabelle `bst_joinL`, unconditional here). -/
public theorem bst_joinL (l : Tree α Color) (x : α) (r : Tree α Color) (c : Color)
    (h : bst (Tree.Node l (x, c) r)) : bst (joinL l x r) := by
  revert h
  induction r generalizing l with
  | Leaf =>
    intro h
    have heq : joinL l x (Tree.Leaf : Tree α Color) = RNode l x Tree.Leaf := by simp [joinL]
    rw [heq]
    exact bst_N l Tree.Leaf x .Red h.1 trivial h.2.2.1 (by simp)
  | Node l' kv r' ih =>
    intro h
    obtain ⟨x', c'⟩ := kv
    obtain ⟨hbl, hbr, hl, hr⟩ := h
    have hbl' : bst l' := hbr.1
    have hbr' : bst r' := hbr.2.1
    have hl' : ∀ y ∈ set_tree l', y < x' := hbr.2.2.1
    have hr' : ∀ y ∈ set_tree r', x' < y := hbr.2.2.2
    have hxx' : x < x' := hr x' (by
      simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]
      exact Or.inl (Or.inr trivial))
    have hbst_node : bst (Tree.Node l (x, .Black) l') :=
      ⟨hbl, hbl', hl, fun y hy => hr y (by
        simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]
        exact Or.inl (Or.inl hy))⟩
    have hjoinl : bst (joinL l x l') := ih l hbst_node
    have hbound : ∀ y ∈ set_tree (joinL l x l'), y < x' := by
      intro y hy
      rw [set_joinL] at hy
      simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
      rcases hy with (hy | rfl) | hy
      · exact lt_trans (hl y hy) hxx'
      · exact hxx'
      · exact hl' y hy
    have hr'_bound : ∀ y ∈ set_tree r', x' < y := hr'
    by_cases hb : bheight l ≥ bheight (Tree.Node l' (x', c') r')
    · simp only [joinL, ite_eq_left hb]
      exact bst_N l (Tree.Node l' (x', c') r') x .Red hbl hbr hl hr
    · simp only [joinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        exact baliL_bst (joinL l x l') x' r' hjoinl hbr' hbound hr'_bound
      | Red =>
        simp only [reduceCtorEq, ite_false]
        exact bst_N (joinL l x l') r' x' .Red hjoinl hbr' hbound hr'_bound

/-- `bst` for `joinR` (mirror of `bst_joinL`). -/
public theorem bst_joinR (l : Tree α Color) (x : α) (r : Tree α Color) (c : Color)
    (h : bst (Tree.Node l (x, c) r)) : bst (joinR l x r) := by
  revert h
  induction l generalizing r with
  | Leaf =>
    intro h
    have heq : joinR (Tree.Leaf : Tree α Color) x r = RNode Tree.Leaf x r := by simp [joinR]
    rw [heq]
    exact bst_N Tree.Leaf r x .Red trivial h.2.1 (by simp) h.2.2.2
  | Node l' kv r' ihl ihr =>
    intro h
    obtain ⟨x', c'⟩ := kv
    obtain ⟨hbl, hbr, hl, hr⟩ := h
    have hbl' : bst l' := hbl.1
    have hbr' : bst r' := hbl.2.1
    have hl' : ∀ y ∈ set_tree l', y < x' := hbl.2.2.1
    have hr' : ∀ y ∈ set_tree r', x' < y := hbl.2.2.2
    have hx'x : x' < x := hl x' (by
      simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]
      exact Or.inl (Or.inr trivial))
    have hbst_node : bst (Tree.Node r' (x, .Black) r) :=
      ⟨hbr', hbr, fun y hy => hl y (by
        simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]
        exact Or.inr hy), hr⟩
    have hjoinr : bst (joinR r' x r) := ihr r hbst_node
    have hbound : ∀ y ∈ set_tree (joinR r' x r), x' < y := by
      intro y hy
      rw [set_joinR] at hy
      simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
      rcases hy with (hy | rfl) | hy
      · exact hr' y hy
      · exact hx'x
      · exact lt_trans hx'x (hr y hy)
    by_cases hb : bheight (Tree.Node l' (x', c') r') ≤ bheight r
    · simp only [joinR, ite_eq_left hb]
      exact bst_N (Tree.Node l' (x', c') r') r x .Red hbl hbr hl hr
    · simp only [joinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        exact baliR_bst l' x' (joinR r' x r) hbl' hjoinr hl' hbound
      | Red =>
        simp only [reduceCtorEq, ite_false]
        exact bst_N l' (joinR r' x r) x' .Red hbl' hjoinr hl' hbound



/-- Invariants for `joinL` (Isabelle `inv_joinL`). -/
public theorem inv_joinL (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvc_l : invc l) (hinvc_r : invc r) (hinvh_l : invh l) (hinvh_r : invh r)
    (hbh : bheight l ≤ bheight r) :
    invc2 (joinL l x r) ∧ (bheight l ≠ bheight r ∧ col r = .Black → invc (joinL l x r))
      ∧ invh (joinL l x r) ∧ bheight (joinL l x r) = bheight r := by
  revert hinvc_l hinvc_r hinvh_l hinvh_r hbh
  induction r generalizing l with
  | Leaf =>
    intro hinvc_l hinvc_r hinvh_l hinvh_r hbh
    have hbhl : bheight l = 0 := Nat.le_zero.mp hbh
    have heq : joinL l x (Tree.Leaf : Tree α Color) = RNode l x Tree.Leaf := by simp [joinL]
    rw [heq]
    refine ⟨⟨hinvc_l, trivial⟩, ?_, ⟨hbhl, hinvh_l, trivial⟩, hbhl⟩
    intro hcon
    exact absurd hcon.1 (by simp [hbhl, bheight])
  | Node l' kv r' ih =>
    intro hinvc_l hinvc_r hinvh_l hinvh_r hbh
    obtain ⟨x', c'⟩ := kv
    have hinvc_l' : invc l' := hinvc_r.2.1
    have hinvc_r' : invc r' := hinvc_r.2.2
    have hinvh_l' : invh l' := hinvh_r.2.1
    have hinvh_r' : invh r' := hinvh_r.2.2
    have hbh_lr : bheight l' = bheight r' := hinvh_r.1
    have hbhr : bheight (Tree.Node l' (x', c') r') =
        (if c' = .Black then bheight l' + 1 else bheight l') := rfl
    by_cases hb : bheight l ≥ bheight (Tree.Node l' (x', c') r')
    · have hbh_eq : bheight l = bheight (Tree.Node l' (x', c') r') := by omega
      simp only [joinL, ite_eq_left hb]
      refine ⟨⟨hinvc_l, hinvc_r⟩, fun hcon => absurd hcon.1 (by simp [hbh_eq]),
        ⟨hbh_eq, hinvh_l, hinvh_r⟩, hbh_eq⟩
    · simp only [joinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        have hbh_l' : bheight l ≤ bheight l' := by
          simp only [eq_self_iff_true, ite_true] at hbhr; omega
        obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ := ih l hinvc_l hinvc_l' hinvh_l hinvh_l' hbh_l'
        obtain ⟨hinvc_b, hinvh_b, hbh_b⟩ := baliL_inv (joinL l x l') x' r' hinvh_j hinvh_r' hinvc2_j hinvc_r' (by omega)
        refine ⟨invc2_of_invc _ hinvc_b, fun _ => hinvc_b, hinvh_b, ?_⟩
        simp only [eq_self_iff_true, ite_true] at hbhr
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have hbh_l' : bheight l ≤ bheight l' := by
          simp only [reduceCtorEq, ite_false] at hbhr; omega
        obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ := ih l hinvc_l hinvc_l' hinvh_l hinvh_l' hbh_l'
        have hbhR : bheight (RNode (joinL l x l') x' r') = bheight (joinL l x l') := rfl
        have hcol_l' : col l' = .Black := (hinvc_r.1 rfl).1
        have hinvc_j : invc (joinL l x l') := hcond_j ⟨by
          simp only [reduceCtorEq, ite_false] at hbhr; omega, hcol_l'⟩
        refine ⟨⟨hinvc_j, hinvc_r'⟩, fun hcon => absurd hcon.2 (by simp [col]), ⟨?_, hinvh_j, hinvh_r'⟩, ?_⟩
        · simp only [reduceCtorEq, ite_false] at hbhr; omega
        · rw [hbhR]; simp only [reduceCtorEq, ite_false] at hbhr; omega

/-- Invariants for `joinR` (mirror of `inv_joinL`). -/
public theorem inv_joinR (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvc_l : invc l) (hinvc_r : invc r) (hinvh_l : invh l) (hinvh_r : invh r)
    (hbh : bheight r ≤ bheight l) :
    invc2 (joinR l x r) ∧ (bheight l ≠ bheight r ∧ col l = .Black → invc (joinR l x r))
      ∧ invh (joinR l x r) ∧ bheight (joinR l x r) = bheight l := by
  revert hinvc_l hinvc_r hinvh_l hinvh_r hbh
  induction l generalizing r with
  | Leaf =>
    intro hinvc_l hinvc_r hinvh_l hinvh_r hbh
    have hbhr : bheight r = 0 := Nat.le_zero.mp hbh
    have heq : joinR (Tree.Leaf : Tree α Color) x r = RNode Tree.Leaf x r := by simp [joinR]
    rw [heq]
    refine ⟨⟨trivial, hinvc_r⟩, ?_, ⟨hbhr.symm, trivial, hinvh_r⟩, rfl⟩
    intro hcon
    exact absurd hcon.1 (by simp [hbhr, bheight])
  | Node l' kv r' ihl ihr =>
    intro hinvc_l hinvc_r hinvh_l hinvh_r hbh
    obtain ⟨x', c'⟩ := kv
    have hinvc_l' : invc l' := hinvc_l.2.1
    have hinvc_r' : invc r' := hinvc_l.2.2
    have hinvh_l' : invh l' := hinvh_l.2.1
    have hinvh_r' : invh r' := hinvh_l.2.2
    have hbh_lr : bheight l' = bheight r' := hinvh_l.1
    have hbhl : bheight (Tree.Node l' (x', c') r') =
        (if c' = .Black then bheight l' + 1 else bheight l') := rfl
    by_cases hb : bheight (Tree.Node l' (x', c') r') ≤ bheight r
    · have hbh_eq : bheight (Tree.Node l' (x', c') r') = bheight r := by omega
      simp only [joinR, ite_eq_left hb]
      refine ⟨⟨hinvc_l, hinvc_r⟩, fun hcon => absurd hcon.1 (by simp [hbh_eq]),
        ⟨hbh_eq, hinvh_l, hinvh_r⟩, rfl⟩
    · simp only [joinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        have hbh_r' : bheight r ≤ bheight r' := by
          simp only [eq_self_iff_true, ite_true] at hbhl; omega
        obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ := ihr r hinvc_r' hinvc_r hinvh_r' hinvh_r hbh_r'
        obtain ⟨hinvc_b, hinvh_b, hbh_b⟩ := baliR_inv l' x' (joinR r' x r) hinvh_l' hinvh_j hinvc_l' hinvc2_j (by omega)
        refine ⟨invc2_of_invc _ hinvc_b, fun _ => hinvc_b, hinvh_b, ?_⟩
        simp only [eq_self_iff_true, ite_true] at hbhl
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have hbh_r' : bheight r ≤ bheight r' := by
          simp only [reduceCtorEq, ite_false] at hbhl; omega
        obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ := ihr r hinvc_r' hinvc_r hinvh_r' hinvh_r hbh_r'
        have hbhR : bheight (RNode l' x' (joinR r' x r)) = bheight l' := rfl
        have hcol_r' : col r' = .Black := (hinvc_l.1 rfl).2
        have hinvc_j : invc (joinR r' x r) := hcond_j ⟨by
          simp only [reduceCtorEq, ite_false] at hbhl; omega, hcol_r'⟩
        refine ⟨⟨hinvc_l', hinvc_j⟩, fun hcon => absurd hcon.2 (by simp [col]), ⟨?_, hinvh_l', hinvh_j⟩, ?_⟩
        · simp only [reduceCtorEq, ite_false] at hbhl; omega
        · rw [hbhR]; simp only [reduceCtorEq, ite_false] at hbhl; omega



/-- `set` for `rbtJoin` (Isabelle `set_join`). -/
public theorem set_rbtJoin (l : Tree α Color) (x : α) (r : Tree α Color) :
    set_tree (rbtJoin l x r) = set_tree l ∪ {x} ∪ set_tree r := by
  simp only [rbtJoin]
  by_cases h1 : bheight l > bheight r
  · rw [ite_eq_left h1, set_paint, set_joinR]
  · rw [ite_eq_right h1]
    by_cases h2 : bheight l < bheight r
    · rw [ite_eq_left h2, set_paint, set_joinL]
    · rw [ite_eq_right h2]
      exact set_BNode l r x

/-- `bst` for `rbtJoin` (Isabelle `bst_join`). -/
public theorem bst_rbtJoin (l : Tree α Color) (x : α) (r : Tree α Color) (c : Color)
    (h : bst (Tree.Node l (x, c) r)) : bst (rbtJoin l x r) := by
  simp only [rbtJoin]
  by_cases h1 : bheight l > bheight r
  · rw [ite_eq_left h1, bst_paint]; exact bst_joinR l x r c h
  · rw [ite_eq_right h1]
    by_cases h2 : bheight l < bheight r
    · rw [ite_eq_left h2, bst_paint]; exact bst_joinL l x r c h
    · rw [ite_eq_right h2]; exact bst_N l r x .Black h.1 h.2.1 h.2.2.1 h.2.2.2

/-- `rbtJoin` preserves `invc ∧ invh` (Isabelle `inv_join`). Isabelle's
`rbt_join` additionally states that the root is black, which this
declaration does not. -/
public theorem inv_rbtJoin (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinv_l : invc l ∧ invh l) (hinv_r : invc r ∧ invh r) :
    invc (rbtJoin l x r) ∧ invh (rbtJoin l x r) := by
  simp only [rbtJoin]
  by_cases h1 : bheight l > bheight r
  · rw [ite_eq_left h1]
    obtain ⟨hinvc2_j, -, hinvh_j, -⟩ :=
      inv_joinR l x r hinv_l.1 hinv_r.1 hinv_l.2 hinv_r.2 (le_of_lt h1)
    exact ⟨invc_paint_Black _ hinvc2_j, by rw [invh_paint]; exact hinvh_j⟩
  · rw [ite_eq_right h1]
    by_cases h2 : bheight l < bheight r
    · rw [ite_eq_left h2]
      obtain ⟨hinvc2_j, -, hinvh_j, -⟩ :=
        inv_joinL l x r hinv_l.1 hinv_r.1 hinv_l.2 hinv_r.2 (le_of_lt h2)
      exact ⟨invc_paint_Black _ hinvc2_j, by rw [invh_paint]; exact hinvh_j⟩
    · rw [ite_eq_right h2]
      have hbh : bheight l = bheight r := by omega
      exact ⟨⟨by simp, hinv_l.1, hinv_r.1⟩, ⟨hbh, hinv_l.2, hinv_r.2⟩⟩

public instance : Inhabited Color := ⟨.Black⟩

/-- The red–black `JoinData` instance: `inv t = invc t ∧ invh t`. -/
public def rbtJoinData : JoinData α Color where
  join := rbtJoin
  inv := fun t => invc t ∧ invh t
  inv_leaf := ⟨trivial, trivial⟩
  set_join := fun l x r => set_rbtJoin l x r
  bst_join := fun l x b r h => bst_rbtJoin l x r b h
  inv_join := fun l x r hinv_l hinv_r => inv_rbtJoin l x r hinv_l hinv_r
  inv_node := fun l kv r h => ⟨⟨h.1.2.1, h.2.2.1⟩, ⟨h.1.2.2, h.2.2.2⟩⟩

/-- Red–black `union` via the generic framework (Isabelle `union_rbt`). -/
public def rbtUnion (t₁ t₂ : Tree α Color) : Tree α Color := union rbtJoinData t₁ t₂

public theorem rbtUnion_set (t₁ t₂ : Tree α Color) (hbst₂ : bst t₂) :
    set_tree (rbtUnion t₁ t₂) = set_tree t₁ ∪ set_tree t₂ :=
  union_set (J := rbtJoinData) t₁ t₂ hbst₂

public theorem rbtUnion_bst (t₁ t₂ : Tree α Color) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (rbtUnion t₁ t₂) := union_bst (J := rbtJoinData) t₁ t₂ hbst₁ hbst₂

public theorem rbtUnion_inv (t₁ t₂ : Tree α Color)
    (hinv₁ : invc t₁ ∧ invh t₁) (hinv₂ : invc t₂ ∧ invh t₂) :
    invc (rbtUnion t₁ t₂) ∧ invh (rbtUnion t₁ t₂) :=
  union_inv (J := rbtJoinData) t₁ t₂ hinv₁ hinv₂

/-- Red–black `inter` via the generic framework (Isabelle `inter_rbt`). -/
public def rbtInter (t₁ t₂ : Tree α Color) : Tree α Color := inter rbtJoinData t₁ t₂

public theorem rbtInter_set (t₁ t₂ : Tree α Color) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    set_tree (rbtInter t₁ t₂) = set_tree t₁ ∩ set_tree t₂ :=
  inter_set (J := rbtJoinData) t₁ t₂ hbst₁ hbst₂

public theorem rbtInter_bst (t₁ t₂ : Tree α Color) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (rbtInter t₁ t₂) := inter_bst (J := rbtJoinData) t₁ t₂ hbst₁ hbst₂

public theorem rbtInter_inv (t₁ t₂ : Tree α Color)
    (hinv₁ : invc t₁ ∧ invh t₁) (hinv₂ : invc t₂ ∧ invh t₂) :
    invc (rbtInter t₁ t₂) ∧ invh (rbtInter t₁ t₂) :=
  inter_inv (J := rbtJoinData) t₁ t₂ hinv₁ hinv₂

/-- Red–black `diff` via the generic framework (Isabelle `diff_rbt`). -/
public def rbtDiff (t₁ t₂ : Tree α Color) : Tree α Color := diff rbtJoinData t₁ t₂

public theorem rbtDiff_set (t₁ t₂ : Tree α Color) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    set_tree (rbtDiff t₁ t₂) = set_tree t₁ \ set_tree t₂ :=
  diff_set (J := rbtJoinData) t₁ t₂ hbst₁ hbst₂

public theorem rbtDiff_bst (t₁ t₂ : Tree α Color) (hbst₁ : bst t₁) (hbst₂ : bst t₂) :
    bst (rbtDiff t₁ t₂) := diff_bst (J := rbtJoinData) t₁ t₂ hbst₁ hbst₂

public theorem rbtDiff_inv (t₁ t₂ : Tree α Color)
    (hinv₁ : invc t₁ ∧ invh t₁) (hinv₂ : invc t₂ ∧ invh t₂) :
    invc (rbtDiff t₁ t₂) ∧ invh (rbtDiff t₁ t₂) :=
  diff_inv (J := rbtJoinData) t₁ t₂ hinv₁ hinv₂

/-- Red–black `insert` / `delete` via the generic framework. -/
public def rbtInsert (x : α) (t : Tree α Color) : Tree α Color := insert rbtJoinData x t

public theorem rbtInsert_set (x : α) (t : Tree α Color) (hbst : bst t) :
    set_tree (rbtInsert x t) = set_tree t ∪ {x} :=
  insert_set (J := rbtJoinData) x t hbst

public theorem rbtInsert_bst (x : α) (t : Tree α Color) (hbst : bst t) :
    bst (rbtInsert x t) := insert_bst (J := rbtJoinData) x t hbst

public theorem rbtInsert_inv (x : α) (t : Tree α Color) (hinv : invc t ∧ invh t) :
    invc (rbtInsert x t) ∧ invh (rbtInsert x t) :=
  insert_inv (J := rbtJoinData) x t hinv

public def rbtDelete (x : α) (t : Tree α Color) : Tree α Color := delete rbtJoinData x t

public theorem rbtDelete_set (x : α) (t : Tree α Color) (hbst : bst t) :
    set_tree (rbtDelete x t) = set_tree t \ {x} :=
  delete_set (J := rbtJoinData) x t hbst

public theorem rbtDelete_bst (x : α) (t : Tree α Color) (hbst : bst t) :
    bst (rbtDelete x t) := delete_bst (J := rbtJoinData) x t hbst

public theorem rbtDelete_inv (x : α) (t : Tree α Color) (hinv : invc t ∧ invh t) :
    invc (rbtDelete x t) ∧ invh (rbtDelete x t) :=
  delete_inv (J := rbtJoinData) x t hinv



/-- `invc2` for `joinL`, without `invh` hypotheses (Isabelle `invc2_joinL`). -/
public theorem invc2_joinL (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvc_l : invc l) (hinvc_r : invc r) (hbh : bheight l ≤ bheight r) :
    invc2 (joinL l x r) ∧ (bheight l ≠ bheight r ∧ col r = .Black → invc (joinL l x r)) := by
  revert hinvc_l hinvc_r hbh
  induction r generalizing l with
  | Leaf =>
    intro hinvc_l hinvc_r hbh
    have hbhl : bheight l = 0 := Nat.le_zero.mp hbh
    have heq : joinL l x (Tree.Leaf : Tree α Color) = RNode l x Tree.Leaf := by simp [joinL]
    rw [heq]
    refine ⟨⟨hinvc_l, trivial⟩, fun hcon => absurd hcon.1 (by simp [hbhl, bheight])⟩
  | Node l' kv r' ih =>
    intro hinvc_l hinvc_r hbh
    obtain ⟨x', c'⟩ := kv
    have hinvc_l' : invc l' := hinvc_r.2.1
    have hinvc_r' : invc r' := hinvc_r.2.2
    have hbhr : bheight (Tree.Node l' (x', c') r') =
        (if c' = .Black then bheight l' + 1 else bheight l') := rfl
    by_cases hb : bheight l ≥ bheight (Tree.Node l' (x', c') r')
    · have hbh_eq : bheight l = bheight (Tree.Node l' (x', c') r') := by omega
      simp only [joinL, ite_eq_left hb]
      exact ⟨⟨hinvc_l, hinvc_r⟩, fun hcon => absurd hcon.1 (by simp [hbh_eq])⟩
    · simp only [joinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        have hbh_l' : bheight l ≤ bheight l' := by
          simp only [eq_self_iff_true, ite_true] at hbhr; omega
        obtain ⟨hinvc2_j, hcond_j⟩ := ih l hinvc_l hinvc_l' hbh_l'
        have hinvc_b : invc (baliL (joinL l x l') x' r') := invc_baliL _ _ _ hinvc2_j hinvc_r'
        exact ⟨invc2_of_invc _ hinvc_b, fun _ => hinvc_b⟩
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have hbh_l' : bheight l ≤ bheight l' := by
          simp only [reduceCtorEq, ite_false] at hbhr; omega
        obtain ⟨hinvc2_j, hcond_j⟩ := ih l hinvc_l hinvc_l' hbh_l'
        have hcol_l' : col l' = .Black := (hinvc_r.1 rfl).1
        have hinvc_j : invc (joinL l x l') := hcond_j ⟨by
          simp only [reduceCtorEq, ite_false] at hbhr; omega, hcol_l'⟩
        exact ⟨⟨hinvc_j, hinvc_r'⟩, fun hcon => absurd hcon.2 (by simp [col])⟩

/-- `invc2` for `joinR` (Isabelle `invc2_joinR` — note it takes `invh`
hypotheses, unlike `invc2_joinL`). -/
public theorem invc2_joinR (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvc_l : invc l) (hinvh_l : invh l) (hinvc_r : invc r) (hinvh_r : invh r)
    (hbh : bheight r ≤ bheight l) :
    invc2 (joinR l x r) ∧ (bheight l ≠ bheight r ∧ col l = .Black → invc (joinR l x r)) := by
  revert hinvc_l hinvh_l hinvc_r hinvh_r hbh
  induction l generalizing r with
  | Leaf =>
    intro hinvc_l hinvh_l hinvc_r hinvh_r hbh
    have hbhr : bheight r = 0 := Nat.le_zero.mp hbh
    have heq : joinR (Tree.Leaf : Tree α Color) x r = RNode Tree.Leaf x r := by simp [joinR]
    rw [heq]
    exact ⟨⟨trivial, hinvc_r⟩, fun hcon => absurd hcon.1 (by simp [hbhr, bheight])⟩
  | Node l' kv r' ihl ihr =>
    intro hinvc_l hinvh_l hinvc_r hinvh_r hbh
    obtain ⟨x', c'⟩ := kv
    have hinvc_l' : invc l' := hinvc_l.2.1
    have hinvc_r' : invc r' := hinvc_l.2.2
    have hinvh_l' : invh l' := hinvh_l.2.1
    have hinvh_r' : invh r' := hinvh_l.2.2
    have hbh_lr : bheight l' = bheight r' := hinvh_l.1
    have hbhl : bheight (Tree.Node l' (x', c') r') =
        (if c' = .Black then bheight l' + 1 else bheight l') := rfl
    by_cases hb : bheight (Tree.Node l' (x', c') r') ≤ bheight r
    · have hbh_eq : bheight (Tree.Node l' (x', c') r') = bheight r := by omega
      simp only [joinR, ite_eq_left hb]
      exact ⟨⟨hinvc_l, hinvc_r⟩, fun hcon => absurd hcon.1 (by simp [hbh_eq])⟩
    · simp only [joinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        have hbh_r' : bheight r ≤ bheight r' := by
          simp only [eq_self_iff_true, ite_true] at hbhl; omega
        obtain ⟨hinvc2_j, hcond_j⟩ := ihr r hinvc_r' hinvh_r' hinvc_r hinvh_r hbh_r'
        have hinvc_b : invc (baliR l' x' (joinR r' x r)) := invc_baliR _ _ _ hinvc_l' hinvc2_j
        exact ⟨invc2_of_invc _ hinvc_b, fun _ => hinvc_b⟩
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have hbh_r' : bheight r ≤ bheight r' := by
          simp only [reduceCtorEq, ite_false] at hbhl; omega
        obtain ⟨hinvc2_j, hcond_j⟩ := ihr r hinvc_r' hinvh_r' hinvc_r hinvh_r hbh_r'
        have hcol_r' : col r' = .Black := (hinvc_l.1 rfl).2
        have hinvc_j : invc (joinR r' x r) := hcond_j ⟨by
          simp only [reduceCtorEq, ite_false] at hbhl; omega, hcol_r'⟩
        exact ⟨⟨hinvc_l', hinvc_j⟩, fun hcon => absurd hcon.2 (by simp [col])⟩

/-- `invh` and black height of `joinL`, proved together (Isabelle
`invh_joinL` + `bheight_joinL`, stated without `invc` hypotheses). -/
public theorem invh_bheight_joinL (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvh_l : invh l) (hinvh_r : invh r) (hbh : bheight l ≤ bheight r) :
    invh (joinL l x r) ∧ bheight (joinL l x r) = bheight r := by
  revert hinvh_l hinvh_r hbh
  induction r generalizing l with
  | Leaf =>
    intro hinvh_l hinvh_r hbh
    have hbhl : bheight l = 0 := Nat.le_zero.mp hbh
    have heq : joinL l x (Tree.Leaf : Tree α Color) = RNode l x Tree.Leaf := by simp [joinL]
    rw [heq]
    exact ⟨⟨hbhl, hinvh_l, trivial⟩, hbhl⟩
  | Node l' kv r' ih =>
    intro hinvh_l hinvh_r hbh
    obtain ⟨x', c'⟩ := kv
    have hinvh_l' : invh l' := hinvh_r.2.1
    have hinvh_r' : invh r' := hinvh_r.2.2
    have hbh_lr : bheight l' = bheight r' := hinvh_r.1
    have hbhr : bheight (Tree.Node l' (x', c') r') =
        (if c' = .Black then bheight l' + 1 else bheight l') := rfl
    by_cases hb : bheight l ≥ bheight (Tree.Node l' (x', c') r')
    · have hbh_eq : bheight l = bheight (Tree.Node l' (x', c') r') := by omega
      simp only [joinL, ite_eq_left hb]
      exact ⟨⟨hbh_eq, hinvh_l, hinvh_r⟩, hbh_eq⟩
    · simp only [joinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        have hbh_l' : bheight l ≤ bheight l' := by
          simp only [eq_self_iff_true, ite_true] at hbhr; omega
        obtain ⟨hinvh_j, hbh_j⟩ := ih l hinvh_l hinvh_l' hbh_l'
        have hinvh_b := invh_baliL (joinL l x l') x' r' hinvh_j hinvh_r' (by omega)
        have hbh_b := bheight_baliL (joinL l x l') x' r' (by omega)
        refine ⟨hinvh_b, ?_⟩
        simp only [eq_self_iff_true, ite_true] at hbhr
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have hbh_l' : bheight l ≤ bheight l' := by
          simp only [reduceCtorEq, ite_false] at hbhr; omega
        obtain ⟨hinvh_j, hbh_j⟩ := ih l hinvh_l hinvh_l' hbh_l'
        have hbhR : bheight (RNode (joinL l x l') x' r') = bheight (joinL l x l') := rfl
        refine ⟨⟨by omega, hinvh_j, hinvh_r'⟩, ?_⟩
        rw [hbhR]; simp only [reduceCtorEq, ite_false] at hbhr; omega

/-- `invh` for `joinL` (Isabelle `invh_joinL`). -/
public theorem invh_joinL (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvh_l : invh l) (hinvh_r : invh r) (hbh : bheight l ≤ bheight r) :
    invh (joinL l x r) := (invh_bheight_joinL l x r hinvh_l hinvh_r hbh).1

/-- Black height of `joinL` (Isabelle `bheight_joinL`). -/
public theorem bheight_joinL (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvh_l : invh l) (hinvh_r : invh r) (hbh : bheight l ≤ bheight r) :
    bheight (joinL l x r) = bheight r := (invh_bheight_joinL l x r hinvh_l hinvh_r hbh).2

/-- `invh` and black height of `joinR`, proved together (Isabelle
`invh_joinR` + `bheight_joinR`). -/
public theorem invh_bheight_joinR (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvh_l : invh l) (hinvh_r : invh r) (hbh : bheight r ≤ bheight l) :
    invh (joinR l x r) ∧ bheight (joinR l x r) = bheight l := by
  revert hinvh_l hinvh_r hbh
  induction l generalizing r with
  | Leaf =>
    intro hinvh_l hinvh_r hbh
    have hbhr : bheight r = 0 := Nat.le_zero.mp hbh
    have heq : joinR (Tree.Leaf : Tree α Color) x r = RNode Tree.Leaf x r := by simp [joinR]
    rw [heq]
    exact ⟨⟨hbhr.symm, trivial, hinvh_r⟩, rfl⟩
  | Node l' kv r' ihl ihr =>
    intro hinvh_l hinvh_r hbh
    obtain ⟨x', c'⟩ := kv
    have hinvh_l' : invh l' := hinvh_l.2.1
    have hinvh_r' : invh r' := hinvh_l.2.2
    have hbh_lr : bheight l' = bheight r' := hinvh_l.1
    have hbhl : bheight (Tree.Node l' (x', c') r') =
        (if c' = .Black then bheight l' + 1 else bheight l') := rfl
    by_cases hb : bheight (Tree.Node l' (x', c') r') ≤ bheight r
    · have hbh_eq : bheight (Tree.Node l' (x', c') r') = bheight r := by omega
      simp only [joinR, ite_eq_left hb]
      exact ⟨⟨hbh_eq, hinvh_l, hinvh_r⟩, rfl⟩
    · simp only [joinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        have hbh_r' : bheight r ≤ bheight r' := by
          simp only [eq_self_iff_true, ite_true] at hbhl; omega
        obtain ⟨hinvh_j, hbh_j⟩ := ihr r hinvh_r' hinvh_r hbh_r'
        have hinvh_b := invh_baliR l' x' (joinR r' x r) hinvh_l' hinvh_j (by omega)
        have hbh_b := bheight_baliR l' x' (joinR r' x r) (by omega)
        refine ⟨hinvh_b, ?_⟩
        simp only [eq_self_iff_true, ite_true] at hbhl
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have hbh_r' : bheight r ≤ bheight r' := by
          simp only [reduceCtorEq, ite_false] at hbhl; omega
        obtain ⟨hinvh_j, hbh_j⟩ := ihr r hinvh_r' hinvh_r hbh_r'
        have hbhR : bheight (RNode l' x' (joinR r' x r)) = bheight l' := rfl
        refine ⟨⟨by omega, hinvh_l', hinvh_j⟩, ?_⟩
        rw [hbhR]; simp only [reduceCtorEq, ite_false] at hbhl; omega

/-- `invh` for `joinR` (Isabelle `invh_joinR`). -/
public theorem invh_joinR (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvh_l : invh l) (hinvh_r : invh r) (hbh : bheight r ≤ bheight l) :
    invh (joinR l x r) := (invh_bheight_joinR l x r hinvh_l hinvh_r hbh).1

/-- Black height of `joinR` (Isabelle `bheight_joinR`). -/
public theorem bheight_joinR (l : Tree α Color) (x : α) (r : Tree α Color)
    (hinvh_l : invh l) (hinvh_r : invh r) (hbh : bheight r ≤ bheight l) :
    bheight (joinR l x r) = bheight l := (invh_bheight_joinR l x r hinvh_l hinvh_r hbh).2

/-- Root color of `joinL` (analogue, for these trees, of AFP
`StronglyJoinableRBT.thy`'s `col_joinL`). -/
public theorem col_joinL (l : Tree α Color) (x : α) (r : Tree α Color)
    (hlt : bheight l < bheight r) (hcol : col r = .Red) :
    col (joinL l x r) = .Red := by
  induction r generalizing l with
  | Leaf =>
    simp [col, bheight] at hlt
  | Node l' kv r' ih =>
    obtain ⟨x', c'⟩ := kv
    by_cases hb : bheight l ≥ bheight (Tree.Node l' (x', c') r')
    · omega
    · simp only [joinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp [col] at hcol
      | Red =>
        simp only [reduceCtorEq, ite_false]
        exact col_RNode _ _ _

/-- Root color of `joinR` (analogue, for these trees, of AFP
`StronglyJoinableRBT.thy`'s `col_joinR`). -/
public theorem col_joinR (l : Tree α Color) (x : α) (r : Tree α Color)
    (hlt : bheight r < bheight l) (hcol : col l = .Red) :
    col (joinR l x r) = .Red := by
  induction l generalizing r with
  | Leaf =>
    simp [col, bheight] at hlt
  | Node l' kv r' ihl ihr =>
    obtain ⟨x', c'⟩ := kv
    by_cases hb : bheight (Tree.Node l' (x', c') r') ≤ bheight r
    · omega
    · simp only [joinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp [col] at hcol
      | Red =>
        simp only [reduceCtorEq, ite_false]
        exact col_RNode _ _ _

/-- `paint Black` increases the black height by at most one
(Isabelle `bheight_paint_Black`). -/
public theorem bheight_paint_Black (t : Tree α Color) :
    bheight (paint .Black t) ≤ bheight t + 1 := by
  cases t with
  | Leaf => simp [paint, bheight]
  | Node l kv r =>
    obtain ⟨a, c⟩ := kv
    cases c with
    | Black => simp [paint, bheight]
    | Red => simp [paint, bheight]



/-- Inorder key list (Isabelle `inorder`). -/
public def inorder : Tree α Color → List α
  | .Leaf => []
  | .Node l (a, _) r => inorder l ++ a :: inorder r


public theorem inorder_paint (c : Color) (t : Tree α Color) :
    inorder (paint c t) = inorder t := by
  cases t with
  | Leaf => rfl
  | Node l kv r => obtain ⟨a, _⟩ := kv; rfl

public theorem tsize_paint (c : Color) (t : Tree α Color) :
    tsize (paint c t) = tsize t := by
  cases t with
  | Leaf => rfl
  | Node l kv r => obtain ⟨a, _⟩ := kv; rfl

/-- `inorder` for `baliL` (Isabelle `inorder_baliL`). -/
public theorem inorder_baliL (l : Tree α Color) (a : α) (r : Tree α Color) :
    inorder (baliL l a r) = inorder l ++ a :: inorder r := by
  fun_cases baliL l a r <;> simp [inorder, RNode, BNode, List.append_assoc]

/-- `inorder` for `baliR` (Isabelle `inorder_baliR`). -/
public theorem inorder_baliR (l : Tree α Color) (a : α) (r : Tree α Color) :
    inorder (baliR l a r) = inorder l ++ a :: inorder r := by
  fun_cases baliR l a r <;> simp [inorder, RNode, BNode, List.append_assoc]

/-- Node count for `baliL` (analogue, for these trees, of AFP
`StronglyJoinableRBT.thy`'s `size_baliL`). -/
public theorem tsize_baliL (l : Tree α Color) (a : α) (r : Tree α Color) :
    tsize (baliL l a r) = tsize l + tsize r + 1 := by
  fun_cases baliL l a r <;> simp [tsize, RNode, BNode] <;> omega

/-- Node count for `baliR` (analogue, for these trees, of AFP
`StronglyJoinableRBT.thy`'s `size_baliR`). -/
public theorem tsize_baliR (l : Tree α Color) (a : α) (r : Tree α Color) :
    tsize (baliR l a r) = tsize l + tsize r + 1 := by
  fun_cases baliR l a r <;> simp [tsize, RNode, BNode] <;> omega

/-- `inorder` for `joinL` (Isabelle `inorder_joinL`). -/
public theorem inorder_joinL (l : Tree α Color) (x : α) (r : Tree α Color)
    (hbh : bheight l ≤ bheight r) :
    inorder (joinL l x r) = inorder l ++ x :: inorder r := by
  revert hbh
  induction r generalizing l with
  | Leaf =>
    intro hbh
    simp [joinL, inorder, RNode]
  | Node l' kv r' ih =>
    intro hbh
    obtain ⟨x', c'⟩ := kv
    by_cases hb : bheight l ≥ bheight (Tree.Node l' (x', c') r')
    · simp only [joinL, ite_eq_left hb]
      simp [inorder, RNode]
    · simp only [joinL, ite_eq_right hb]
      have hbhr : bheight (Tree.Node l' (x', c') r') =
          (if c' = .Black then bheight l' + 1 else bheight l') := rfl
      have hbh_l' : bheight l ≤ bheight l' := by
        cases c' with
        | Black => simp only [eq_self_iff_true, ite_true] at hbhr; omega
        | Red => simp only [reduceCtorEq, ite_false] at hbhr; omega
      -- NOTE: the `cases c'` above is only for the `have`; re-case below on
      -- the color for the equation. (The `have` did not split the goal.)
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        simp [inorder_baliL, ih l hbh_l', inorder, List.append_assoc]
      | Red =>
        simp only [reduceCtorEq, ite_false]
        simp [ih l hbh_l', inorder, RNode, List.append_assoc]

/-- `inorder` for `joinR` (Isabelle `inorder_joinR`). -/
public theorem inorder_joinR (l : Tree α Color) (x : α) (r : Tree α Color) :
    inorder (joinR l x r) = inorder l ++ x :: inorder r := by
  induction l generalizing r with
  | Leaf =>
    simp [joinR, inorder, RNode]
  | Node l' kv r' ihl ihr =>
    obtain ⟨x', c'⟩ := kv
    by_cases hb : bheight (Tree.Node l' (x', c') r') ≤ bheight r
    · simp only [joinR, ite_eq_left hb]
      simp [inorder, RNode]
    · simp only [joinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        simp [inorder_baliR, ihr, inorder, List.append_assoc]
      | Red =>
        simp only [reduceCtorEq, ite_false]
        simp [ihr, inorder, RNode, List.append_assoc]

/-- `inorder` for `join` (Isabelle's unnamed `inorder (join …)` lemma). -/
public theorem inorder_rbtJoin (l : Tree α Color) (x : α) (r : Tree α Color) :
    inorder (rbtJoin l x r) = inorder l ++ x :: inorder r := by
  simp only [rbtJoin]
  by_cases h1 : bheight l > bheight r
  · rw [ite_eq_left h1, inorder_paint]
    exact inorder_joinR l x r
  · rw [ite_eq_right h1]
    by_cases h2 : bheight l < bheight r
    · rw [ite_eq_left h2, inorder_paint]
      exact inorder_joinL l x r (le_of_lt h2)
    · rw [ite_eq_right h2]
      simp [inorder, BNode]

/-- Node count for `joinL` (analogue, for these trees, of AFP
`StronglyJoinableRBT.thy`'s `size_joinL`). -/
public theorem tsize_joinL (l : Tree α Color) (x : α) (r : Tree α Color) :
    tsize (joinL l x r) = tsize l + tsize r + 1 := by
  induction r generalizing l with
  | Leaf =>
    simp [joinL, tsize, RNode]
  | Node l' kv r' ih =>
    obtain ⟨x', c'⟩ := kv
    by_cases hb : bheight l ≥ bheight (Tree.Node l' (x', c') r')
    · simp only [joinL, ite_eq_left hb]
      simp [tsize, RNode]
    · simp only [joinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        rw [tsize_baliL, ih]
        simp [tsize]
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have h : tsize (RNode (joinL l x l') x' r') = tsize (joinL l x l') + tsize r' + 1 := rfl
        rw [h, ih]
        simp [tsize]
        omega

/-- Node count for `joinR` (analogue, for these trees, of AFP
`StronglyJoinableRBT.thy`'s `size_joinR`). -/
public theorem tsize_joinR (l : Tree α Color) (x : α) (r : Tree α Color) :
    tsize (joinR l x r) = tsize l + tsize r + 1 := by
  induction l generalizing r with
  | Leaf =>
    simp [joinR, tsize, RNode]
  | Node l' kv r' ihl ihr =>
    obtain ⟨x', c'⟩ := kv
    by_cases hb : bheight (Tree.Node l' (x', c') r') ≤ bheight r
    · simp only [joinR, ite_eq_left hb]
      simp [tsize, RNode]
    · simp only [joinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        rw [tsize_baliR, ihr]
        simp [tsize]
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have h : tsize (RNode l' x' (joinR r' x r)) = tsize l' + tsize (joinR r' x r) + 1 := rfl
        rw [h, ihr]
        simp [tsize]
        omega

/-- Node count for `join` (analogue, for these trees and this `join`, of AFP
`StronglyJoinableRBT.thy`'s `join_size`). -/
public theorem tsize_rbtJoin (l : Tree α Color) (x : α) (r : Tree α Color) :
    tsize (rbtJoin l x r) = tsize l + tsize r + 1 := by
  simp only [rbtJoin]
  by_cases h1 : bheight l > bheight r
  · rw [ite_eq_left h1, tsize_paint]
    exact tsize_joinR l x r
  · rw [ite_eq_right h1]
    by_cases h2 : bheight l < bheight r
    · rw [ite_eq_left h2, tsize_paint]
      exact tsize_joinL l x r
    · rw [ite_eq_right h2]
      simp [tsize, BNode]

end JoinableBinarySearchTree

end Cslib.Algorithms.Lean
