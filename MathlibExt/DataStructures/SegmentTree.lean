/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

/-!
# Segment tree size bound

A segment tree is a full binary tree whose leaves hold the
array entries. This module proves the build-size bound: a
full binary tree with `n` leaves has at most `2n - 1` nodes.
Query and update walk bounds are not formalized here.
-/

@[expose] public section

/-- A segment tree over an array: leaves hold entries, internal
nodes hold two subtrees (core of ALG-29a). -/
inductive SegTree (α : Type*)
  | leaf (a : α) : SegTree α
  | node (l r : SegTree α) : SegTree α

/-- Number of nodes. -/
def SegTree.size : SegTree α → ℕ
  | .leaf _ => 1
  | .node l r => l.size + r.size + 1

/-- Number of leaves. -/
def SegTree.leaves : SegTree α → ℕ
  | .leaf _ => 1
  | .node l r => l.leaves + r.leaves

/-- A full binary tree with `n` leaves has at most `2n - 1`
nodes: `size + 1 <= 2 * leaves`. This bounds segment-tree
build size and storage. -/
theorem SegTree.size_add_one_le (t : SegTree α) :
    t.size + 1 ≤ 2 * t.leaves := by
  induction t with
  | leaf _ => rfl
  | node l r ihl ihr =>
    simp only [SegTree.size, SegTree.leaves]
    omega

end
