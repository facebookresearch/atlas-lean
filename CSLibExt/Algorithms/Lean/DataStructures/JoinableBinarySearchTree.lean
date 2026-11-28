/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.RedBlackJoin
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.AvlJoin
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.TwoThreeJoin
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.StronglyJoinable
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.StronglyJoinableRBT
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.StronglyJoinableAVL

/-!
# Joinable binary search trees

The `Set2` interface of Chapter 10 of *Functional Data Structures and
Algorithms* (Nipkow, ed., book pp. 117–125): binary search trees with a
generic `join` operation, from which `split`, `insert`, `delete`,
`union`, `inter`, and `diff` are all derived. Import the submodules
separately when only one instantiation is needed:

- `Basic`: the generic join framework (`JoinData`, `split_min`,
  `join2`, `split`, `union` / `inter` / `diff`, Exercises 10.1–10.2).
- `RedBlackJoin`: the red–black `join` (Figure 10.4).
- `AvlJoin`: the AVL `join` (Chapter 9 + AFP).
- `TwoThreeJoin`: the 2–3-tree `join` (Exercise 10.3).
- `StronglyJoinable`: the strongly joinable framework
  (`StronglyJoinableData`).
- `StronglyJoinableRBT`: the stored-height red–black instance.
- `StronglyJoinableAVL`: the AVL instance.

The generic `O(m log (n/m + 1))` work analysis for `union` / `inter` /
`diff` is out of scope (the book cites Blelloch et al. for it).
-/
