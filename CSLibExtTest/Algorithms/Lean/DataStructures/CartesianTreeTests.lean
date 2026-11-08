/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.CartesianTree

/-!
# Tests for the Cartesian-tree API

These client examples exercise construction over the shared `BinaryTree`
carrier, including empty and singleton inputs, duplicate minima, skewed
inputs, and fuel boundaries.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.CartesianTreeTests

open CartesianTree

example : build ([] : List Nat) = .nil := rfl

example : build [7] = .node 7 .nil .nil := by decide

example : build [3, 1, 2] =
    .node 1 (.node 3 .nil .nil) (.node 2 .nil .nil) := by decide

example : BinarySearchTree.inorder (build [3, 1, 2]) = [3, 1, 2] :=
  inorder_build [3, 1, 2]

example : BinarySearchTree.inorder (build [5, 4, 3, 2, 1]) =
    [5, 4, 3, 2, 1] :=
  inorder_build [5, 4, 3, 2, 1]

example : BinarySearchTree.inorder (build [1, 2, 3, 4, 5]) =
    [1, 2, 3, 4, 5] :=
  inorder_build [1, 2, 3, 4, 5]

example : HeapOrdered (build [3, 1, 2, 1, 4]) :=
  heapOrdered_build [3, 1, 2, 1, 4]

example : ∃ m : Nat, root (build [3, 1, 2]) = some m ∧ m = 1 := by
  obtain ⟨m, hRoot⟩ := root_build_cons_isSome 3 [1, 2]
  obtain ⟨hMem, hLe⟩ := root_build_min hRoot
  refine ⟨m, hRoot, ?_⟩
  have h1 : m ≤ 1 := hLe 1 (by simp)
  simp at hMem
  omega

/-- Duplicate minima split at the first occurrence, so the second `1`
lands in the right subtree and the root is still `1`. -/
example : build [2, 1, 1] =
    .node 1 (.node 2 .nil .nil) (.node 1 .nil .nil) := by decide

example : (2 : Nat) ∈ build [3, 1, 2] := by
  rw [mem_build]
  simp

example : buildFuel 0 [3, 1, 2] = (.nil : BinaryTree Nat) := rfl

example : BinarySearchTree.inorder (buildFuel 3 [3, 1, 2]) = [3, 1, 2] :=
  inorder_buildFuel 3 [3, 1, 2] (by decide)

example : listMin 3 [1, 2] = 1 := by decide

example : listMin 3 [1, 2] ∈ [3, 1, 2] :=
  listMin_mem 3 [1, 2]

example : (splitAtFirst 1 [3, 1, 2]).1 = [3] := by decide

example : (splitAtFirst 1 [3, 1, 2]).2 = [2] := by decide

/-- The split is at the *first* occurrence: the split value does not occur
in the left part, even when it occurs again later in the input. -/
example : (1 : Nat) ∉ (splitAtFirst 1 [3, 1, 2, 1]).1 :=
  splitAtFirst_not_mem_fst 1 [3, 1, 2, 1] (by decide)

example (m : Nat) (xs : List Nat) (hm : m ∈ xs) :
    m ∉ (splitAtFirst m xs).1 :=
  splitAtFirst_not_mem_fst m xs hm

/-- A type with decidable equality but no order, to exercise
`splitAtFirst` and its specification at their `[DecidableEq α]`
generality. -/
public inductive Token where
  | a | b | c
deriving DecidableEq, Repr

example : (splitAtFirst Token.b [Token.a, Token.b, Token.c, Token.b]).1 =
    [Token.a] := by decide

example : (splitAtFirst Token.b [Token.a, Token.b, Token.c, Token.b]).2 =
    [Token.c, Token.b] := by decide

example : Token.b ∉
    (splitAtFirst Token.b [Token.a, Token.b, Token.c, Token.b]).1 :=
  splitAtFirst_not_mem_fst Token.b [Token.a, Token.b, Token.c, Token.b]
    (by decide)

example (xs : List Nat) : (BinarySearchTree.inorder (build xs)).Perm xs :=
  perm_build xs

#print axioms Cslib.Algorithms.Lean.CartesianTree.inorder_build
#print axioms Cslib.Algorithms.Lean.CartesianTree.heapOrdered_build
#print axioms Cslib.Algorithms.Lean.CartesianTree.root_build_min
#print axioms Cslib.Algorithms.Lean.CartesianTree.splitAtFirst_spec
#print axioms Cslib.Algorithms.Lean.CartesianTree.splitAtFirst_not_mem_fst

end Cslib.Algorithms.Lean.CartesianTreeTests
