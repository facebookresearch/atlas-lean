/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree
public import CSLibExt.Algorithms.Lean.DataStructures.IntervalTree

/-!
# Stable instance names for module-prefix consumers

These existing names remain available when Atlas consumers relocate the source
modules. The membership instance retains its structural interpretation.
-/

universe u

example {α : Type u} : Membership α (BinaryTree α) :=
  Cslib.Algorithms.Lean.BinarySearchTree.instMembershipBinaryTree_cSLibExt

example {α : Type u} (tree : BinaryTree α) (value : α) :
    @Membership.mem α (BinaryTree α)
      Cslib.Algorithms.Lean.BinarySearchTree.instMembershipBinaryTree_cSLibExt
      tree value = Cslib.Algorithms.Lean.BinarySearchTree.Mem value tree := rfl

example (a b : Int) : Decidable (a ≤ b) :=
  Cslib.Algorithms.Lean.IntervalTree.instDecidableLEInt_cSLibExt a b

example (a b : Int) : Decidable (a < b) :=
  Cslib.Algorithms.Lean.IntervalTree.instDecidableLTInt_cSLibExt a b

example (a b : Int) : Decidable (a = b) :=
  Cslib.Algorithms.Lean.IntervalTree.instDecidableEqInt_cSLibExt a b
