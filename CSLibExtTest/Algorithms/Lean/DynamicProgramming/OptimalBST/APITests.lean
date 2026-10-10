/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Cost
public import Mathlib.Basic.Real.Basic

set_option autoImplicit false
universe u
open Cslib.Algorithms.Lean.BinarySearchTree
open Cslib.Algorithms.Lean.OptimalBST

#check @expectedSearchCost
#check @optimalBST
#check @optimalBST_empty
#check @optimalBST_table_spec
#check @optimalBST_minimal
#check @optimalBST_time
#check @optimalBST_time_bounds

example {R : Type u} [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]
    (n : Nat) (p : Vector R n) (q : Vector R (n + 1)) :
    IsLeast {z : R | ∃ (tree : BinaryTree (Fin n))
      (complete : inorder tree = List.finRange n),
      expectedSearchCost n p q tree complete = z} (optimalBST p q).ret.1[0][n] :=
  optimalBST_minimal n p q

example (p : Vector Rat 2) (q : Vector Rat 3) :
    (optimalBST p q).time = 4 := by
  simpa using optimalBST_time _ p q

example (p : Vector Real 2) (q : Vector Real 3) :
    IsLeast {z : Real | ∃ (tree : BinaryTree (Fin 2))
      (complete : inorder tree = List.finRange 2),
      expectedSearchCost 2 p q tree complete = z} (optimalBST p q).ret.1[0][2] :=
  optimalBST_minimal 2 p q

example {R : Type u} [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]
    (p : Vector R 0) (q : Vector R 1) :
    (optimalBST p q).time = 0 := by
  simpa using optimalBST_time _ p q
