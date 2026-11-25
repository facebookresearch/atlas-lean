/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LeftistHeap
public import CSLibExt.Algorithms.Lean.DataStructures.LeftistHeapPriorityQueue
import Mathlib.Tactic
@[expose] public section

namespace Cslib.Algorithms.Lean.LHeap

def dupHeap : LHeap Nat :=
  insert (insert (insert (LHeap.E : LHeap Nat) 2) 1) 2

example : findMin? (LHeap.E : LHeap Nat) = none := rfl

example : extractMin (LHeap.E : LHeap Nat) = none := rfl

example : findMin? (insert (LHeap.E : LHeap Nat) 1) = some 1 := rfl

example : extractMin (insert (LHeap.E : LHeap Nat) 1) = some (1, LHeap.E) := rfl

example : findMin? dupHeap = some 1 := rfl

example : (extractMin dupHeap).map Prod.fst = some 1 := rfl

example : ((extractMin dupHeap).bind fun (_, h1) =>
    (extractMin h1).map Prod.fst) = some 2 := rfl

example (h' : LHeap Nat) (hx : extractMin dupHeap = some (1, h')) :
    {1} + mset_tree h' = mset_tree dupHeap :=
  extractMin_mset hx

example {h h' : LHeap Nat} {x y : Nat} (hh : heap h)
    (hx : extractMin h = some (x, h')) (hy : y ∈ mset_tree h) : x ≤ y :=
  extractMin_le hh hx hy

end Cslib.Algorithms.Lean.LHeap
