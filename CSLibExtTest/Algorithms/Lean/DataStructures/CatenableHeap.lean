/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.CatenableHeap

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.CatenableHeap.Tests

open Cslib.Algorithms.Lean

/-! Ordinary (non-monadic) wrappers: the heap each timed operation returns. -/

/-- The empty heap, without its cost. -/
private meta def makeHeap : CatenableHeap Nat :=
  (CatenableHeap.make : TimeM ℕ (CatenableHeap Nat)).ret

/-- `insert` without its cost. -/
private meta def insertHeap (x : Nat) (h : CatenableHeap Nat) : CatenableHeap Nat :=
  (CatenableHeap.insert x h).ret

/-- `union` without its cost. -/
private meta def unionHeap (h₁ h₂ : CatenableHeap Nat) : CatenableHeap Nat :=
  (CatenableHeap.union h₁ h₂).ret

/-- The heap built by inserting the elements of `xs` from right to left into the empty heap. -/
private meta def ofList (xs : List Nat) : CatenableHeap Nat :=
  xs.foldr insertHeap makeHeap

private meta def a : CatenableHeap Nat := ofList [1, 2]
private meta def b : CatenableHeap Nat := ofList [3]
private meta def c : CatenableHeap Nat := ofList [4, 5, 6]
private meta def big : CatenableHeap Nat := ofList (List.range 200)

-- `make` and `insert`.
#guard makeHeap.toList = []
#guard makeHeap.size = 0
#guard (CatenableHeap.make : TimeM ℕ (CatenableHeap Nat)).time = 0
#guard (insertHeap 7 makeHeap).toList = [7]
#guard (CatenableHeap.insert 7 a).time = 1
#guard (insertHeap 7 a).toList = [7, 1, 2]
#guard (insertHeap 7 a).size = 3

-- Empty operand on either side, and on both.
#guard (unionHeap makeHeap a).toList = [1, 2]
#guard (unionHeap a makeHeap).toList = [1, 2]
#guard (unionHeap makeHeap makeHeap).toList = []
#guard (unionHeap makeHeap makeHeap).size = 0
#guard (CatenableHeap.union makeHeap a).time = 1
#guard (CatenableHeap.union a makeHeap).time = 1
#guard (CatenableHeap.union makeHeap makeHeap).time = 1

-- Duplicate elements are kept with multiplicity.
#guard (unionHeap (ofList [3, 3]) b).toList = [3, 3, 3]
#guard (unionHeap (ofList [3, 3]) b).size = 3
#guard (unionHeap (ofList [3, 3]) b).toMultiset.count 3 = 3
#guard (unionHeap a a).toList = [1, 2, 1, 2]
#guard (unionHeap a a).toMultiset = {1, 1, 2, 2}

-- Nested unions: both groupings give the same left-to-right order.
#guard (unionHeap (unionHeap a b) c).toList = [1, 2, 3, 4, 5, 6]
#guard (unionHeap a (unionHeap b c)).toList = [1, 2, 3, 4, 5, 6]
#guard (unionHeap (unionHeap a makeHeap) (unionHeap makeHeap (unionHeap b c))).toList =
  [1, 2, 3, 4, 5, 6]
#guard (unionHeap (unionHeap a b) c).size = 6
#guard (insertHeap 0 (unionHeap a (unionHeap b c))).toList = [0, 1, 2, 3, 4, 5, 6]

-- Operand order changes `toList` but not the multiset or the size.
#guard (unionHeap a b).toList = [1, 2, 3]
#guard (unionHeap b a).toList = [3, 1, 2]
#guard (unionHeap a b).toList ≠ (unionHeap b a).toList
#guard (unionHeap a b).toMultiset = (unionHeap b a).toMultiset
#guard (unionHeap a b).size = (unionHeap b a).size

-- `union` costs 1 however large its operands are.
#guard (CatenableHeap.union big big).time = 1
#guard (unionHeap big big).size = 400
#guard (unionHeap big b).toList = List.range 200 ++ [3]

end Cslib.Algorithms.Lean.CatenableHeap.Tests
