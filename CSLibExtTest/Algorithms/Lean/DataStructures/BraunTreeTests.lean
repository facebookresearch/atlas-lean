/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree

/-!
# Braun-tree regression tests

Concrete computations for the core Braun-tree priority queue:
`insert`, `delLeft`, `siftDown`, `delMin`, `getMin`, `isEmpty`,
together with the invariant and multiset preservation theorems
applied to small trees. All checks are kernel-checked `example`s
using the public API; well-founded-recursive functions are unfolded
with their equation lemmas (`simp [siftDown, ...]`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BraunTreeTests

open BraunTree

/-- `insert` into the empty tree. -/
example : insert 1 (BraunTree.Leaf : BraunTree ℕ) =
    BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf := by decide

/-- `insert` preserves the multiset (theorem application). -/
example : msetTree (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) =
    ({1, 2} : Multiset ℕ) := by
  decide

/-- `insert` preserves `Braun` and `Heap` (theorem applications). -/
example : Braun (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) :=
  braun_insert 2 (braun_insert 1 trivial)

example : Heap (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) :=
  heap_insert 2 (heap_insert 1 trivial)

/-- `delLeft` removes the leftmost element. -/
example : delLeft (BraunTree.Node BraunTree.Leaf 1
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) =
    some (1, BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) := by decide

/-- `delLeft` on the empty tree is `none`. -/
example : delLeft (BraunTree.Leaf : BraunTree ℕ) = none := by decide

/-- `getMin` returns the minimum. -/
example : getMin (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) = some 1 := by
  decide

/-- `getMin` on the empty tree is `none`. -/
example : getMin (BraunTree.Leaf : BraunTree ℕ) = none := by decide

/-- `isEmpty` on the empty and non-empty trees. -/
example : isEmpty (BraunTree.Leaf : BraunTree ℕ) = true := by decide

example : isEmpty (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf) = false := by
  decide

/-- `siftDown` with a smaller element on top. -/
example : siftDown (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
    BraunTree.Leaf =
    BraunTree.Node (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
      BraunTree.Leaf := by
  simp [siftDown]

/-- `delMin` removes the minimum. -/
example : delMin (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) =
    BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf := by
  simp [delMin, delLeft, BraunTree.insert, siftDown]

/-- `delMin` on the empty tree is empty. -/
example : delMin (BraunTree.Leaf : BraunTree ℕ) = BraunTree.Leaf := by decide

/-- Sizes and heights on a small tree. -/
example : size (BraunTree.Node BraunTree.Leaf 1
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) = 2 := by decide

example : height (BraunTree.Node BraunTree.Leaf 1
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) = 2 := by decide

/-- The `msetTree` of a small tree. -/
example : msetTree (BraunTree.Node BraunTree.Leaf 1
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) = ({1, 2} : Multiset ℕ) := by
  decide

end Cslib.Algorithms.Lean.BraunTreeTests
