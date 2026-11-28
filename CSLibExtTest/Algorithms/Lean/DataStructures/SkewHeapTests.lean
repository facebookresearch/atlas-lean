/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SkewHeap

/-!
# Skew-heap executable regression tests

Concrete merges, operations, and small height witnesses for the skew-heap
API. All reductions and correctness checks use the public API and
kernel-checked proofs. Cost assertions count only the stated units
(`T_merge` steps / potential), not traversal or allocation.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SkewHeapTests

open SkewHeap

/-- The singleton heap holding `a`. -/
def singleton (a : ℕ) : SkewHeap.Tree ℕ := SkewHeap.Tree.node SkewHeap.Tree.leaf a SkewHeap.Tree.leaf

example : merge (singleton 0) (singleton 1) =
    SkewHeap.Tree.node (singleton 1) 0 SkewHeap.Tree.leaf := by
  simp [singleton, merge]

example : merge (singleton 1) (singleton 0) =
    SkewHeap.Tree.node (singleton 1) 0 SkewHeap.Tree.leaf := by
  simp [singleton, merge]

example : toMultiset (merge (singleton 0) (singleton 1)) = {0} + {1} := by
  rw [mset_merge]
  simp [singleton, toMultiset]

example : size (merge (singleton 0) (singleton 1)) = 2 := by
  rw [size_merge]
  simp [singleton, size]

example : heap (merge (singleton 0) (singleton 1)) :=
  heap_merge (heap_singleton 0) (heap_singleton 1)

example : getMin (merge (singleton 0) (singleton 1)) = some 0 := by
  simp [singleton, merge, getMin]

example : delMin (merge (singleton 0) (singleton 1)) = singleton 1 := by
  simp [singleton, merge, delMin]

example : merge2 (singleton 0) (singleton 1) =
    SkewHeap.Tree.node (singleton 1) 0 SkewHeap.Tree.leaf := by
  simp [singleton, merge2]

example : naiveMerge (singleton 0) (singleton 1) =
    SkewHeap.Tree.node SkewHeap.Tree.leaf 0 (singleton 1) := by
  simp [singleton, naiveMerge]

/-- Merging two singletons in either order keeps the multiset. -/
example : toMultiset (merge (singleton 3) (singleton 1)) =
    toMultiset (merge (singleton 1) (singleton 3)) := by
  rw [mset_merge, mset_merge]
  ac_rfl

/-- `merge` is not commutative: the merge path matters. -/
example : ∃ t1 t2 : SkewHeap.Tree ℕ, merge t1 t2 ≠ merge t2 t1 :=
  merge_not_commutative

/-- The potential is not always zero. -/
example : ∃ t : SkewHeap.Tree ℕ, Phi t ≠ 0 := exists_phi_pos

/-- Exercise 22.1 at `k = 3`: insertions `2, 1, 0` build a tree of height 3. -/
example : height (List.foldl (fun t a => SkewHeap.insert a t) SkewHeap.Tree.leaf [2, 1, 0]) = 3 := by
  simp [SkewHeap.insert, merge, height]

/-- Exercise 22.1, existence form, at `k = 3`: exactly 3 insertions. -/
example : ∃ ns : List ℕ,
    ns.length = 3 ∧
      height (List.foldl (fun t a => insert a t) SkewHeap.Tree.leaf ns) = 3 :=
  exercise_22_1 3

end Cslib.Algorithms.Lean.SkewHeapTests
