/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Complete

/-!
# Complete / almost-complete tree tests

Concrete computations for `size1`, `minHeight`, `complete`,
`acomplete`, and `nlog2`, plus the bridge theorems
(`height_acomplete`, `acomplete_if_braun`, `acomplete_optimal`)
applied to small trees.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BraunTree.CompleteTests

open BraunTree
open BraunTree.Complete

/-- `size1` counts leaves. -/
example : size1 (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf) = 2 := by decide

/-- `size1 t = size t + 1`. -/
example : size1 (BraunTree.Node BraunTree.Leaf 1
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) =
    size (BraunTree.Node BraunTree.Leaf 1
      (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) + 1 :=
  size1_size _

/-- `minHeight` of a single-node tree and of a chain. -/
example : minHeight (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf) = 1 := by decide

example : minHeight (BraunTree.Node (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf) 2
    BraunTree.Leaf) = 1 := by decide

/-- `complete` holds for the empty tree and for a perfect tree. -/
example : complete (BraunTree.Leaf : BraunTree ℕ) := trivial

example : complete (BraunTree.Node (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf) 2
    (BraunTree.Node BraunTree.Leaf 3 BraunTree.Leaf)) := by
  simp [complete, height]

/-- `acomplete` holds for a Braun tree (via `acomplete_if_braun`). -/
example : acomplete (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) :=
  acomplete_if_braun (braun_insert 2 (braun_insert 1 trivial))

/-- `height_acomplete` on a small almost-complete tree. -/
example : height (BraunTree.Node BraunTree.Leaf 1
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) =
    Nat.clog 2 (size1 (BraunTree.Node BraunTree.Leaf 1
      (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf))) := by
  apply height_acomplete
  simp [acomplete, minHeight, height]

/-- `nlog2` values. -/
example : nlog2 1 = 0 := by decide

example : nlog2 2 = 1 := by decide

example : nlog2 8 = 3 := by decide

example : nlog2 100 = 7 := by decide

/-- `acomplete_optimal`: almost-complete trees have minimal height. -/
example : acomplete (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) →
    size (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) ≤
      size (BraunTree.Node BraunTree.Leaf 1
        (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) →
    height (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) ≤
      height (BraunTree.Node BraunTree.Leaf 1
        (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) :=
  fun h hs => acomplete_optimal h hs

end Cslib.Algorithms.Lean.BraunTree.CompleteTests
