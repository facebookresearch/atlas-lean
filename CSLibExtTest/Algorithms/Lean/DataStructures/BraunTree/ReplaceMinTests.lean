/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.ReplaceMin

/-!
# ReplaceMin / `merge` / `delMin2` regression tests

Concrete computations for the second deletion implementation
(`BraunTree.ReplaceMin`), plus the `replaceMin_siftDown` bridge and
the `Braun`/`Heap`/multiset preservation theorems applied to small
trees.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BraunTree.ReplaceMinTests

open BraunTree
open BraunTree.ReplaceMin

/-- `leRoot` on the empty and non-empty trees. -/
example : leRoot 1 (BraunTree.Leaf : BraunTree ℕ) = true := by decide

example : leRoot 1 (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) = true := by
  decide

example : leRoot 3 (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) = false := by
  decide

/-- `replaceMin` replaces the root. -/
example : replaceMin 0 (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) =
    BraunTree.Node BraunTree.Leaf 0 BraunTree.Leaf := by
  simp [replaceMin]

/-- `replaceMin` on a Braun tree is `siftDown` (theorem application). -/
example : replaceMin 0 (BraunTree.Node (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf) 2
    BraunTree.Leaf) =
    siftDown (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf) 0 BraunTree.Leaf :=
  replaceMin_siftDown (by simp [Braun, size])

/-- `merge` of two singleton heaps. -/
example : merge (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf)
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) =
    BraunTree.Node (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1 BraunTree.Leaf := by
  simp [merge]

/-- `merge` with the empty tree. -/
example : merge (BraunTree.Leaf : BraunTree ℕ)
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) =
    BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf := by
  simp [merge]

/-- `delMin2` removes the minimum. -/
example : delMin2 (BraunTree.Node (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
    BraunTree.Leaf) =
    BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf := by
  simp [delMin2, merge]

/-- `delMin2` preserves `Braun`, `Heap`, and the multiset (theorem applications). -/
example : Braun (delMin2 (BraunTree.Node (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
    BraunTree.Leaf)) :=
  braun_delMin2 (by simp [Braun, size])

example : Heap (delMin2 (BraunTree.Node (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
    BraunTree.Leaf)) :=
  heap_delMin2 (by simp [Heap, msetTree]) (by simp [Braun, size])

example : msetTree (delMin2 (BraunTree.Node (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
    BraunTree.Leaf)) =
    msetTree (BraunTree.Node (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
      BraunTree.Leaf) - {1} :=
  mset_delMin2 (by simp [Braun, size])

/-- `delLeft_braun_size`: `delLeft` preserves `Braun` and removes one element. -/
example : Braun (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf) ∧
    size (BraunTree.Node (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
      BraunTree.Leaf) =
    size (BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf) + 1 :=
  delLeft_braun_size
    (by decide : delLeft (BraunTree.Node (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
      BraunTree.Leaf) =
      some (2, BraunTree.Node BraunTree.Leaf 1 BraunTree.Leaf))
    (by simp [Braun, size])

/-- `isEmpty` is the emptiness test: `pq_spec2`'s emptiness field. -/
example : ∀ (t : BraunTree ℕ), isEmpty t = true ↔ msetTree t = 0 := by
  obtain ⟨_, _, _, _, _, _, hEmpty⟩ := pq_spec2 (α := ℕ)
  exact hEmpty

end Cslib.Algorithms.Lean.BraunTree.ReplaceMinTests
