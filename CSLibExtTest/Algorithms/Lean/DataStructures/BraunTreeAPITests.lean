/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree

/-!
# Braun-tree API tests

Public-API contracts exercised as theorem applications (no reduction
needed): the ADT discharge `pq_spec` fields, the step-counting time
bounds, and the logarithmic-height bound, on concrete small trees.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BraunTreeAPITests

open BraunTree

/-- `T_insert` is at most the height plus one (book #16). -/
example : T_insert 3 (insert 2 (BraunTree.Leaf : BraunTree ℕ)) ≤
    height (insert 2 (BraunTree.Leaf : BraunTree ℕ)) + 1 :=
  T_insert_le 3 _

/-- `T_delLeft` is at most the height (book #17). -/
example : T_delLeft (BraunTree.Node BraunTree.Leaf 1
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) ≤
    height (BraunTree.Node BraunTree.Leaf 1
      (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) :=
  T_delLeft_le (by simp)

/-- `T_siftDown` is at most the max height plus one (book #18). -/
example : T_siftDown (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) 1
    BraunTree.Leaf ≤
    max (height (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf))
      (height (BraunTree.Leaf : BraunTree ℕ)) + 1 :=
  T_siftDown_le (by simp [Braun, size])

/-- `T_delMin` is at most twice the height (Lemma 16.1, book #20). -/
example : T_delMin (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) ≤
    2 * height (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) :=
  T_delMin_le (braun_insert 2 (braun_insert 1 trivial))

/-- Braun trees have logarithmic height. -/
example : 2 ^ height (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) ≤
    2 * size (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) + 1 :=
  braun_height_size (braun_insert 2 (braun_insert 1 trivial))

/-- The deleted element is the minimum (book #15, `getMin` form). -/
example : ∃ a, getMin (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) = some a ∧
    msetTree (delMin (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ)))) =
    msetTree (insert 2 (insert 1 (BraunTree.Leaf : BraunTree ℕ))) - {a} :=
  mset_delMin_getMin (braun_insert 2 (braun_insert 1 trivial)) (by simp [BraunTree.insert])

/-- `delLeft` removes exactly one element (book #5, minus form). -/
example : 1 ∈ msetTree (BraunTree.Node BraunTree.Leaf 1
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) ∧
    msetTree (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) =
    msetTree (BraunTree.Node BraunTree.Leaf 1
      (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf)) - {1} :=
  delLeft_mset_sub (by decide)

/-- `isEmpty` is the emptiness test: `pq_spec`'s emptiness field. -/
example : ∀ (t : BraunTree ℕ), isEmpty t = true ↔ msetTree t = 0 := by
  obtain ⟨_, _, _, _, _, _, hEmpty⟩ := pq_spec (α := ℕ)
  exact hEmpty

end Cslib.Algorithms.Lean.BraunTreeAPITests
