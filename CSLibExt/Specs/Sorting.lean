/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

/-!
# A relational sorting contract

`SortingSpec xs ys` says that `ys` preserves every occurrence in `xs`
and is pairwise nondecreasing. It uses Lean's `List.Perm` and
`List.Pairwise`, with no algorithm, decidability, or order laws required.
The element type may inhabit any universe. In particular, `LE` need not
be a linear order; correctness of an algorithm can require stronger laws.

The contract says nothing about stability, comparison costs, or arrays.
The insertion-sort and selection-sort bridges live in separate modules.
-/

@[expose] public section

universe u

namespace CSLibExt.Specs.Sorting

variable {α : Type u} [LE α]

/-- Pairwise nondecreasing order, retaining the original spec entry point. -/
def SortedProp (xs : List α) : Prop := List.Pairwise (· ≤ ·) xs

/-- `ys` is a sorted permutation of `xs`, including duplicate occurrences. -/
def SortingSpec (xs ys : List α) : Prop :=
  List.Perm ys xs ∧ SortedProp ys

end CSLibExt.Specs.Sorting
