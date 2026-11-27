/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.FenwickTree.ProbeBounds
public meta import CSLibExt.Algorithms.Lean.DataStructures.FenwickTree.ProbeBounds
public meta import CSLibExt.Algorithms.Lean.DataStructures.FenwickTree
public meta import Mathlib.Algebra.Group.Nat.Defs

/-!
# Tests for Fenwick tree index walks

Check the visit lists themselves, then compare them with a prefix query and a point update
on the array-backed implementation. `Nat` needs no additive inverses.
-/

namespace Cslib.Algorithms.Lean.FenwickTree

#guard prefixVisits 0 17 == []
#guard prefixVisits 5 0 == []
#guard updateVisits 0 1 == []
#guard updateVisits 5 0 == []
#guard updateVisits 5 6 == []

#guard prefixVisits 1 1 == [1]
#guard prefixVisits 1 2 == [1]
#guard updateVisits 1 1 == [1]
#guard updateVisits 1 2 == []

-- The power-of-two root is one block, but the preceding prefix needs several blocks.
#guard prefixVisits 8 7 == [7, 6, 4]
#guard prefixVisits 8 8 == [8]
#guard updateVisits 8 1 == [1, 2, 4, 8]
#guard updateVisits 8 8 == [8]
#guard (updateVisits 8 1).length == (8 : Nat).log2 + 1

-- At a non-power-of-two size, clamping keeps the last block, and the update stops before 16.
#guard prefixVisits 13 99 == [13, 12, 8]
#guard updateVisits 13 9 == [9, 10, 12]
#guard updateVisits 13 13 == [13]
#guard (prefixVisits 13 99).reverse.flatMap (fun j => List.range' (j - lowbit j) (lowbit j)) ==
  List.range 13

private def sampleEntries : List Nat := List.range' 1 13

private def sample : FenwickTree Nat := build sampleEntries

#guard sample.prefixSum 11 == 66
#guard sample.prefixSum 99 == 91
#guard sample.prefixSum 99 ==
  ((prefixVisits sample.size 99).map (fun j => sample.bit.getD j 0)).sum

-- The public `add` takes a zero-based index, so position 8 starts the walk at endpoint 9.
-- A nonzero delta on `Nat` makes every changed stored entry observable, including the check
-- that the dummy entry and unvisited entries are not changed.
#guard ((List.range (sample.size + 1)).filter fun j =>
  (sample.add 8 100).bit.getD j 0 != sample.bit.getD j 0) == updateVisits sample.size 9
#guard (sample.add 13 100).bit == sample.bit

example {α : Type*} [AddCommMonoid α] (a : List α) (k : Nat) :
    ((prefixVisits a.length k).map (blockSum a)).sum = (a.take k).sum :=
  sum_prefixVisits_blockSum a k

-- These arrays are not built from an underlying list. The query reads the actual stored
-- values, and neither operation needs a representation invariant (or a zero dummy).
private def arbitraryTree : FenwickTree Nat := ⟨#[99, 11, 22, 33, 44, 55, 66, 77]⟩

#guard arbitraryTree.prefixSum 0 == 0
#guard arbitraryTree.prefixSum 3 == 55
#guard arbitraryTree.prefixSum 99 == 187
#guard (arbitraryTree.add 2 5).bit == #[99, 11, 22, 38, 49, 55, 66, 77]
#guard (arbitraryTree.add 7 5).bit == arbitraryTree.bit
#guard (arbitraryTree.add 2 0).bit == arbitraryTree.bit

private def emptyStorage : FenwickTree Nat := ⟨#[]⟩
private def dummyOnly : FenwickTree Nat := ⟨#[99]⟩

#guard emptyStorage.prefixSum 99 == 0
#guard (emptyStorage.add 0 5).bit == #[]
#guard dummyOnly.prefixSum 99 == 0
#guard (dummyOnly.add 0 5).bit == #[99]

example {α : Type*} [AddCommMonoid α] (t : FenwickTree α) (k : Nat) :
    t.prefixSum k = ((prefixVisits t.size k).map (fun j => t.bit.getD j 0)).sum :=
  prefixSum_eq_sum_prefixVisits t k

example {α : Type*} [AddCommMonoid α] (t : FenwickTree α) (i j : Nat) (δ : α) :
    (t.add i δ).bit.getD j 0 =
      t.bit.getD j 0 + (if j ∈ updateVisits t.size (i + 1) then δ else 0) :=
  getD_add_eq t i δ j

#print axioms prefixUpdate_probeBounds
#print axioms sum_prefixVisits_blockSum
#print axioms prefixSum_eq_sum_prefixVisits
#print axioms getD_add_eq

end Cslib.Algorithms.Lean.FenwickTree
