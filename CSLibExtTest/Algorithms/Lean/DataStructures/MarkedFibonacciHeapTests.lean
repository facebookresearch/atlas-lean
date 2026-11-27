/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap.Marked
import Mathlib.Data.Nat.Basic

/-! # Operation and cost probes for the marked handle model -/

namespace Cslib.Algorithms.Lean.MarkedFibonacci.Tests

private def load : List Nat → Heap Nat
  | [] => .empty 0
  | x :: xs => (load xs).insert x x

private theorem live_load (xs : List Nat) : (load xs).live = xs.toFinset := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [load, Heap.insert, ih]

private theorem load_history (xs : List Nat) (distinct : xs.Nodup) :
    History false (load xs) xs.length xs.length (3 * xs.length) := by
  induction xs with
  | nil => exact .empty 0
  | cons x xs ih =>
    have fresh : x ∉ (load xs).live := by simpa [live_load] using distinct.notMem
    have step := History.next (ih distinct.of_cons) (Or.inr rfl)
      (Step.insert (load xs) x x fresh)
    simpa [load, Op.insertions, Nat.mul_add] using step

private def nine := load (List.range 9)
private def tree := nine.extract.1

-- Eight pending rank-zero roots cause seven actual links and leave bin 3 occupied. Four bins
-- (including the three empty ones) are both initialised and scanned. This is not a cost oracle.
example : nine.extract.2 = 40 ∧ tree.roots = [1] ∧ tree.children 1 = [2, 3, 5] ∧
    tree.children 5 = [6, 7] ∧ tree.parent 8 = some 7 := by decide +kernel

example : History false tree 10 9 67 := by
  exact .next (load_history (List.range 9) List.nodup_range) (Or.inr rfl) (.extractMin nine)

-- Lowering a root, or lowering its child to a tie, preserves edges and mark bits.
example : (tree.decrease 1 0).2 = 0 ∧ (tree.decrease 1 0).1.minimum = some 1 ∧
    (tree.decrease 2 1).2 = 0 ∧ (tree.decrease 2 1).1.parent 2 = some 1 := by decide +kernel

private def firstLoss := tree.decrease 6 0
private def secondLoss := firstLoss.1.decrease 7 0

-- A first child loss marks 5; the second cuts 5 and unmarks it, stopping at root 1. Equal
-- decreased priorities at distinct handles do not cause the cached minimum to become a non-root.
example : firstLoss.2 = 1 ∧ firstLoss.1.marked = {5} ∧ firstLoss.1.children 5 = [7] ∧
    firstLoss.1.minimum = some 6 := by decide +kernel
example : secondLoss.2 = 2 ∧ secondLoss.1.marked = ∅ ∧ secondLoss.1.roots = [5, 7, 6, 1] ∧
    secondLoss.1.children 1 = [2, 3] ∧ secondLoss.1.parent 8 = some 7 ∧
    secondLoss.1.minimum = some 6 := by decide +kernel

example : History false secondLoss.1 12 9 79 := by
  have ht : History false tree 10 9 67 :=
    .next (load_history (List.range 9) List.nodup_range) (Or.inr rfl) (.extractMin nine)
  have h₁ := History.next ht (Or.inr rfl) (Step.decrease tree 6 0 (by decide +kernel) (by decide +kernel))
  have h₂ := History.next h₁ (Or.inr rfl) (Step.decrease firstLoss.1 7 0 (by decide +kernel)
    (by decide +kernel))
  have c₁ : (tree.decrease 6 0).2 = 1 := by decide +kernel
  have c₂ : (firstLoss.1.decrease 7 0).2 = 2 := by decide +kernel
  rw [c₁, c₂] at h₂
  exact h₂

-- At rank three the Fibonacci lower bound can be tight: two different first losses leave
-- exactly the subtree 1(2,3,5(6)), of size F₅ = 5 rather than the binomial size 8.
private def tight := ((tree.decrease 4 0).1.decrease 7 0).1
example : tight.children 1 = [2, 3, 5] ∧ tight.children 2 = [] ∧ tight.children 3 = [] ∧
    tight.children 5 = [6] ∧ tight.children 6 = [] ∧ tight.marked = {3, 5} := by decide +kernel

-- Two *successive* marked parents: 15 is cut first, then 13 and 9; root 1 is never marked.
private def larger := (load (List.range 17)).extract.1
private def markedPair := ((larger.decrease 10 0).1.decrease 14 0).1
example : markedPair.marked = {9, 13} ∧ (markedPair.decrease 15 0).2 = 3 ∧
    (markedPair.decrease 15 0).1.marked = ∅ ∧ (markedPair.decrease 15 0).1.rank 1 = 3 := by decide +kernel

example : ((load []).extract.2, (load [9]).extract.2) = (1, 1) := by decide +kernel
example : ((load [0, 1, 2, 3]).extract.1.roots, (load [0, 1, 2, 3]).extract.2) =
    ([3, 1], 15) := by decide +kernel
example : (Op.extractMin (some 1)).allowance 3 = 2 := by decide +kernel

-- The two sides own different live handles, and the aggregate counts both insertions.
example : History true ((load [4]).meld (load [2])) 3 2 8 := by
  apply History.meld (m := 1) (m' := 1) (n := 1) (n' := 1) (w := 3) (w' := 3) rfl
  · exact .next (.empty 0) (Or.inl rfl) (.insert _ 4 4 (by decide +kernel))
  · exact .next (.empty 0) (Or.inl rfl) (.insert _ 2 2 (by decide +kernel))
  · decide

end Cslib.Algorithms.Lean.MarkedFibonacci.Tests
