/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LeftistHeap.ConstructionCost

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LeftistHeap.ConstructionCostTests

open Cslib.Algorithms.Lean.LeftistHeap.ConstructionCost

#check mergeCostBound
#check mergeAdjacent
#check mergeAdjacent_length
#check mergeAdjacentCost
#check mergeAllCostAux_stable
#check mergeAllCost_unfold_pow
#check fdsa_chap15_ex01
#check fdsa_chap15_ex02

-- All four list shapes exercise the adjacent-pass recurrence.
example : mergeAdjacent Nat.add [] = [] := rfl
example : mergeAdjacent Nat.add [7] = [7] := rfl
example : mergeAdjacent Nat.add [1, 2, 3, 4] = [3, 7] := rfl
example : mergeAdjacent Nat.add [1, 2, 3, 4, 5] = [3, 7, 5] := rfl

example : mergeCostBound 0 = 1 := by decide
example : mergeCostBound 1 = 3 := by decide
example : mergeCostBound 3 = 5 := by decide

-- The unpaired final input contributes no cost.
example : mergeAdjacentCost (fun a b : Nat => a + b) [] = 0 := rfl
example : mergeAdjacentCost (fun a b : Nat => a + b) [7] = 0 := rfl
example : mergeAdjacentCost (fun a b : Nat => a + b) [1, 2, 3] = 3 := rfl
example : mergeAdjacentCost (fun a b : Nat => a + b) [1, 2, 3, 4] = 10 := rfl

-- Insufficient fuel is deliberately not the public cost; sufficient fuel is stable.
example : mergeAllCostAux Nat.add (fun _ _ => 1) 0 [1, 1, 1, 1] = 0 := rfl
example : mergeAllCost Nat.add (fun _ _ => 1) [] = 0 := rfl
example : mergeAllCost Nat.add (fun _ _ => 1) [7] = 0 := rfl
example : mergeAllCost Nat.add (fun _ _ => 1) [1, 1, 1] = 2 := rfl
example : mergeAllCost Nat.add (fun _ _ => 1) [1, 1, 1, 1] = 3 := rfl
example : mergeAllCostAux Nat.add (fun _ _ => 1) 9 [1, 1, 1, 1]
    = mergeAllCost Nat.add (fun _ _ => 1) [1, 1, 1, 1] := by
  exact mergeAllCostAux_stable Nat.add (fun _ _ => 1) [1, 1, 1, 1] 9 (by decide)

-- Exercise the single-pass theorem with its fixed-size, not all-size, premise.
example (n : Nat) :
    mergeAdjacentCost (fun _ _ : Nat => mergeCostBound n) [n, n, n]
      ≤ ([n, n, n].length / 2) * mergeCostBound n := by
  apply fdsa_chap15_ex02 (fun _ : Nat => True) id
    (fun _ _ => mergeCostBound n) [n, n, n] n
  · simp
  · simp
  · intros
    exact Nat.le_refl _

-- A nonvacuous model: sizes add, the invariant is true, each merge costs one.
-- This exercises the complete power-of-two theorem, including its size premise.
example : mergeAllCost Nat.add (fun _ _ => 1) [1, 1, 1, 1]
    ≤ ∑ i ∈ Finset.Icc 1 2,
      2 ^ (2 - i) * mergeCostBound (2 ^ (i - 1) * 1) := by
  apply fdsa_chap15_ex01 (fun _ : Nat => True) id Nat.add
    (fun _ _ => 1) [1, 1, 1, 1] 1 2
  · simp
  · simp
  · rfl
  · intros
    rfl
  · intros
    trivial
  · intro a b m _ _ _ _
    change 1 ≤ 2 * Nat.log2 (m + 1) + 1
    omega

-- k = 0 is an actual singleton case, not an empty-list case.
example (n : Nat) : mergeAllCost Nat.add (fun _ _ => 1) [n]
    ≤ ∑ i ∈ Finset.Icc 1 0,
      2 ^ (0 - i) * mergeCostBound (2 ^ (i - 1) * n) := by
  apply fdsa_chap15_ex01 (fun _ : Nat => True) id Nat.add
    (fun _ _ => 1) [n] n 0
  · simp
  · simp
  · rfl
  · intros
    rfl
  · intros
    trivial
  · intro a b m _ _ _ _
    change 1 ≤ 2 * Nat.log2 (m + 1) + 1
    omega

end Cslib.Algorithms.Lean.LeftistHeap.ConstructionCostTests
