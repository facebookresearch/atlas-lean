/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.Knapsack

@[expose] public section

open Cslib.Algorithms.Lean.TimeM.Knapsack

#check Item
#check Result
#check totalWeight
#check totalValue
#check Feasible
#check solve
#check solve_correct
#check solve_time
#check solve_time_le_three_mul

example : (solve [] 0).ret = ({ chosen := ∅, value := 0 } : Result []) := by decide
example : (solve [] 7).ret = ({ chosen := ∅, value := 0 } : Result []) := by decide

private def exactFit : List Item := [{ weight := 4, value := 7 }]

example : (solve exactFit 4).ret.value = 7 := by decide
example : (⟨0, by simp [exactFit]⟩ : Fin exactFit.length) ∈
    (solve exactFit 4).ret.chosen := by decide
example : (solve exactFit 3).ret.value = 0 := by decide
example : (⟨0, by simp [exactFit]⟩ : Fin exactFit.length) ∉
    (solve exactFit 3).ret.chosen := by decide

private def textbook : List Item :=
  [{ weight := 10, value := 60 }, { weight := 20, value := 100 },
    { weight := 30, value := 120 }]

example : (solve textbook 50).ret.value = 220 := by decide
example : (⟨0, by simp [textbook]⟩ : Fin textbook.length) ∉
    (solve textbook 50).ret.chosen := by decide
example : (⟨1, by simp [textbook]⟩ : Fin textbook.length) ∈
    (solve textbook 50).ret.chosen := by decide
example : (⟨2, by simp [textbook]⟩ : Fin textbook.length) ∈
    (solve textbook 50).ret.chosen := by decide
example : totalWeight textbook (solve textbook 50).ret.chosen = 50 := by decide
example : totalValue textbook (solve textbook 50).ret.chosen = 220 := by decide

private def duplicates : List Item :=
  [{ weight := 2, value := 5 }, { weight := 2, value := 5 }]

example : (solve duplicates 2).ret.value = 5 := by decide
example : (⟨0, by simp [duplicates]⟩ : Fin duplicates.length) ∈
    (solve duplicates 2).ret.chosen := by decide
example : (⟨1, by simp [duplicates]⟩ : Fin duplicates.length) ∉
    (solve duplicates 2).ret.chosen := by decide
example : (solve duplicates 4).ret.value = 10 := by decide
example : (⟨0, by simp [duplicates]⟩ : Fin duplicates.length) ∈
    (solve duplicates 4).ret.chosen := by decide
example : (⟨1, by simp [duplicates]⟩ : Fin duplicates.length) ∈
    (solve duplicates 4).ret.chosen := by decide

private def zeroWeight : List Item :=
  [{ weight := 0, value := 4 }, { weight := 0, value := 5 }]

example : (solve zeroWeight 0).ret.value = 9 := by decide
example : (⟨0, by simp [zeroWeight]⟩ : Fin zeroWeight.length) ∈
    (solve zeroWeight 0).ret.chosen := by decide
example : (⟨1, by simp [zeroWeight]⟩ : Fin zeroWeight.length) ∈
    (solve zeroWeight 0).ret.chosen := by decide

private def zeroValue : List Item :=
  [{ weight := 0, value := 0 }, { weight := 3, value := 0 }]

example : (solve zeroValue 3).ret.value = 0 := by decide
example : (solve zeroValue 3).ret.chosen = ∅ := by decide

example : (solve [] 0).time = 0 := by decide
example : (solve duplicates 0).time = 4 := by decide
example : (solve textbook 5).time = 21 := by decide

example (items : List Item) (capacity : Nat) :
    let result := (solve items capacity).ret
    Feasible items capacity result.chosen ∧
      result.value = totalValue items result.chosen ∧
      ∀ chosen : Finset (Fin items.length),
        Feasible items capacity chosen → totalValue items chosen ≤ result.value :=
  solve_correct items capacity

example (items : List Item) (capacity : Nat)
    (i : Fin items.length) (_hi : i ∈ (solve items capacity).ret.chosen) :
    i.val < items.length :=
  i.isLt

example (items : List Item) (capacity : Nat) :
    (solve items capacity).time = items.length * (capacity + 1) + items.length :=
  solve_time items capacity

example (items : List Item) (capacity : Nat) (hcapacity : 0 < capacity) :
    (solve items capacity).time ≤ 3 * (items.length * capacity) :=
  solve_time_le_three_mul items capacity hcapacity
