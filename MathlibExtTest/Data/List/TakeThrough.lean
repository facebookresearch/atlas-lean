/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Data.List.TakeThrough

@[expose] public section

open List

variable {α : Type*}

example (p : α → Bool) (xs : List α) :
    takeThrough p xs = xs.take (xs.findIdx p + 1) := rfl

example : takeThrough (fun x : Nat => decide (3 ≤ x)) [] = [] := by decide
example : takeThrough (fun x : Nat => decide (3 ≤ x)) [3, 4] = [3] := by decide
example : takeThrough (fun x : Nat => decide (3 ≤ x)) [1, 2, 3, 4] = [1, 2, 3] := by decide
example : takeThrough (fun x : Nat => decide (5 ≤ x)) [1, 2, 3, 4] = [1, 2, 3, 4] := by decide
example : takeThrough (fun x : Nat => decide (3 ≤ x)) [3] = [3] := by decide
example : takeThrough (fun x : Nat => decide (3 ≤ x)) [2] = [2] := by decide

example :
    takeThrough (fun x : Nat => decide (3 ≤ x)) ([1, 3] ++ [4, 5]) = [1, 3] := by
  rw [takeThrough_append_of_any_eq_true (by decide)]
  decide

example :
    takeThrough (fun x : Nat => decide (3 ≤ x)) ([1, 2] ++ [3, 4]) = [1, 2, 3] := by
  rw [takeThrough_append_of_any_eq_false (by decide)]
  decide

example : takeThrough (fun x : Nat => x == 0) (range 4) = range 1 := by decide
example : takeThrough (fun x : Nat => x == 2) (range 5) = range 3 := by decide
example : takeThrough (fun x : Nat => x == 5) (range 5) = range 5 := by decide

private def selectOdd (x : Nat) : Option Nat :=
  if x % 2 = 1 then some x else none

example :
    (takeThrough (fun x => (selectOdd x).any fun y => decide (3 ≤ y)) [0, 1, 2, 3, 4, 5]).filterMap
        selectOdd = [1, 3] := by
  decide

example :
    (takeThrough (fun x => (selectOdd x).any fun y => decide (3 ≤ y)) [0, 1, 2, 3, 4, 5]).filterMap
        selectOdd =
      takeThrough (fun y => decide (3 ≤ y)) ([0, 1, 2, 3, 4, 5].filterMap selectOdd) :=
  filterMap_takeThrough selectOdd (fun y => decide (3 ≤ y)) _

example (p : α → Bool) : takeThrough p [] = [] := takeThrough_nil p

example (p : α → Bool) (x : α) (xs : List α) (h : p x = true) :
    takeThrough p (x :: xs) = [x] := takeThrough_cons_of_pos h xs

example (p : α → Bool) (x : α) (xs : List α) (h : p x = false) :
    takeThrough p (x :: xs) = x :: takeThrough p xs := takeThrough_cons_of_neg h xs

example (p : α → Bool) (x : α) : takeThrough p [x] = [x] := takeThrough_singleton p x

example (p : α → Bool) (xs : List α) (x : α) (h : x ∈ takeThrough p xs) : x ∈ xs :=
  mem_of_mem_takeThrough h

example (p : α → Bool) (xs : List α) (h : xs.any p = false) : takeThrough p xs = xs :=
  takeThrough_eq_self_of_any_eq_false h

example (p : α → Bool) (xs : List α) : (takeThrough p xs).any p = xs.any p :=
  any_takeThrough p xs

example (q : Nat → Bool) (n : Nat) :
    takeThrough q (range n) =
      range (match (range n).find? q with | some i => i + 1 | none => n) :=
  takeThrough_range q n

#print axioms List.takeThrough
#print axioms List.takeThrough_nil
#print axioms List.takeThrough_cons_of_pos
#print axioms List.takeThrough_cons_of_neg
#print axioms List.takeThrough_singleton
#print axioms List.mem_of_mem_takeThrough
#print axioms List.takeThrough_eq_self_of_any_eq_false
#print axioms List.takeThrough_append_of_any_eq_true
#print axioms List.takeThrough_append_of_any_eq_false
#print axioms List.any_takeThrough
#print axioms List.takeThrough_range
#print axioms List.filterMap_takeThrough
