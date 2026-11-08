/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Selection.MedianOfMedians
public meta import CSLibExt.Algorithms.Lean.Selection.MedianOfMedians
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Cslib.Algorithms.Lean.Sort.Insertion

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

example : (medianOfMedians ([] : List Nat) 0).ret = none := by decide
example : (medianOfMedians [7] 0).ret = some 7 := by decide
example : (medianOfMedians [7] 1).ret = none := by decide
example : (medianOfMedians [3, 1, 4, 2] 1).ret = some 2 := by decide
example : (medianOfMedians [3, 1, 4, 2] 2).ret = some 3 := by decide
example : (medianOfMedians [7, 7, 7, 7] 2).ret = some 7 := by decide

example (xs : List Nat) (k : Nat) :
    (medianOfMedians xs k).ret = (xs.insertionSort (· ≤ ·))[k]? :=
  medianOfMedians_eq_getElem?_insertionSort xs k

example (xs : List Nat) (k : Nat) :
    (medianOfMedians xs k).time ≤ 80 * xs.length := medianOfMedians_time xs k

example {xs : List Nat} {k : Nat} {x : Nat} (hnodup : xs.Nodup)
    (hresult : (medianOfMedians xs k).ret = some x) :
    (xs.toFinset.filter (fun y => y ≤ x)).card = k + 1 :=
  medianOfMedians_set_rank hnodup hresult

-- Higher-universe ordered inputs must support the complete public selector API.
example {α : Type 1} [LinearOrder α] (xs : List α) (k : Nat) :
    (medianOfMedians xs k).ret = (xs.insertionSort (· ≤ ·))[k]? :=
  medianOfMedians_eq_getElem?_insertionSort xs k

example {α : Type 1} [LinearOrder α] (xs : List α) (k : Nat) :
    (medianOfMedians xs k).time ≤ 80 * xs.length := medianOfMedians_time xs k

example {α : Type 1} [LinearOrder α] (xs : List α) :
    (medianOfMediansGroups xs).time ≤ 2 * xs.length := medianOfMediansGroups_time xs

example {α : Type 1} [LinearOrder α] (xs : List α) :
    (insertionSort xs).time ≤ xs.length * (xs.length - 1) / 2 := insertionSort_time xs

/-- Execute the recursive selector and fail elaboration if its value or charges change. -/
private def checkSelection (xs : List Nat) (k : Nat) (expected : Option Nat) (cost : Nat) :
    IO (Option Nat × Nat × Bool) := do
  let actual := medianOfMedians xs k
  unless actual.ret == expected do throw (IO.userError "Unexpected selected value")
  unless actual.time == cost do throw (IO.userError "Unexpected comparison charges")
  unless actual.time ≤ 80 * xs.length do throw (IO.userError "Comparison bound exceeded")
  pure (actual.ret, actual.time, true)

#eval checkSelection [] 0 none 0
#eval checkSelection [3, 1, 2] 1 (some 2) 3
#eval checkSelection ((List.range 501).reverse) 0 (some 0) 14742
#eval checkSelection ((List.range 501).reverse) 250 (some 250) 14680
#eval checkSelection ((List.range 501).reverse) 500 (some 500) 7180
#eval checkSelection (List.replicate 501 7) 250 (some 7) 1001
#eval checkSelection (List.range 140) 139 (some 139) 9730
#eval checkSelection (List.range 141) 140 (some 140) 2846
#eval checkSelection (List.range 141) 141 none 0

#eval show IO (List Nat) from do
  let actual := medianOfMediansGroups [5, 4, 3, 2, 1, 9]
  unless actual.ret == [3, 9] do throw (IO.userError "Unexpected full or partial group median")
  pure actual.ret

end Cslib.Algorithms.Lean.TimeM
