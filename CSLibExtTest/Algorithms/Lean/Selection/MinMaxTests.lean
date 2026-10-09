/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Selection.MinMax
public meta import CSLibExt.Algorithms.Lean.Selection.MinMax
public meta import Cslib.Algorithms.Lean.TimeM
import Mathlib.Algebra.Order.Ring.Rat
public meta import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-! Executed fixtures for the paired extrema algorithm, including its comparison count. -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private meta def verifyInt (label : String) (xs : List Int)
    (expected : Option (Int × Int)) (comparisons : Nat) : IO Unit := do
  let result := minMax xs
  if result.ret != expected || result.time != comparisons then
    throw (IO.userError s!"{label}: got {result.ret} with {result.time} comparisons")
  IO.println s!"{label}: {result.ret}, {result.time} comparisons"

private meta def verifyRat (label : String) (xs : List Rat)
    (expected : Option (Rat × Rat)) (comparisons : Nat) : IO Unit := do
  let result := minMax xs
  if result.ret != expected || result.time != comparisons then
    throw (IO.userError s!"{label}: got {result.ret} with {result.time} comparisons")
  IO.println s!"{label}: {result.ret}, {result.time} comparisons"

#eval verifyInt "empty" [] none 0
#eval verifyInt "singleton signed" [-7] (some (-7, -7)) 0
#eval verifyInt "initial pair ascending" [-3, 8] (some (-3, 8)) 1
#eval verifyInt "initial pair reversed" [8, -3] (some (-3, 8)) 1
#eval verifyInt "initial pair tied" [4, 4] (some (4, 4)) 1
#eval verifyInt "odd both updates" [0, -4, 9] (some (-4, 9)) 3
#eval verifyInt "odd ties" [2, 2, 2] (some (2, 2)) 3
#eval verifyInt "even pair reversals" [4, -2, 8, -5] (some (-5, 8)) 4
#eval verifyInt "odd ascending" [1, 2, 3, 4, 5] (some (1, 5)) 6
#eval verifyInt "even decreasing" [6, 5, 4, 3, 2, 1] (some (1, 6)) 7
#eval verifyRat "fractions and signs" [1 / 2, -3 / 2, 7 / 4, 0] (some (-3 / 2, 7 / 4)) 4
#eval verifyInt "mixed updates" [0, -1, 5, -10, -2] (some (-10, 5)) 6

universe u

example {α : Type u} [LinearOrder α] (xs : List α) :
    (minMax xs).ret = xs.min?.bind (fun lo => xs.max?.map (fun hi => (lo, hi))) :=
  minMax_ret xs

example {α : Type u} [LinearOrder α] (xs : List α) :
    (minMax xs).ret = none ↔ xs = [] := minMax_eq_none_iff xs

example {α : Type u} [LinearOrder α] (xs : List α) (lo hi : α) :
    (minMax xs).ret = some (lo, hi) ↔
      lo ∈ xs ∧ hi ∈ xs ∧ (∀ x ∈ xs, lo ≤ x) ∧ (∀ x ∈ xs, x ≤ hi) :=
  minMax_eq_some_iff xs lo hi

example {α : Type u} [LinearOrder α] :
    minMax ([] : List α) = pure none := minMax_nil

example {α : Type u} [LinearOrder α] (a : α) :
    minMax [a] = pure (some (a, a)) := minMax_singleton a

example {α : Type u} [LinearOrder α] (xs : List α) (k : Nat)
    (h : xs.length = 2 * k + 1) : (minMax xs).time = 3 * k :=
  minMax_time_odd xs k h

example {α : Type u} [LinearOrder α] (xs : List α) (k : Nat)
    (h : xs.length = 2 * k) (hk : 1 ≤ k) : (minMax xs).time = 3 * k - 2 :=
  minMax_time_even xs k h hk

example {α : Type u} [LinearOrder α] (xs : List α) :
    (minMax xs).time =
      if xs.length = 0 then 0 else ((3 * xs.length + 1) / 2) - 2 := minMax_time xs

end Cslib.Algorithms.Lean.TimeM
