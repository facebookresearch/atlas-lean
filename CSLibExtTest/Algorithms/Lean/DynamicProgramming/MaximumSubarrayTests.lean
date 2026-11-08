/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Int
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray
public meta import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public meta import Mathlib.Data.Int.Order.Basic

/-!
# Kadane maximum-subarray tests

Executed fixtures check the returned sum and the exact operation count, including the CLRS
Figure 4.3 stock-price-change array, all-negative inputs, ties, and the empty list. Closed
examples check the same values with `decide`; abstract examples exercise the public theorems.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private meta def checkInt (label : String) (xs : List Int) (expected : Option Int)
    (ops : Nat) : IO Unit := do
  let result := maxSubarraySum xs
  unless result.ret == expected && result.time == ops do
    throw (IO.userError s!"{label}: got {result.ret} with {result.time} ops")
  IO.println s!"{label}: {result.ret}, {result.time} ops"

private meta def checkRat (label : String) (xs : List Rat) (expected : Option Rat)
    (ops : Nat) : IO Unit := do
  let result := maxSubarraySum xs
  unless result.ret == expected && result.time == ops do
    throw (IO.userError s!"{label}: got {result.ret} with {result.time} ops")
  IO.println s!"{label}: {result.ret}, {result.time} ops"

/-- CLRS, third edition, Figure 4.3: the maximum run is `A[8..11] = 18, 20, -7, 12`. -/
private def clrsChanges : List Int :=
  [13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7]

#eval checkInt "empty" [] none 0
#eval checkInt "singleton negative" [-7] (some (-7)) 0
#eval checkInt "CLRS Figure 4.3" clrsChanges (some 43) 45
#eval checkInt "all negative keeps a nonempty run" [-8, -3, -6, -2, -5, -4] (some (-2)) 15
#eval checkInt "zeros and negatives" [-1, 0, -2] (some 0) 6
#eval checkInt "restart after a deep dip" [5, -10, 3, 4] (some 7) 9
#eval checkInt "whole list" [2, -1, 2, -1, 2] (some 4) 12
#eval checkInt "Bentley's example" [31, -41, 59, 26, -53, 58, 97, -93, -23, 84] (some 187) 27
#eval checkRat "fractions" [1 / 2, -1 / 3, 1 / 2, -2] (some (2 / 3)) 9

example : (maxSubarraySum clrsChanges).ret = some 43 := by decide
example : (maxSubarraySum ([-8, -3, -6, -2, -5, -4] : List Int)).ret = some (-2) := by decide
example : (maxSubarraySum ([] : List Int)).ret = none := by decide
example : (maxSubarraySum ([5, -10, 3, 4] : List Int)).ret = some 7 := by decide

/-- The CLRS answer is attained by the run `A[8..11]`. -/
example : ([18, 20, -7, 12] : List Int) <:+: clrsChanges ∧
    ([18, 20, -7, 12] : List Int).sum = 43 := by decide

universe u

example {α : Type u} [AddMonoid α] [LinearOrder α] [AddRightMono α] (xs : List α) (m : α) :
    (maxSubarraySum xs).ret = some m ↔ IsMaxSubarraySum xs m :=
  maxSubarraySum_ret_eq_some_iff xs m

example {α : Type u} [AddMonoid α] [LinearOrder α] (xs : List α) :
    (maxSubarraySum xs).ret = none ↔ xs = [] :=
  maxSubarraySum_ret_eq_none_iff xs

example {α : Type u} [AddMonoid α] [LinearOrder α] (xs : List α) :
    (maxSubarraySum xs).time = 3 * (xs.length - 1) := by simp

example {α : Type u} [AddMonoid α] [LinearOrder α] [AddRightMono α] (xs ys : List α) (m : α)
    (hm : (maxSubarraySum xs).ret = some m) (hys : ys <:+: xs) (hne : ys ≠ []) :
    ys.sum ≤ m :=
  sum_le_of_maxSubarraySum hm hys hne

/-- The spec rules out the empty-run answer `0` for an all-negative input. -/
example : ¬ IsMaxSubarraySum ([-3, -1] : List Int) 0 := fun h =>
  absurd (h.unique ((maxSubarraySum_ret_eq_some_iff _ _).1
    (by decide : (maxSubarraySum ([-3, -1] : List Int)).ret = some (-1)))) (by decide)

#print axioms maxSubarraySum
#print axioms maxSubarraySum_time
#print axioms maxSubarraySum_ret_eq_some_iff
#print axioms maxSubarraySum_ret_eq_none_iff
#print axioms sum_le_of_maxSubarraySum
#print axioms exists_sum_eq_of_maxSubarraySum
#print axioms IsMaxSubarraySum.unique

end Cslib.Algorithms.Lean.TimeM
