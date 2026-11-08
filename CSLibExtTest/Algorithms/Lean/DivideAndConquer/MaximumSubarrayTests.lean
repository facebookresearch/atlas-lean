/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DivideAndConquer.MaximumSubarray
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Int
public meta import CSLibExt.Algorithms.Lean.DivideAndConquer.MaximumSubarray
public meta import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public meta import Mathlib.Data.Int.Order.Basic

/-!
# Divide-and-conquer maximum-subarray tests

Executed fixtures check the returned sum against the expected value and against Kadane's scan,
and the operation count against the recurrence, on the CLRS Figure 4.3 array, all-negative
inputs, restarts, a run that must cross the midpoint, odd and even lengths, and the empty list.
Closed examples check values through the agreement theorem and instantiate the cost theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private meta def checkInt (label : String) (xs : List Int) (expected : Option Int)
    (ops : Nat) : IO Unit := do
  let r := maxSubarraySumDC xs
  unless r.ret == expected && r.ret == (maxSubarraySum xs).ret && r.time == ops do
    throw (IO.userError s!"{label}: got {r.ret} with {r.time} ops")
  IO.println s!"{label}: {r.ret} (agrees with Kadane), {r.time} ops"

private meta def checkRat (label : String) (xs : List Rat) (expected : Option Rat)
    (ops : Nat) : IO Unit := do
  let r := maxSubarraySumDC xs
  unless r.ret == expected && r.ret == (maxSubarraySum xs).ret && r.time == ops do
    throw (IO.userError s!"{label}: got {r.ret} with {r.time} ops")
  IO.println s!"{label}: {r.ret} (agrees with Kadane), {r.time} ops"

/-- CLRS, third edition, Figure 4.3: the maximum run is `A[8..11] = 18, 20, -7, 12`. -/
private def clrsChanges : List Int :=
  [13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7]

#eval checkInt "empty" [] none 0
#eval checkInt "singleton negative" [-7] (some (-7)) 0
#eval checkInt "two elements" [3, -1] (some 3) 7
#eval checkInt "CLRS Figure 4.3" clrsChanges (some 43) 173
#eval checkInt "all negative keeps a nonempty run" [-8, -3, -6, -2, -5, -4] (some (-2)) 47
#eval checkInt "zeros and negatives" [-1, 0, -2] (some 0) 16
#eval checkInt "restart after a deep dip" [5, -10, 3, 4] (some 7) 25
#eval checkInt "whole list" [2, -1, 2, -1, 2] (some 4) 36
#eval checkInt "Bentley's example" [31, -41, 59, 26, -53, 58, 97, -93, -23, 84] (some 187) 95
#eval checkInt "crossing run wins" [-5, 4, 4, -5] (some 8) 25
#eval checkRat "fractions" [1 / 2, -1 / 3, 1 / 2, -2] (some (2 / 3)) 25

-- The divide-and-conquer recursion is well founded, so closed values go through the agreement
-- theorem with Kadane's structurally recursive scan.
example : (maxSubarraySumDC clrsChanges).ret = some 43 := by
  rw [maxSubarraySumDC_eq_maxSubarraySum]; decide
example : (maxSubarraySumDC ([-8, -3, -6, -2, -5, -4] : List Int)).ret = some (-2) := by
  rw [maxSubarraySumDC_eq_maxSubarraySum]; decide
example : (maxSubarraySumDC ([] : List Int)).ret = none := by
  rw [maxSubarraySumDC_eq_maxSubarraySum]; decide

universe u

example {α : Type u} [AddMonoid α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
    (xs : List α) (m : α) :
    (maxSubarraySumDC xs).ret = some m ↔ IsMaxSubarraySum xs m :=
  maxSubarraySumDC_ret_eq_some_iff xs m

example {α : Type u} [AddMonoid α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
    (xs : List α) : (maxSubarraySumDC xs).ret = (maxSubarraySum xs).ret :=
  maxSubarraySumDC_eq_maxSubarraySum xs

example {α : Type u} [AddMonoid α] [LinearOrder α] (xs : List α) (hxs : xs ≠ []) :
    (maxSubarraySumDC xs).time + 3 ≤ 2 * xs.length * Nat.clog 2 xs.length + 3 * xs.length :=
  maxSubarraySumDC_time_le xs hxs

#print axioms maxSubarraySumDC
#print axioms maxSubarraySumDC_ret_eq_some_iff
#print axioms maxSubarraySumDC_eq_maxSubarraySum
#print axioms maxSubarrayDC_time
#print axioms maxSubarraySumDC_time_le
#print axioms IsMaxSubarraySum.append

end Cslib.Algorithms.Lean.TimeM
