/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.PatienceSorting
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.PatienceSorting

/-!
# Patience-sorting tests

Executed fixtures compare the computed length with the expected value and with the quadratic
dynamic program's subsequence, and check the comparison count against `n * ⌈log₂ (n + 1)⌉`, on
duplicates (increasing is strict), sorted and reverse-sorted inputs, the empty list, and a
sequence where a later small element must replace a tail. Closed examples instantiate the
specification and the agreement theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private meta def check (label : String) (xs : List ℕ) (expected : ℕ) : IO Unit := do
  let r := patienceLength xs
  let quad := (longestIncreasingSubsequence xs).ret.length
  let bound := xs.length * Nat.clog 2 (xs.length + 1)
  unless r.ret == expected && r.ret == quad && r.time ≤ bound do
    throw (IO.userError s!"{label}: got {r.ret} (quadratic {quad}), {r.time} comparisons")
  IO.println s!"{label}: {r.ret} (quadratic DP agrees), {r.time} ≤ {bound} comparisons"

#eval check "empty" [] 0
#eval check "single" [7] 1
#eval check "classic" [10, 9, 2, 5, 3, 7, 101, 18] 4
#eval check "duplicates count once (strict)" [2, 2, 2, 2] 1
#eval check "sorted" [1, 2, 3, 4, 5, 6, 7, 8] 8
#eval check "reverse sorted" [8, 7, 6, 5, 4, 3, 2, 1] 1
#eval check "late small elements replace tails" [3, 4, 5, 1, 2, 3, 4] 4
#eval check "van der Corput sequence (16 terms)"
  [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15] 6

example : IsLISLength [3, 4, 5, 1, 2, 3, 4] (patienceLength [3, 4, 5, 1, 2, 3, 4]).ret :=
  patienceLength_spec _

example (xs : List ℤ) :
    (patienceLength xs).ret = (longestIncreasingSubsequence xs).ret.length :=
  patienceLength_eq_length_longestIncreasingSubsequence xs

example (xs : List ℤ) :
    (patienceLength xs).time ≤ xs.length * Nat.clog 2 (xs.length + 1) :=
  patienceLength_time_le xs

#print axioms patienceLength
#print axioms patienceLength_spec
#print axioms patienceLength_eq_length_longestIncreasingSubsequence
#print axioms patienceLength_time_le
#print axioms PatienceInv.scan

end Cslib.Algorithms.Lean.TimeM
