/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.LongestIncreasingSubsequence
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Int
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.LongestIncreasingSubsequence
public meta import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public meta import Mathlib.Data.Int.Order.Basic

/-!
# Longest increasing subsequence tests

Executed fixtures check the returned subsequence (that it is a strictly increasing subsequence of
the input, and its length) and the exact `n * (n + 1) / 2` inspection count on the standard
examples, ties (strictness), monotone inputs, rationals, and the empty list. Closed examples
check values with `decide` and the strictness boundary through the specification.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open scoped List

private meta def checkInt (label : String) (xs : List Int) (expected cost : Nat) : IO Unit := do
  let result := longestIncreasingSubsequence xs
  let ys := result.ret
  unless ys.length == expected && result.time == cost && ys.isSublist xs &&
      decide (ys.Pairwise (· < ·)) do
    throw (IO.userError s!"{label}: got {ys} with cost {result.time}")
  IO.println s!"{label}: {ys} (length {ys.length}), cost {result.time}"

private meta def checkRat (label : String) (xs : List Rat) (expected cost : Nat) : IO Unit := do
  let result := longestIncreasingSubsequence xs
  let ys := result.ret
  unless ys.length == expected && result.time == cost && ys.isSublist xs &&
      decide (ys.Pairwise (· < ·)) do
    throw (IO.userError s!"{label}: got {ys} with cost {result.time}")
  IO.println s!"{label}: {ys} (length {ys.length}), cost {result.time}"

/-- The van der Corput-style sequence from the standard LIS example; its LIS length is `6`. -/
private def binarySequence : List Int := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]

#eval checkInt "empty" [] 0 0
#eval checkInt "singleton" [42] 1 1
#eval checkInt "classic" [10, 9, 2, 5, 3, 7, 101, 18] 4 36
#eval checkInt "binary sequence" binarySequence 6 136
#eval checkInt "all equal is strict" [5, 5, 5, 5] 1 10
#eval checkInt "strictly decreasing" [5, 4, 3, 2, 1] 1 15
#eval checkInt "strictly increasing" [-3, -1, 0, 2, 7] 5 15
#eval checkInt "ties inside a run" [1, 2, 2, 3] 3 10
#eval checkInt "late start wins" [9, 10, 1, 2, 3] 3 15
#eval checkRat "fractions" [1 / 2, 1 / 3, 2 / 3, 3 / 4] 3 10

example : (longestIncreasingSubsequence ([10, 9, 2, 5, 3, 7, 101, 18] : List Int)).ret =
    [2, 3, 7, 18] := by decide
example : (longestIncreasingSubsequence ([5, 5, 5] : List Int)).ret = [5] := by decide
example : (longestIncreasingSubsequence ([] : List Int)).ret = [] := by decide

/-- Strictness: `[5, 5]` is a subsequence of `[5, 5]` but not increasing, so the length is `1`. -/
example : IsLISLength ([5, 5] : List Int) 1 :=
  (length_longestIncreasingSubsequence_eq_iff _ 1).1 (by decide)

example : ¬ IsLISLength ([5, 5] : List Int) 2 := fun h =>
  absurd ((length_longestIncreasingSubsequence_eq_iff _ 2).2 h) (by decide)

example {α : Type} [Preorder α] [DecidableLT α] (xs : List α) :
    (longestIncreasingSubsequence xs).ret <+ xs ∧
      (longestIncreasingSubsequence xs).ret.Pairwise (· < ·) ∧
      ∀ ys, ys <+ xs → ys.Pairwise (· < ·) →
        ys.length ≤ (longestIncreasingSubsequence xs).ret.length :=
  longestIncreasingSubsequence_spec xs

example {α : Type} [Preorder α] [DecidableLT α] (xs : List α) (k : ℕ) :
    (longestIncreasingSubsequence xs).ret.length = k ↔ IsLISLength xs k :=
  length_longestIncreasingSubsequence_eq_iff xs k

example {α : Type} [Preorder α] [DecidableLT α] (xs : List α) :
    2 * (longestIncreasingSubsequence xs).time = xs.length * (xs.length + 1) :=
  longestIncreasingSubsequence_time xs

#print axioms longestIncreasingSubsequence
#print axioms longestIncreasingSubsequence_time
#print axioms longestIncreasingSubsequence_spec
#print axioms length_longestIncreasingSubsequence_eq_iff
#print axioms isLISLength_longestIncreasingSubsequence
#print axioms IsLISLength.unique

end Cslib.Algorithms.Lean.TimeM
