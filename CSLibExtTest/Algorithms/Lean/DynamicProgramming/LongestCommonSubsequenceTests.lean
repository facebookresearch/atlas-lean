/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.LongestCommonSubsequence

/-!
# Longest common subsequence tests

Concrete witnesses, occurrence multiplicity, empty boundaries, and transition counts.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.LongestCommonSubsequenceTests

universe u

open Cslib.Algorithms.Lean
open List

example : (longestCommonSubsequence ([] : List Nat) []).ret = (0, []) := by decide

example : (longestCommonSubsequence ([] : List Nat) []).time = 0 := by decide

example : (longestCommonSubsequence ([] : List Nat) [1, 2]).ret = (0, []) := by decide

example : (longestCommonSubsequence [1, 2] ([] : List Nat)).ret = (0, []) := by decide

example : (longestCommonSubsequence ([] : List Nat) [1, 2]).time = 0 := by decide

example : (longestCommonSubsequence [1, 2] ([] : List Nat)).time = 0 := by decide

example : (longestCommonSubsequence [1] [1]).ret = (1, [1]) := by decide

example : (longestCommonSubsequence [1] [1]).time = 2 := by decide

example : (longestCommonSubsequence [1] [2]).ret = (0, []) := by decide

example : (longestCommonSubsequence [1] [2]).time = 2 := by decide

example : (longestCommonSubsequence [1, 2] [3, 4]).ret = (0, []) := by decide

example : (longestCommonSubsequence [1, 2, 3] [1, 2, 3]).ret = (3, [1, 2, 3]) := by
  decide

example : (longestCommonSubsequence [1, 1, 1] [1, 1]).ret = (2, [1, 1]) := by decide

example : (longestCommonSubsequence [1, 2, 1, 2] [1, 1, 2, 2]).ret.1 = 3 := by decide

example : (longestCommonSubsequence [1, 2] [2, 1]).ret.1 = 1 := by decide

example :
    let result := (longestCommonSubsequence [1, 2] [2, 1]).ret
    result.2 <+ [1, 2] ∧ result.2 <+ [2, 1] ∧ result.2.length = 1 := by decide

example :
    (longestCommonSubsequence ['A', 'B', 'C', 'B', 'D', 'A', 'B']
      ['B', 'D', 'C', 'A', 'B', 'A']).ret.1 = 4 := by decide

example :
    let result := (longestCommonSubsequence ['A', 'B', 'C', 'B', 'D', 'A', 'B']
      ['B', 'D', 'C', 'A', 'B', 'A']).ret
    result.2.length = result.1 ∧
      result.2 <+ ['A', 'B', 'C', 'B', 'D', 'A', 'B'] ∧
      result.2 <+ ['B', 'D', 'C', 'A', 'B', 'A'] ∧
      (∀ zs, zs <+ ['A', 'B', 'C', 'B', 'D', 'A', 'B'] →
        zs <+ ['B', 'D', 'C', 'A', 'B', 'A'] → zs.length ≤ result.2.length) :=
  longestCommonSubsequence_correct _ _

example : (longestCommonSubsequence [1, 2, 3] [1, 2, 3]).time = 12 := by decide

example : (longestCommonSubsequence [1, 1, 1] [1, 1]).time = 8 := by decide

example : (longestCommonSubsequence [1, 2] [3, 4]).time = 6 := by decide

example : (longestCommonSubsequence [1, 2, 3] [1, 3]).time ≤ 6 + (3 + 2) :=
  longestCommonSubsequence_time _ _

example : (longestCommonSubsequence ([] : List Nat) []).time ≤ 0 :=
  longestCommonSubsequence_time _ _

example :
    (longestCommonSubsequence ['A', 'B', 'C', 'B', 'D', 'A', 'B']
      ['B', 'D', 'C', 'A', 'B', 'A']).time ≤ 7 * 6 + (7 + 6) :=
  longestCommonSubsequence_time _ _

example {α : Type u} [BEq α] [LawfulBEq α] (xs ys : List α) :
    let result := (longestCommonSubsequence xs ys).ret
    result.2.length = result.1 ∧ result.2 <+ xs ∧ result.2 <+ ys ∧
      (∀ zs, zs <+ xs → zs <+ ys → zs.length ≤ result.2.length) :=
  longestCommonSubsequence_correct xs ys

end Cslib.Algorithms.Lean.LongestCommonSubsequenceTests
