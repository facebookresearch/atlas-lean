/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.AlignmentBridges
import all CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm

/-!
# Alignment bridge tests

Closed checks on ten inputs: `kitten`/`sitting`, an empty first list, an empty second list,
`flaw`/`lawn`, the CLRS pair `abcbdab`/`bdcaba`, `aaaa`/`aa`, two empty lists, the unequal
singletons `7`/`8`, the identical pair `252`/`252`, and the swapped pair `25`/`52`. Each `decide`
evaluates the tabulated edit distance, the Needleman–Wunsch score with substitution score
`if a == b then 0 else -1` and gap `-1`, the tabulated LCS length, and the Needleman–Wunsch score
with substitution score `if a == b then 1 else 0` and gap `0`. Generic checks instantiate both
bridges at `Char` and in an arbitrary universe, and use one bridge to read an LCS length off a
Needleman–Wunsch score.
-/

namespace Cslib.Algorithms.Lean.AlignmentBridgesTests

universe v

open Cslib.Algorithms.Lean

/-- The four values the bridges relate on one input: edit distance, the edit-scored
Needleman–Wunsch score, LCS length, and the LCS-scored Needleman–Wunsch score. -/
def bridgeRow (xs ys : List Char) : ℕ × ℤ × ℕ × ℤ :=
  ((editDistance xs ys).ret.distance,
    nwScore (fun a b => if a == b then 0 else -1) (-1) xs ys,
    (longestCommonSubsequence xs ys).ret.1,
    nwScore (fun a b => if a == b then 1 else 0) 0 xs ys)

/-! Closed checks -/

example : bridgeRow "kitten".toList "sitting".toList = (3, -3, 4, 4) := by decide

example : bridgeRow "".toList "abc".toList = (3, -3, 0, 0) := by decide

example : bridgeRow "abc".toList "".toList = (3, -3, 0, 0) := by decide

example : bridgeRow "flaw".toList "lawn".toList = (2, -2, 3, 3) := by decide

example : bridgeRow "abcbdab".toList "bdcaba".toList = (5, -5, 4, 4) := by decide

example : bridgeRow "aaaa".toList "aa".toList = (2, -2, 2, 2) := by decide

example : bridgeRow [] [] = (0, 0, 0, 0) := by decide

example : bridgeRow "7".toList "8".toList = (1, -1, 0, 0) := by decide

example : bridgeRow "252".toList "252".toList = (0, 0, 3, 3) := by decide

example : bridgeRow "25".toList "52".toList = (2, -2, 1, 1) := by decide

/-! Generic checks -/

example (xs ys : List Char) :
    ((editDistance xs ys).ret.distance : ℤ) =
      -nwScore (fun a b => if a == b then 0 else -1) (-1) xs ys :=
  editDistance_distance_eq_neg_nwScore xs ys

example (xs ys : List Char) :
    ((longestCommonSubsequence xs ys).ret.1 : ℤ) =
      nwScore (fun a b => if a == b then 1 else 0) 0 xs ys :=
  longestCommonSubsequence_length_eq_nwScore xs ys

example {β : Type v} [BEq β] [LawfulBEq β] (xs ys : List β) :
    ((editDistance xs ys).ret.distance : ℤ) =
      -nwScore (fun a b => if a == b then 0 else -1) (-1) xs ys :=
  editDistance_distance_eq_neg_nwScore xs ys

example {β : Type v} [BEq β] [LawfulBEq β] (xs ys : List β) :
    ((longestCommonSubsequence xs ys).ret.1 : ℤ) =
      nwScore (fun a b => if a == b then 1 else 0) 0 xs ys :=
  longestCommonSubsequence_length_eq_nwScore xs ys

-- The bridge reads the tabulated LCS length off the Needleman–Wunsch specification.
example : (longestCommonSubsequence "abcbdab".toList "bdcaba".toList).ret.1 = 4 := by
  have h := longestCommonSubsequence_length_eq_nwScore "abcbdab".toList "bdcaba".toList
  have hnw : nwScore (fun a b => if a == b then 1 else 0) 0
      "abcbdab".toList "bdcaba".toList = 4 := by decide
  omega

#print axioms editDistance_distance_eq_neg_nwScore
#print axioms longestCommonSubsequence_length_eq_nwScore

end Cslib.Algorithms.Lean.AlignmentBridgesTests
