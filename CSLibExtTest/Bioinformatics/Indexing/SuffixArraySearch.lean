/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Indexing.SuffixArraySearch
public meta import CSLibExt.Bioinformatics.Indexing.SuffixArraySearch
public import Mathlib.Data.Char
public meta import Mathlib.Data.Char

/-!
# Suffix-array search tests

Executed fixtures on `banana` (suffix array `[5, 3, 1, 0, 4, 2]`): the row intervals of several
patterns (including the empty pattern, an absent pattern, a pattern longer than the text and the
overlapping occurrences of `ana`) against a naive scan of the rows; the probe count of binary
search against `⌊log₂ n⌋ + 1`; pseudo-random texts over a three-letter alphabet. Each run throws
on a disagreement.
-/

namespace Cslib.Bioinformatics.Indexing.SuffixArraySearch

open Cslib.Algorithms.Lean.SuffixArray

/-- `banana`. -/
def banana : List Char := "banana".toList

#guard suffixArray banana = [5, 3, 1, 0, 4, 2]
-- `ana` starts the suffixes of rows 1 (`ana`) and 2 (`anana`).
#guard saSearch banana "ana".toList = (1, 3)
#guard saSearch banana "".toList = (0, 6)
#guard saSearch banana "x".toList = (6, 6)
#guard saSearch banana "bananas".toList = (4, 4)

/-- The naive membership test of row `r` in the occurrence interval. -/
def naiveRow (s P : List Char) (r : ℕ) : Bool :=
  decide (P <+: suffix s ((suffixArray s).getD r 0))

#guard ["ana", "a", "na", "ban", "", "x", "banana", "nab", "n", "bananas"].all fun p =>
  (List.range 6).all fun r =>
    decide ((saSearch banana p.toList).1 ≤ r ∧ r < (saSearch banana p.toList).2) ==
      naiveRow banana p.toList r

-- Binary search probes at most `⌊log₂ n⌋ + 1` times.
#guard (List.range 70).all fun n => (List.range (n + 1)).all fun k =>
  lowerBoundSteps (fun i => decide (i < k)) 0 n ≤ Nat.log 2 n + 1
#guard (List.range 70).all fun n => (List.range (n + 1)).all fun k =>
  lowerBound (fun i => decide (i < k)) 0 n == k

/-- A pseudo-random text of length `n` over `{0, 1, 2}`. -/
def randText (seed n : ℕ) : List ℕ :=
  (List.range n).map fun i => (seed * 7 + i * i * 13 + i) % 3

#guard (List.range 15).all fun k => [[0], [1, 2], [2, 2, 0], []].all fun P =>
  let s := randText k (k + 3)
  (List.range s.length).all fun r =>
    decide ((saSearch s P).1 ≤ r ∧ r < (saSearch s P).2) ==
      decide (P <+: suffix s ((suffixArray s).getD r 0))

end Cslib.Bioinformatics.Indexing.SuffixArraySearch
