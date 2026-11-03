/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Indexing.SuffixArrayBWT
public meta import CSLibExt.Bioinformatics.Indexing.SuffixArrayBWT
public import Mathlib.Data.Char
public meta import Mathlib.Data.Char

/-!
# Suffix array and Burrows–Wheeler transform bridge tests

Executed fixtures on `banana`: the suffix array of `banana$` equals the sorted rotation order;
the transform read off the suffix array; the occurrences of several patterns reported from the
backward-search interval against a naive scan; the LF step in suffix-array terms; locate with
every second text position sampled (correct on every row, at most one LF step), and the junk
value of locate when the row of position `0` is not sampled (the hypothesis of `locate_eq`
fails). Also pseudo-random texts over a three-letter alphabet. Each run throws on a
disagreement.
-/

namespace Cslib.Bioinformatics.Indexing.SuffixArrayBWT

open Cslib.Algorithms.Lean.SuffixArray Cslib.Bioinformatics.Indexing.BWT

/-- `banana`. -/
def banana : List Char := "banana".toList

#guard suffixArray (withSentinel banana) = [6, 5, 3, 1, 0, 4, 2]
#guard sortedRotations banana = suffixArray (withSentinel banana)
#guard bwt banana = (suffixArray (withSentinel banana)).map
  fun i => (withSentinel banana).getD ((i + 6) % 7) ⊥

-- `ana` occurs at positions 3 and 1 (rows 2 and 3 of the suffix array).
#guard occurrences banana "ana".toList = [3, 1]
#guard occurrences banana "x".toList = []
#guard occurrences banana "".toList = [6, 5, 3, 1, 0, 4, 2]

/-- The naive list of occurrences, in increasing order. -/
def naiveOcc (t P : List Char) : List ℕ :=
  (List.range (t.length + 1)).filter fun i => P <+: t.drop i

#guard ["ana", "a", "na", "ban", "", "x", "banana", "nab", "n"].all fun p =>
  (occurrences banana p.toList).mergeSort (· ≤ ·) == naiveOcc banana p.toList

-- `SA[r] = SA[LF r] + 1` when `SA[r] > 0`, and `SA[LF r] = 6` for the row of position `0`.
#guard (List.range 7).all fun r =>
  let SA := suffixArray (withSentinel banana)
  SA.getD (lf (bwt banana) r) 0 == (SA.getD r 0 + 6) % 7

/-- Samples at the even text positions of `banana`. -/
def evenSample (r : ℕ) : Option ℕ :=
  let v := (suffixArray (withSentinel banana)).getD r 0
  if r < 7 ∧ v % 2 = 0 then some v else none

#guard (List.range 7).all fun r =>
  locate (bwt banana) evenSample r == (suffixArray (withSentinel banana)).getD r 0
#guard (List.range 7).all fun r => locateSteps (bwt banana) evenSample 7 r ≤ 1

-- Junk value outside the hypotheses of `locate_eq`: with no samples at all, locate walks its
-- whole fuel and returns `7` instead of the position.
#guard locate (bwt banana) (fun _ => none) 0 = 7

/-- A pseudo-random text of length `n` over `{0, 1, 2}`. -/
def randText (seed n : ℕ) : List ℕ :=
  (List.range n).map fun i => (seed * 7 + i * i * 13 + i) % 3

#guard (List.range 20).all fun k =>
  sortedRotations (randText k k) == suffixArray (withSentinel (randText k k))

end Cslib.Bioinformatics.Indexing.SuffixArrayBWT
