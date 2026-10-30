/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Indexing.BWT
public meta import CSLibExt.Bioinformatics.Indexing.BWT
public import Mathlib.Data.Char
public meta import Mathlib.Data.Char

/-!
# Burrows–Wheeler transform and FM-index backward search tests

Executed fixtures: the transform of `banana` (`annb$aa`, with `$` the sentinel); inversion of
`banana`, of the empty text, of a one-letter text and of 40 pseudo-random texts over a
three-letter alphabet; the LF-mapping property row by row on `banana`; the transform of a
two-letter text; backward-search intervals and occurrence counts on `banana` (including the
empty pattern, an absent letter, the whole text, and the overlapping occurrences of `ana`)
against a naive count, and the row-interval characterization on all rows for several patterns.
Each run throws on a disagreement.
-/

namespace Cslib.Bioinformatics.Indexing.BWT

/-- `banana`. -/
def banana : List Char := "banana".toList

-- `banana$` sorts as `$banana, a$banan, ana$ban, anana$b, banana$, na$bana, nana$ba`.
#guard bwt banana = [↑'a', ↑'n', ↑'n', ↑'b', (⊥ : WithBot Char), ↑'a', ↑'a']
#guard sortedRotations banana = [6, 5, 3, 1, 0, 4, 2]
#guard invert (bwt banana) = banana.map (↑)
#guard invert (bwt ([] : List Char)) = []
#guard invert (bwt ['x']) = [(('x' : Char) : WithBot Char)]

-- `21$` sorts as `$21, 1$2, 21$`.
#guard bwt [2, 1] = [((1 : ℕ) : WithBot ℕ), ((2 : ℕ) : WithBot ℕ), ⊥]

-- The LF-mapping property, row by row.
#guard (List.range 7).all fun r =>
  (sortedRotations banana).getD (lf (bwt banana) r) 0 =
    ((sortedRotations banana).getD r 0 + 6) % 7

/-- A pseudo-random text of length `n` over `{0, 1, 2}`. -/
def randText (seed n : ℕ) : List ℕ :=
  (List.range n).map fun i => (seed * 7 + i * i * 13 + i) % 3

#guard (List.range 40).all fun k => invert (bwt (randText k k)) == (randText k k).map (↑)

/-! ## FM-index backward search -/

/-- The naive occurrence count. -/
def naiveCount (t P : List Char) : ℕ :=
  (List.range (t.length + 1)).countP fun i => P <+: t.drop i

#guard ["ana", "a", "na", "ban", "", "x", "banana", "nab"].all fun p =>
  let P := p.toList
  (backwardSearch (bwt banana) P).2 - (backwardSearch (bwt banana) P).1 = naiveCount banana P

-- `ana` occurs twice (overlapping), in rows `2` and `3`.
#guard backwardSearch (bwt banana) "ana".toList = (2, 4)

-- Backward search makes one recursive call per pattern letter: a 64-letter pattern finishes
-- (two recursive calls per letter would take 2^64 steps).
#guard
  let t := List.replicate 64 'a'
  (backwardSearch (bwt t) t).2 - (backwardSearch (bwt t) t).1 = 1

-- The interval is exactly the set of rows whose rotation starts with the pattern.
#guard ["ana", "a", "n", "", "x"].all fun p =>
  let P := p.toList
  (List.range 7).all fun r =>
    (decide ((backwardSearch (bwt banana) P).1 ≤ r ∧ r < (backwardSearch (bwt banana) P).2)) ==
      decide (P.map (↑) <+: (withSentinel banana).rotate ((sortedRotations banana).getD r 0))

end Cslib.Bioinformatics.Indexing.BWT
