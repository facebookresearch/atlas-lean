/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.NeedlemanWunschTable
public meta import CSLibExt.Bioinformatics.Alignment.NeedlemanWunschTable

/-!
# Needleman–Wunsch table tests

Executed fixtures: the example `GCATGCU` / `GATTACA` (match `+1`, mismatch `-1`, gap `-1`;
optimal score `0`); boundary cases (empty sequences, identical sequences, a positive gap score);
the last row of a small table; agreement of the table with the exponential-time specification
`nwScore` on all pairs of strings of length at most `3` over a two-letter alphabet, for three gap
scores. Each run throws on a disagreement.
-/

namespace Cslib.Bioinformatics.Alignment.NeedlemanWunsch

open Cslib.Algorithms.Lean

/-- Match `+1`, mismatch `-1`. -/
def σ₀ (a b : Char) : ℤ := if a = b then 1 else -1

#guard nwTab σ₀ (-1) "GCATGCU".toList "GATTACA".toList = 0
#guard nwTab σ₀ (-1) [] [] = 0
#guard nwTab σ₀ (-1) [] "ACGT".toList = -4
#guard nwTab σ₀ (-2) "ACG".toList [] = -6
#guard nwTab σ₀ (-1) "ACGT".toList "ACGT".toList = 4
-- A positive gap score rewards gaps: all `3 + 2` letters in gap columns.
#guard nwTab σ₀ 1 "ACG".toList "TT".toList = 5
-- The last row of the table for `AC` against `A`: `F[2][0] = -2`, `F[2][1] = 0`.
#guard nwRows σ₀ (-1) "AC".toList "A".toList = [-2, 0]

/-- All lists over `{A, C}` of length at most `n`. -/
def words : ℕ → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: (words n).flatMap fun w => ['A' :: w, 'C' :: w]

#guard (words 3).length = 15

#guard [-2, -1, 1].all fun g : ℤ => (words 3).all fun xs => (words 3).all fun ys =>
  nwTab σ₀ g xs ys == nwScore σ₀ g xs ys

-- The correctness theorem, instantiated.
example (xs ys : List Char) : nwTab σ₀ (-1) xs ys = nwScore σ₀ (-1) xs ys :=
  nwTab_eq_nwScore σ₀ (-1) xs ys

end Cslib.Bioinformatics.Alignment.NeedlemanWunsch
