/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.GotohTable
public meta import CSLibExt.Bioinformatics.Alignment.GotohTable

/-!
# Gotoh table tests

Executed fixtures: `AAAA` / `AA` (match `+2`, mismatch `-1`, gap open `-3`, gap extend `-1`), where
one gap run of length `2` (score `4 - 3 - 1 = 0`) beats two separate gaps (`4 - 3 - 3 = -2`);
boundary cases (empty sequences: a single gap run); agreement of the table with the
exponential-time specification `gotohScore` on all pairs of strings of length at most `3` over a
two-letter alphabet for several gap parameters (including `gapOpen > gapExtend` and positive
scores); agreement with `nwScore` when `gapOpen = gapExtend`. Each run throws on a
disagreement.
-/

namespace Cslib.Bioinformatics.Alignment.Gotoh

open Cslib.Algorithms.Lean

/-- Match `+2`, mismatch `-1`. -/
def σ₀ (a b : Char) : ℤ := if a = b then 2 else -1

#guard gotohTab σ₀ (-3) (-1) "AAAA".toList "AA".toList = 0
#guard gotohScore σ₀ (-3) (-1) "AAAA".toList "AA".toList = 0
-- With linear gaps `-3` the two gap columns cost `-6`.
#guard gotohTab σ₀ (-3) (-3) "AAAA".toList "AA".toList = -2
#guard gotohTab σ₀ (-3) (-1) [] [] = 0
-- Against the empty sequence: one gap run of length 4, `-3 - 1 - 1 - 1`.
#guard gotohTab σ₀ (-3) (-1) [] "ACGT".toList = -6
#guard gotohTab σ₀ (-3) (-1) "ACG".toList [] = -5

/-- All lists over `{A, C}` of length at most `n`. -/
def words : ℕ → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: (words n).flatMap fun w => ['A' :: w, 'C' :: w]

#guard [((-3 : ℤ), (-1 : ℤ)), (-1, -3), (-2, -2), (1, -1), (0, 2)].all fun (o, e) =>
  (words 3).all fun xs => (words 3).all fun ys =>
    gotohTab σ₀ o e xs ys == gotohScore σ₀ o e xs ys

#guard [(-2 : ℤ), -1, 1].all fun g => (words 3).all fun xs => (words 3).all fun ys =>
  gotohTab σ₀ g g xs ys == nwScore σ₀ g xs ys

-- The correctness theorems, instantiated.
example (xs ys : List Char) : gotohTab σ₀ (-3) (-1) xs ys = gotohScore σ₀ (-3) (-1) xs ys :=
  gotohTab_eq_gotohScore σ₀ (-3) (-1) xs ys
example (xs ys : List Char) : gotohTab σ₀ (-2) (-2) xs ys = nwScore σ₀ (-2) xs ys :=
  gotohTab_eq_nwScore σ₀ (-2) (-2) (-2) rfl rfl xs ys

end Cslib.Bioinformatics.Alignment.Gotoh
