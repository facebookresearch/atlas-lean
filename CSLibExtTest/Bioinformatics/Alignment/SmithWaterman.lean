/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.SmithWaterman
public meta import CSLibExt.Bioinformatics.Alignment.SmithWaterman

/-!
# Smith–Waterman table tests

Executed fixtures: the textbook example `TGTTACGG` / `GGTTGACTA` (match `+3`, mismatch `-3`,
gap `-2`; best local alignment `GTT-AC` / `GTTGAC`, score `13`); boundary cases (an empty
sequence, no positive local alignment, identical sequences); agreement of the table with the
exponential-time specifications `swScore` and `localScore` on all pairs of short DNA strings
over a two-letter alphabet. Each run throws on a disagreement.
-/

namespace Cslib.Bioinformatics.Alignment.SmithWaterman

open Cslib.Algorithms.Lean

/-- Match `+3`, mismatch `-3`. -/
def σ₀ (a b : Char) : ℤ := if a = b then 3 else -3

#guard swTab σ₀ (-2) "TGTTACGG".toList "GGTTGACTA".toList = 13
#guard swTab σ₀ (-2) [] "ACGT".toList = 0
#guard swTab σ₀ (-2) "AAAA".toList "CCC".toList = 0
#guard swTab σ₀ (-2) "ACGT".toList "ACGT".toList = 12

/-- All lists over `{A, C}` of length at most `n`. -/
def words : ℕ → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: (words n).flatMap fun w => ['A' :: w, 'C' :: w]

#guard (words 3).length = 15

#guard (words 3).all fun xs => (words 3).all fun ys =>
  swTab σ₀ (-2) xs ys == swScore σ₀ (-2) xs ys && swTab σ₀ (-2) xs ys == localScore σ₀ (-2) xs ys

-- The correctness theorems, instantiated.
example (xs ys : List Char) : swTab σ₀ (-2) xs ys = localScore σ₀ (-2) xs ys :=
  swTab_eq_localScore σ₀ (-2) (by decide) xs ys
example (xs ys : List Char) : swTab σ₀ 1 xs ys = swScore σ₀ 1 xs ys :=
  swTab_eq_swScore σ₀ 1 xs ys

end Cslib.Bioinformatics.Alignment.SmithWaterman
