/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Bioinformatics.Assembly.LanderWatermanIslands

/-! Finite checks of the island, isolated-read, gap and linear-genome counts. -/

namespace CSLibExtTest.Bioinformatics.Assembly.LanderWatermanIslands

open Cslib.Bioinformatics.Assembly.LanderWaterman

/-- Two reads, a circle of five positions, window `V = 1`: `5 * (4 ^ 2 - 3 ^ 2) = 35`. -/
example : ∑ p : Fin 5, (Finset.univ.filter fun s : Fin 2 → Fin 5 => EndsRun 1 s p).card = 35 := by
  decide +kernel

/-- No reads: no run ends. -/
example : ∑ p : Fin 5, (Finset.univ.filter fun s : Fin 0 → Fin 5 => EndsRun 1 s p).card = 0 := by
  decide +kernel

/-- Reads at `0` and `2` on `Fin 5` with `V = 1`: both positions end a run. -/
example : EndsRun 1 (![0, 2] : Fin 2 → Fin 5) 0 ∧ EndsRun 1 (![0, 2] : Fin 2 → Fin 5) 2 := by
  decide

/-- Reads at `0` and `1` with `V = 1`: position `0` does not end a run. -/
example : ¬ EndsRun 1 (![0, 1] : Fin 2 → Fin 5) 0 := by decide

/-- Two reads at the same position are not isolated. -/
example : ¬ IsolatedRead 1 (![3, 3] : Fin 2 → Fin 6) 3 := by decide

/-- `6 * 2 * (6 - 3) ^ 1 = 36` isolated-read pairs for `G = 6`, `N = 2`, `W = 1`. -/
example : ∑ p : Fin 6, (Finset.univ.filter fun s : Fin 2 → Fin 6 =>
    IsolatedRead 1 s p).card = 36 := by
  decide +kernel

/-- Gaps of length at least `1` for `G = 6`, `N = 2`, `L = 2`: `6 * (4 ^ 2 - 3 ^ 2) = 42`. -/
example : ∑ x : Fin 6, (Finset.univ.filter fun s : Fin 2 → Fin 6 =>
    GapAtLeast 2 1 s x).card = 42 := by
  decide +kernel

/-- Linear genome `G = 8`, `L = 3`: the ends are covered by one start, the interior by three. -/
example : (Finset.univ.filter fun s : Fin (8 - 3 + 1) => s.val ≤ 0 ∧ 0 < s.val + 3).card = 1 := by
  decide

example : (Finset.univ.filter fun s : Fin (8 - 3 + 1) => s.val ≤ 4 ∧ 4 < s.val + 3).card = 3 := by
  decide

example : (Finset.univ.filter fun s : Fin (8 - 3 + 1) => s.val ≤ 7 ∧ 7 < s.val + 3).card = 1 := by
  decide

/-- A fully connected circle (`G = 4`, every gap at most `W = 1`): one island, no end position. -/
example : ∀ p, ¬ EndsRun 1 (![0, 1, 2, 3] : Fin 4 → Fin 4) p := by decide

/-- Two-piece overlap (`G = 6`, `L = 5`, `T = 4`, `W = 1`): reads at `0` and `3` share four bases
in two pieces, yet both positions end a run, so the window reads as detection only when
`2 * L ≤ G + 1`. -/
example : EndsRun 1 (![0, 3] : Fin 2 → Fin 6) 0 ∧ EndsRun 1 (![0, 3] : Fin 2 → Fin 6) 3 := by
  decide

/-- No reads: the uncovered circle has no gap mark. -/
example : ∀ x, ¬ GapAtLeast 2 1 (![] : Fin 0 → Fin 6) x := by decide

/-- One read of length `2` at `0` on `Fin 6`: the gap `2, …, 5` is marked once, at `5`, for every
`m ≤ 4`, and not for `m = 5`. -/
example : (∀ m ∈ [1, 2, 3, 4], GapAtLeast 2 m (![0] : Fin 1 → Fin 6) 5) ∧
    ¬ GapAtLeast 2 5 (![0] : Fin 1 → Fin 6) 5 ∧
    ∀ x : Fin 6, x ≠ 5 → ¬ GapAtLeast 2 1 (![0] : Fin 1 → Fin 6) x := by
  decide

/-- Duplicate starts: one end position, no isolated read. -/
example : EndsRun 1 (![3, 3] : Fin 2 → Fin 6) 3 ∧ ¬ IsolatedRead 1 (![3, 3] : Fin 2 → Fin 6) 3 := by
  decide

end CSLibExtTest.Bioinformatics.Assembly.LanderWatermanIslands
