/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Bioinformatics.Alignment.Traceback

/-! Tests for the Needleman–Wunsch and Smith–Waterman tracebacks. -/

namespace CSLibExtTest.Bioinformatics.Alignment.Traceback

open Cslib.Algorithms.Lean Cslib.Bioinformatics.Alignment.Traceback

/-- Match `2`, mismatch `-1`. -/
def s (a b : ℕ) : ℤ := if a = b then 2 else -1

example : nwTraceback s (-1) [1, 2, 3] [1, 3] =
    [(some 1, some 1), (some 2, none), (some 3, some 3)] := by
  decide +kernel

example : alignmentScore s (-1) (nwTraceback s (-1) [1, 2, 3] [1, 3]) = 3 := by decide +kernel

example : nwTraceback s (-1) [] [1, 3] = [(none, some 1), (none, some 3)] := by decide +kernel

example : nwTraceback s (-1) [1, 2] [] = [(some 1, none), (some 2, none)] := by decide +kernel

example : nwTraceback s (-1) ([] : List ℕ) [] = [] := by decide +kernel

example : swTraceback s (-1) [5, 1, 2, 3, 6] [7, 1, 3, 8] =
    ((1, 4), (1, 3), [(some 1, some 1), (some 2, none), (some 3, some 3)]) := by decide +kernel

/-- No positive local alignment: the empty alignment of two empty infixes. -/
example : swTraceback s (-1) [5, 6] [7, 8] = ((0, 0), (0, 0), []) := by decide +kernel

/-- A positive gap: the traceback still attains `swTab = 3`, which is below the local optimum. -/
example : swTraceback s 1 [5, 6] [7, 8] =
    ((0, 2), (1, 2), [(some 5, none), (none, some 8), (some 6, none)]) := by
  decide +kernel

example : Cslib.Bioinformatics.Alignment.SmithWaterman.swTab s 1 [5, 6] [7, 8] = 3 := by
  decide +kernel

example : localScore s 1 [5, 6] [7, 8] = 4 := by decide +kernel

/-- `argmaxCell` returns a real entry even when row `0` is empty, and `(0, 0)` only for a table
with no entry. -/
example : argmaxCell [[], [-1]] = (1, 0) := by decide +kernel

example : argmaxCell [[], [0]] = (1, 0) := by decide +kernel

example : argmaxCell [] = (0, 0) := by decide +kernel

example : argmaxCell [[], []] = (0, 0) := by decide +kernel

/-- Ties keep the first largest entry. -/
example : argmaxCell [[-2, -1], [-1]] = (0, 1) := by decide +kernel

end CSLibExtTest.Bioinformatics.Alignment.Traceback
