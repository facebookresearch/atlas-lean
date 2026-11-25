/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtSmallPartCounts

open MetaMathlibExt

private abbrev totalFour (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), arndtCompositionCount (fun i => i ≤ 4) n k

-- Check the empty composition, the first pair, and the loss of the singleton at weight five.
example : totalFour 0 = 1 ∧ totalFour 3 = 2 ∧ totalFour 4 = 3 ∧ totalFour 5 = 4 := by
  decide

-- At weight six a pair can leave a nonempty paired tail; at weight seven the pair (4, 3) fits.
example : arndtCompositionCount (fun i => i ≤ 4) 6 4 = 1 ∧
    arndtCompositionCount (fun i => i ≤ 4) 7 2 = 1 := by
  decide

-- Test the theorem against numerical values on both sides of the last pair-weight threshold.
example : totalFour 6 = 6 ∧ totalFour 7 = 9 ∧ totalFour 8 = 13 := by
  exact ⟨(sum_arndtCompositionCount_le_four 6).trans (by decide),
    (sum_arndtCompositionCount_le_four 7).trans (by decide),
    (sum_arndtCompositionCount_le_four 8).trans (by decide)⟩

-- The totals satisfy the short Narayana recurrence, starting at weight three.
example (n : ℕ) : totalFour (n + 3) = totalFour (n + 2) + totalFour n := by
  simp only [totalFour, sum_arndtCompositionCount_le_four]
  rfl
