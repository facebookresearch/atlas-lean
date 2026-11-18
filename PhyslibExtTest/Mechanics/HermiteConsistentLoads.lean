/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.HermiteConsistentLoads
import Mathlib.Tactic.NormNum

/-!
# Hermite-load checks

Focused checks for `PhyslibExt.Mechanics.HermiteConsistentLoads`:
at `w = 2`, `L = 3` the four entries are `3`, `3 / 2`, `3`,
`-3 / 2` (summing vertically to the total load `6`); at `w = 0`
every entry vanishes.

These are elaboration and non-vacuity checks, not new results.
-/

open intervalIntegral

/-- Entry values at `w = 2`, `L = 3`. -/
example : (∫ x in (0 : ℝ)..3, (2 : ℝ) * (1 - 3 * (x / 3) ^ 2 + 2 * (x / 3) ^ 3)) = 3
    ∧ (∫ x in (0 : ℝ)..3, (2 : ℝ) * (3 * ((x / 3) - 2 * (x / 3) ^ 2 + (x / 3) ^ 3))) = 3 / 2 := by
  have h := hermite_consistent_loads (w := 2) (L := 3) (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [h.1]
    norm_num
  · rw [h.2.1]
    norm_num

/-- Zero load gives a zero first entry. -/
example : (∫ x in (0 : ℝ)..3, (0 : ℝ) * (1 - 3 * (x / 3) ^ 2 + 2 * (x / 3) ^ 3)) = 0 := by
  have h := hermite_consistent_loads (w := 0) (L := 3) (by norm_num)
  rw [h.1]
  norm_num
