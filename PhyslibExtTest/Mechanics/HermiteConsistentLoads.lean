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
`-3 / 2` (summing vertically to the total load `6`); the same
values come from the canonical `HermiteCubic.hermite` basis; at
`w = 0` every entry vanishes.

These are elaboration and non-vacuity checks, not new results.
-/

open intervalIntegral

/-- All four entry values at `w = 2`, `L = 3`. -/
example : (∫ x in (0 : ℝ)..3, (2 : ℝ) * (1 - 3 * (x / 3) ^ 2 + 2 * (x / 3) ^ 3)) = 3
    ∧ (∫ x in (0 : ℝ)..3, (2 : ℝ) * (3 * ((x / 3) - 2 * (x / 3) ^ 2 + (x / 3) ^ 3))) = 3 / 2
    ∧ (∫ x in (0 : ℝ)..3, (2 : ℝ) * (3 * (x / 3) ^ 2 - 2 * (x / 3) ^ 3)) = 3
    ∧ (∫ x in (0 : ℝ)..3, (2 : ℝ) * (3 * (-(x / 3) ^ 2 + (x / 3) ^ 3))) = -3 / 2 := by
  have h := HermiteCubic.hermite_consistent_loads (w := 2) (L := 3) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.1]
    norm_num
  · rw [h.2.1]
    norm_num
  · rw [h.2.2.1]
    norm_num
  · rw [h.2.2.2]
    norm_num

/-- The canonical-basis theorem gives the same four values. -/
example : (∫ x in (0 : ℝ)..3, (2 : ℝ) * HermiteCubic.hermite 3 1 0 0 0 x) = 3
    ∧ (∫ x in (0 : ℝ)..3, (2 : ℝ) * HermiteCubic.hermite 3 0 1 0 0 x) = 3 / 2
    ∧ (∫ x in (0 : ℝ)..3, (2 : ℝ) * HermiteCubic.hermite 3 0 0 1 0 x) = 3
    ∧ (∫ x in (0 : ℝ)..3, (2 : ℝ) * HermiteCubic.hermite 3 0 0 0 1 x) = -3 / 2 := by
  have h := HermiteCubic.hermite_consistent_loads_hermite (w := 2) (L := 3)
    (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.1]
    norm_num
  · rw [h.2.1]
    norm_num
  · rw [h.2.2.1]
    norm_num
  · rw [h.2.2.2]
    norm_num

/-- Zero load gives zero entries throughout. -/
example : (∫ x in (0 : ℝ)..3, (0 : ℝ) * (1 - 3 * (x / 3) ^ 2 + 2 * (x / 3) ^ 3)) = 0
    ∧ (∫ x in (0 : ℝ)..3, (0 : ℝ) * (3 * ((x / 3) - 2 * (x / 3) ^ 2 + (x / 3) ^ 3))) = 0
    ∧ (∫ x in (0 : ℝ)..3, (0 : ℝ) * (3 * (x / 3) ^ 2 - 2 * (x / 3) ^ 3)) = 0
    ∧ (∫ x in (0 : ℝ)..3, (0 : ℝ) * (3 * (-(x / 3) ^ 2 + (x / 3) ^ 3))) = 0 := by
  have h := HermiteCubic.hermite_consistent_loads (w := 0) (L := 3) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.1]
    norm_num
  · rw [h.2.1]
    norm_num
  · rw [h.2.2.1]
    norm_num
  · rw [h.2.2.2]
    norm_num
