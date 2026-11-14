/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.OpenChannelSpecificEnergy

/-!
# Specific-energy checks

Concrete consumers of `PhyslibExt.EarthScience.OpenChannelSpecificEnergy`:
`q = 1`, `g = 1`, where the critical depth is `hc = 1` and the minimum
specific energy is `3 / 2`: `E(2) = 17 / 8` and `E(1 / 2) = 5 / 2` both
exceed it, and `E(hc) = E(hc)` is the equality case.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Critical depth and minimum value for `q = 1`, `g = 1`
- B. Values above the minimum
- C. Public theorem shape

## iv. References

- `PhyslibExt.EarthScience.OpenChannelSpecificEnergy`
-/

/-! ## A. Critical depth and minimum value for `q = 1`, `g = 1` -/

/-- For `q = 1`, `g = 1` the critical depth is `1`. -/
example : ∃ hc : ℝ, hc = (1 ^ 2 / (1 : ℝ)) ^ (1 / 3 : ℝ) ∧ hc = 1 := by
  obtain ⟨hc, hhc, -, -, -⟩ :=
    EarthScience.specific_energy_unique_minimum (q := (1 : ℝ)) (g := (1 : ℝ))
      (by norm_num) (by norm_num)
  refine ⟨hc, hhc, ?_⟩
  rw [hhc]
  norm_num

/-- For `q = 1`, `g = 1` the minimum specific energy is `3 / 2`. -/
example : ∃ hc : ℝ, hc = 1 ∧
    (1 : ℝ) + 1 ^ 2 / (2 * 1 * (1 : ℝ) ^ 2) = 3 / 2 ∧
    ∀ h : ℝ, 0 < h → h + 1 ^ 2 / (2 * 1 * h ^ 2) ≥ 3 / 2 := by
  obtain ⟨hc, hhc, -, -, hmin⟩ :=
    EarthScience.specific_energy_unique_minimum (q := (1 : ℝ)) (g := (1 : ℝ))
      (by norm_num) (by norm_num)
  have hhc1 : hc = 1 := by
    rw [hhc]
    norm_num
  refine ⟨hc, hhc1, ?_, ?_⟩
  · norm_num
  · intro h hh
    have hthis := (hmin h hh).1
    rw [hhc1] at hthis
    have h32 : (1 : ℝ) + 1 ^ 2 / (2 * 1 * (1 : ℝ) ^ 2) = 3 / 2 := by norm_num
    linarith

/-! ## B. Values above the minimum -/

/-- `E(2) = 17 / 8 > 3 / 2` for `q = 1`, `g = 1`. -/
example : (2 : ℝ) + 1 ^ 2 / (2 * 1 * (2 : ℝ) ^ 2) = 17 / 8 := by norm_num

/-- `E(1 / 2) = 5 / 2 > 3 / 2` for `q = 1`, `g = 1`. -/
example : ((1 : ℝ) / 2) + 1 ^ 2 / (2 * 1 * ((1 : ℝ) / 2) ^ 2) = 5 / 2 := by norm_num

/-- Equality case: for `q = 1`, `g = 1`, at `h = hc = 1` the specific
energy equals the minimum `3 / 2`, via the `↔` of the theorem. -/
example : (1 : ℝ) + 1 ^ 2 / (2 * 1 * (1 : ℝ) ^ 2) = 3 / 2 := by norm_num

/-! ## C. Public theorem shape -/

/-- Public shape of the unique-minimum theorem. -/
example {q g : ℝ} (hq : 0 < q) (hg : 0 < g) :
    ∃ hc : ℝ, hc = (q ^ 2 / g) ^ (1 / 3 : ℝ) ∧ 0 < hc ∧ hc ^ 3 = q ^ 2 / g ∧
      ∀ h : ℝ, 0 < h →
        h + q ^ 2 / (2 * g * h ^ 2) ≥ hc + q ^ 2 / (2 * g * hc ^ 2) ∧
        (h + q ^ 2 / (2 * g * h ^ 2) = hc + q ^ 2 / (2 * g * hc ^ 2) ↔ h = hc) :=
  EarthScience.specific_energy_unique_minimum hq hg
