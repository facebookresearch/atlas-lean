/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.RadiometricAgeFromRatio

import Mathlib.Tactic.NormNum

/-!
# Radiometric age from ratio checks

Concrete consumers of `PhyslibExt.EarthScience.RadiometricAgeFromRatio`:
a generic elaboration check, the zero-age boundary case `t = 0`,
nonnegativity of the recovered age, and the domain of the ratio
(nonnegative for `t ≥ 0`, zero at `t = 0`).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.RadiometricAgeFromRatio`
-/

/-- Generic elaboration: the theorem applies to any `λ > 0`,
`P0 > 0`, and `t ≥ 0`. -/
example {lam P0 t : ℝ} (hlam : 0 < lam) (hP0 : 0 < P0) (ht : 0 ≤ t) :
    Real.log (1 + (P0 - P0 * Real.exp (-lam * t))
        / (P0 * Real.exp (-lam * t))) / lam = t :=
  EarthScience.radiometric_age_from_ratio hlam hP0 ht

/-- Zero-age boundary: at `t = 0` the daughter is `0`, the ratio is
`0`, and the recovered age is `0`. -/
example {lam P0 : ℝ} (hlam : 0 < lam) (hP0 : 0 < P0) :
    Real.log (1 + (P0 - P0 * Real.exp (-lam * (0 : ℝ)))
        / (P0 * Real.exp (-lam * (0 : ℝ)))) / lam = 0 :=
  EarthScience.radiometric_age_from_ratio hlam hP0 (le_refl 0)

/-- Nonnegativity: the recovered age equals `t ≥ 0`. -/
example {lam P0 t : ℝ} (hlam : 0 < lam) (hP0 : 0 < P0) (ht : 0 ≤ t) :
    0 ≤ Real.log (1 + (P0 - P0 * Real.exp (-lam * t))
        / (P0 * Real.exp (-lam * t))) / lam := by
  rw [EarthScience.radiometric_age_from_ratio hlam hP0 ht]
  exact ht

/-- Domain of the ratio: for `t ≥ 0` the daughter/parent ratio is nonnegative, not
necessarily positive. -/
example {lam P0 t : ℝ} (hlam : 0 < lam) (hP0 : 0 < P0) (ht : 0 ≤ t) :
    0 ≤ (P0 - P0 * Real.exp (-lam * t)) / (P0 * Real.exp (-lam * t)) := by
  have hE : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  apply div_nonneg
  · nlinarith
  · positivity

/-- At `t = 0` the daughter/parent ratio is exactly `0`. -/
example {lam P0 : ℝ} :
    (P0 - P0 * Real.exp (-lam * (0 : ℝ))) / (P0 * Real.exp (-lam * (0 : ℝ))) = 0 := by
  simp
