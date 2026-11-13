/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.DecompactionRelation

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Decompaction relation checks

Concrete consumers of `PhyslibExt.EarthScience.DecompactionRelation`:
a generic elaboration check, a numeric case `h = 10, φ = 1/5,
φ0 = 2/5` (decompacted thickness `40/3`, solid volume `8`), and the
no-compaction boundary case `φ = φ0` where the thickness is unchanged.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.DecompactionRelation`
-/

/-- Generic elaboration: the theorem applies to any `h ≥ 0` and
`φ ≤ φ0 < 1`. -/
example {h φ φ0 : ℝ} (hh : 0 ≤ h) (hφ : φ ≤ φ0) (hφ0 : φ0 < 1) :
    (h * (1 - φ) / (1 - φ0)) * (1 - φ0) = h * (1 - φ)
      ∧ h ≤ h * (1 - φ) / (1 - φ0) :=
  EarthScience.decompaction_relation hh hφ hφ0

/-- Numeric case: `h = 10, φ = 1/5, φ0 = 2/5` gives decompacted
thickness `40/3`, solid volume `8`, and `10 ≤ 40/3`. -/
example : (10 * (1 - (1 / 5 : ℝ)) / (1 - (2 / 5 : ℝ))) * (1 - (2 / 5 : ℝ))
      = 10 * (1 - (1 / 5 : ℝ))
    ∧ (10 : ℝ) ≤ 10 * (1 - (1 / 5 : ℝ)) / (1 - (2 / 5 : ℝ)) := by
  have h := EarthScience.decompaction_relation (h := (10 : ℝ))
    (φ := (1 / 5 : ℝ)) (φ0 := (2 / 5 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  exact h

/-- No-compaction boundary: with `φ = φ0` the decompacted thickness
equals `h`. -/
example {h φ : ℝ} (_hh : 0 ≤ h) (hφ : φ < 1) :
    h * (1 - φ) / (1 - φ) = h := by
  have hpos : (0 : ℝ) < 1 - φ := by linarith
  have hne : (1 : ℝ) - φ ≠ 0 := ne_of_gt hpos
  rw [mul_div_assoc, div_self hne, mul_one]
