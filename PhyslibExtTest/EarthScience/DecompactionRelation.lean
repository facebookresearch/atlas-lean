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
φ0 = 2/5` (decompacted thickness `40/3`, solid volume `8`, both checked
by `norm_num`), the no-compaction boundary case `φ = φ0` where the
thickness is unchanged, and the zero-porosity boundary case `φ = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.DecompactionRelation`
-/

/-- Generic elaboration: the theorem applies to any `h ≥ 0` and
`0 ≤ φ ≤ φ0 < 1`. -/
example {h φ φ0 : ℝ} (hh : 0 ≤ h) (hφ' : 0 ≤ φ) (hφ : φ ≤ φ0) (hφ0 : φ0 < 1) :
    (h * (1 - φ) / (1 - φ0)) * (1 - φ0) = h * (1 - φ)
      ∧ h ≤ h * (1 - φ) / (1 - φ0) :=
  EarthScience.decompaction_relation hh hφ' hφ hφ0

/-- Numeric case: `h = 10, φ = 1/5, φ0 = 2/5` satisfies the hypotheses of
`decompaction_relation`, which gives solid-volume conservation and
`10 ≤ 10 * (1 - 1/5) / (1 - 2/5)`. -/
example : (10 * (1 - (1 / 5 : ℝ)) / (1 - (2 / 5 : ℝ))) * (1 - (2 / 5 : ℝ))
      = 10 * (1 - (1 / 5 : ℝ))
    ∧ (10 : ℝ) ≤ 10 * (1 - (1 / 5 : ℝ)) / (1 - (2 / 5 : ℝ)) :=
  EarthScience.decompaction_relation (h := (10 : ℝ)) (φ := (1 / 5 : ℝ)) (φ0 := (2 / 5 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Numeric values, computed independently of the theorem: for `h = 10, φ = 1/5,
φ0 = 2/5` the decompacted thickness is `40/3`, and both sides of the solid-volume
balance equal `8`. -/
example : 10 * (1 - (1 / 5 : ℝ)) / (1 - (2 / 5 : ℝ)) = 40 / 3
    ∧ (10 * (1 - (1 / 5 : ℝ)) / (1 - (2 / 5 : ℝ))) * (1 - (2 / 5 : ℝ)) = 8
    ∧ 10 * (1 - (1 / 5 : ℝ)) = 8 := by
  norm_num

/-- No-compaction boundary: with `φ = φ0` the decompacted thickness
equals `h`, by cancelling `1 - φ ≠ 0` in the conservation identity of
`decompaction_relation`. -/
example {h φ : ℝ} (hh : 0 ≤ h) (hφ' : 0 ≤ φ) (hφ : φ < 1) :
    h * (1 - φ) / (1 - φ) = h := by
  have hne : (1 : ℝ) - φ ≠ 0 := ne_of_gt (show (0 : ℝ) < 1 - φ by linarith)
  exact mul_right_cancel₀ hne (EarthScience.decompaction_relation hh hφ' le_rfl hφ).1

/-- Zero-porosity boundary: a layer with no present pore space (`φ = 0`)
decompacts to thickness `h / (1 - φ0)`, which conserves the solid volume `h`
and is at least `h`. -/
example {h φ0 : ℝ} (hh : 0 ≤ h) (hφ0' : 0 ≤ φ0) (hφ0 : φ0 < 1) :
    (h / (1 - φ0)) * (1 - φ0) = h ∧ h ≤ h / (1 - φ0) := by
  have key := EarthScience.decompaction_relation (φ := 0) hh le_rfl hφ0' hφ0
  simp only [sub_zero, mul_one] at key
  exact key
