/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.OpticalMineralogy

/-!
# Phase-retardation checks

Concrete consumers of `PhyslibExt.EarthScience.OpticalMineralogy`:
the explicit formula, zero thickness, equal indices, the `δ = π`
example, and the sign flip when the two modes are swapped.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Formula and vanishing retardation
- B. Non-vacuous example and sign convention

## iv. References

- `PhyslibExt.EarthScience.OpticalMineralogy`
-/

/-! ## A. Formula and vanishing retardation -/

/-- Explicit formula: `n₁ = 3 / 2, n₂ = 1, h = 2, lam = 1 / 2`. -/
example : EarthScience.phaseRetardation (3 / 2) 1 2 (1 / 2) =
    2 * Real.pi * ((3 / 2 : ℝ) - 1) * 2 / (1 / 2) :=
  EarthScience.phaseRetardation_eq _ _ _ _

/-- Zero thickness: `h = 0` gives `δ = 0`. -/
example : EarthScience.phaseRetardation (3 / 2) 1 0 1 = 0 :=
  EarthScience.phaseRetardation_zero_thickness _ _ _

/-- Equal indices: `n₁ = n₂ = 3 / 2` gives `δ = 0` at `h = 2`. -/
example : EarthScience.phaseRetardation (3 / 2) (3 / 2) 2 1 = 0 :=
  EarthScience.phaseRetardation_equal_indices _ _ _

/-! ## B. Non-vacuous example and sign convention -/

/-- Non-vacuous example: `n₁ = 3 / 2, n₂ = 1, h = 1, lam = 1` gives `δ = π`. -/
example : EarthScience.phaseRetardation (3 / 2) 1 1 1 = Real.pi :=
  EarthScience.phaseRetardation_example

/-- Signed convention: swapping the modes (`n₁ = 1 < n₂ = 3 / 2`) gives `δ = -π`. -/
example : EarthScience.phaseRetardation 1 (3 / 2) 1 1 = -Real.pi := by
  rw [EarthScience.phaseRetardation_eq]
  norm_num
  ring
