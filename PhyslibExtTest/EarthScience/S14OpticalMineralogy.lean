/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.S14OpticalMineralogy

/-!
# Phase-retardation checks

Concrete consumers of `PhyslibExt.EarthScience.S14OpticalMineralogy`:
zero thickness, equal indices, and the `δ = π` example.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Vanishing retardation
- B. Non-vacuous example

## iv. References

- `PhyslibExt.EarthScience.S14OpticalMineralogy`
-/

/-- Zero thickness: `h = 0` gives `δ = 0`. -/
example : 2 * Real.pi * ((3 / 2 : ℝ) - 1) * 0 / 1 = 0 :=
  EarthScience.phaseRetardation_zero_thickness (by norm_num)

/-- Equal indices: `n₁ = n₂ = 3 / 2` gives `δ = 0` at `h = 2`. -/
example : 2 * Real.pi * ((3 / 2 : ℝ) - (3 / 2)) * 2 / 1 = 0 :=
  EarthScience.phaseRetardation_equal_indices (by norm_num)

/-- Non-vacuous example: `n₁ = 3 / 2, n₂ = 1, h = 1, lam = 1` gives `δ = π`. -/
example : 2 * Real.pi * ((3 / 2 : ℝ) - 1) * 1 / 1 = Real.pi :=
  EarthScience.phaseRetardation_example
