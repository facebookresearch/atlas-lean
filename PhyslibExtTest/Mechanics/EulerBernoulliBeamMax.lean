/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.EulerBernoulliBeamMax

/-!
# Beam midpoint-maximum checks

Focused checks for `PhyslibExt.Mechanics.EulerBernoulliBeamMax`:
the numeric midpoint value (5 for L = 4, EI = 2, w = 3), the
midpoint bound at an interior point, and the zero-load case.

These are elaboration and non-vacuity checks, not new results.
-/

open Mechanics.EulerBernoulli

/-- Midpoint value: `5 * 3 * 4 ^ 4 / (384 * 2) = 5`. -/
example : uniformLoadDeflection 3 2 4 (4 / 2 : ℝ) = 5 := by
  rw [uniformLoadDeflection_midpoint]
  norm_num

/-- The midpoint bound at an interior point. -/
example : uniformLoadDeflection 3 2 4 1
    ≤ uniformLoadDeflection 3 2 4 (4 / 2 : ℝ) :=
  uniformLoadDeflection_le_midpoint (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- Zero load: the deflection is identically zero, so the midpoint
bound holds with equality everywhere. -/
example : uniformLoadDeflection 0 2 4 1
    = uniformLoadDeflection 0 2 4 (4 / 2 : ℝ) := by
  simp [uniformLoadDeflection]
