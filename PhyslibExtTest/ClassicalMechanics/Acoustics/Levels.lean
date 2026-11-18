/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.ClassicalMechanics.Acoustics.Levels

/-!
# Intensity level checks

Focused checks for `PhyslibExt.ClassicalMechanics.Acoustics.Levels`:
equal intensities give zero level difference, and doubling intensity
(two equal sources) gives `10 * log10 2`.

These are elaboration and non-vacuity checks, not new results.
-/

open Acoustics

/-- Zero difference at equal intensities, through the public theorem. -/
example : intensityLevel 1 2 - intensityLevel 1 2 = intensityLevelDifference 2 2 :=
  intensityLevel_sub_eq (by norm_num) (by norm_num) (by norm_num)

/-- Two equal sources, through the public theorem. -/
example : intensityLevelDifference 1 (∑ _i ∈ Finset.range 2, (1 : ℝ))
    = 10 * Real.logb 10 (2 : ℝ) :=
  intensityLevelDifference_equal_sources (by norm_num) (by norm_num) rfl
