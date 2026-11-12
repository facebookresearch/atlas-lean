/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.LinearWaves
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Travelling-wave checks

Concrete consumers of `PhyslibExt.EarthScience.LinearWaves`: the wave
equation for a specific travelling wave, the zero-amplitude case, and the
zero-wavenumber (spatially constant) case.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. A specific travelling wave
- B. Degenerate cases

## iv. References

- `PhyslibExt.EarthScience.LinearWaves`
-/

/-- The wave `cos (2x - 6t)` (amplitude 1, `k = 2`, `c = 3`) solves
`u_tt = 9 u_xx` at `(t, x) = (0, 0)`. -/
example :
    deriv (fun t => deriv (fun t' => 1 * Real.cos (2 * 0 - 3 * 2 * t')) t) 0 =
      3 ^ 2 * deriv (fun x => deriv (fun x' => 1 * Real.cos (2 * x' - 3 * 2 * 0)) x) 0 :=
  EarthScience.wave_travelling_solves 1 2 3 0 0

/-- Zero amplitude: the second time derivative vanishes. -/
example (k c x t : ℝ) :
    deriv (fun t => deriv (fun t' => 0 * Real.cos (k * x - c * k * t')) t) t = 0 := by
  rw [EarthScience.wave_second_deriv_time]
  simp

/-- Zero wavenumber: the wave is spatially constant, so the second space
derivative vanishes. -/
example (A c x t : ℝ) :
    deriv (fun x => deriv (fun x' => A * Real.cos (0 * x' - c * 0 * t)) x) x = 0 := by
  rw [EarthScience.wave_second_deriv_space]
  simp

/-- Standing-wave node check: at `k x - c k t = π / 2` the wave value is
`0`, and the second time derivative formula gives `0` there too. -/
example (A k c : ℝ) :
    -(c * k) ^ 2 * (A * Real.cos (Real.pi / 2)) = 0 := by
  rw [Real.cos_pi_div_two]
  simp
