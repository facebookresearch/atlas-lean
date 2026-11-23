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
equation for a specific travelling wave, the shared plane-wave model with
`omega = c * k`, the zero-amplitude case, the zero-wavenumber (spatially
constant) case, and a zero crossing of the travelling wave.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. A specific travelling wave
- B. Degenerate cases and a zero crossing

## iv. References

- `PhyslibExt.EarthScience.LinearWaves`
-/

open PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves (planeWave)

/-- The wave `cos (2x - 6t)` (amplitude 1, `k = 2`, `c = 3`) solves
`u_tt = 9 u_xx` at `(t, x) = (0, 0)`. -/
example :
    deriv (fun t => deriv (fun t' => planeWave 1 2 (3 * 2) 0 t') t) 0 =
      3 ^ 2 * deriv (fun x => deriv (fun x' => planeWave 1 2 (3 * 2) x' 0) x) 0 :=
  EarthScience.wave_travelling_solves 1 2 3 0 0

/-- The shared plane-wave model `planeWave E0 k omega` solves the wave equation
whenever `omega = c * k`. -/
example (E0 k c omega x t : ℝ) (hω : omega = c * k) :
    deriv (fun t => deriv (fun t' => planeWave E0 k omega x t') t) t =
      c ^ 2 * deriv (fun x => deriv (fun x' => planeWave E0 k omega x' t) x) x := by
  subst hω
  exact EarthScience.wave_travelling_solves E0 k c x t

/-- Zero amplitude: the second time derivative vanishes. -/
example (k c x t : ℝ) :
    deriv (fun t => deriv (fun t' => planeWave 0 k (c * k) x t') t) t = 0 := by
  rw [EarthScience.wave_second_deriv_time]
  simp [planeWave]

/-- Zero wavenumber: the wave is spatially constant, so the second space
derivative vanishes. -/
example (A c x t : ℝ) :
    deriv (fun x => deriv (fun x' => planeWave A 0 (c * 0) x' t) x) x = 0 := by
  rw [EarthScience.wave_second_deriv_space]
  simp

/-- Zero crossing of the travelling wave: with `k = c = 1`, at `x = π / 2`
and `t = 0` the phase `k x - c k t` is `π / 2`, the wave value is `0`, and
so is its second time derivative. This zero moves with the wave; it is not
a standing-wave node. -/
example (A : ℝ) :
    deriv (fun t => deriv (fun t' => planeWave A 1 (1 * 1) (Real.pi / 2) t') t) 0 = 0 := by
  rw [EarthScience.wave_second_deriv_time]
  simp [planeWave]
