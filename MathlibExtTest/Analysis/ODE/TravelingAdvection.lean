/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.ODE.TravelingAdvection

import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Traveling-profile advection checks

Concrete consumers of `MathlibExt.Analysis.ODE.TravelingAdvection`:
the sine profile at a numeric point, a cubic profile at a numeric
point (with derivative `3 * s ^ 2`), and the degenerate zero-speed
boundary case `c = 0`, where the profile is static in time.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Sine profile at a numeric point
- B. Cubic profile at a numeric point
- C. Zero speed

## iv. References

- `MathlibExt.Analysis.ODE.TravelingAdvection`
-/

/-- Sine profile at `c = 2, t = 0.3, x = 1.1`: `u_t = -2 cos 0.5`,
`u_x = cos 0.5`, residual `0`. -/
example :
    deriv (fun t => Real.sin ((1.1 : ℝ) - 2 * t)) (0.3 : ℝ)
      + 2 * deriv (fun x => Real.sin (x - 2 * (0.3 : ℝ))) (1.1 : ℝ) = 0 :=
  EarthScience.sine_traveling_profile_solves_advection 2 0.3 1.1

/-- Cubic profile `f s = s ^ 3` at `c = 2, t = 0.3, x = 1.1`. -/
example :
    deriv (fun t => ((1.1 : ℝ) - 2 * t) ^ 3) (0.3 : ℝ)
      + 2 * deriv (fun x => (x - 2 * (0.3 : ℝ)) ^ 3) (1.1 : ℝ) = 0 := by
  have hf : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s ^ 3) (3 * s ^ 2) s := fun s => by
    simpa using hasDerivAt_pow 3 s
  exact EarthScience.traveling_profile_solves_advection hf 2 0.3 1.1

/-- Zero speed: the profile is static, so `u_t = 0` and the residual is `0`. -/
example (t x : ℝ) :
    deriv (fun t => Real.sin (x - 0 * t)) t
      + 0 * deriv (fun x => Real.sin (x - 0 * t)) x = 0 :=
  EarthScience.sine_traveling_profile_solves_advection 0 t x
