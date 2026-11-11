/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.ODE.M08HeatMode

/-!
# Single-mode heat-equation checks

Concrete consumers of `MathlibExt.Analysis.ODE.M08HeatMode`: the heat
equation at a numeric point, boundary/initial values at a numeric
point, decay at `t ≥ 0` for `κ > 0`, and the degenerate `κ = 0` case
(constant-in-time mode).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Heat equation at a numeric point
- B. Boundary and initial values
- C. Degenerate diffusivity

## iv. References

- `MathlibExt.Analysis.ODE.M08HeatMode`
-/

/-- Heat equation at `κ = 0.7, t = 0.4, x = 0.3`. -/
example : deriv (fun t => Real.exp (-(0.7 : ℝ) * Real.pi ^ 2 * t) * Real.sin (Real.pi * (0.3 : ℝ))) (0.4 : ℝ)
    = 0.7 * iteratedDeriv 2
        (fun x => Real.exp (-(0.7 : ℝ) * Real.pi ^ 2 * (0.4 : ℝ)) * Real.sin (Real.pi * x)) (0.3 : ℝ) :=
  EarthScience.heat_mode_satisfies_heat_eq

/-- Boundary and initial data at `κ = 0.7, t = 0.4, x = 0.3`. -/
example : Real.exp (-(0.7 : ℝ) * Real.pi ^ 2 * (0.4 : ℝ)) * Real.sin (Real.pi * 0) = 0 ∧
    Real.exp (-(0.7 : ℝ) * Real.pi ^ 2 * (0.4 : ℝ)) * Real.sin (Real.pi * 1) = 0 ∧
    Real.exp (-(0.7 : ℝ) * Real.pi ^ 2 * 0) * Real.sin (Real.pi * (0.3 : ℝ)) = Real.sin (Real.pi * (0.3 : ℝ)) :=
  EarthScience.heat_mode_boundary_initial

/-- Degenerate diffusivity `κ = 0`: the mode is constant in time,
so its `t`-derivative is `0`. -/
example (x t : ℝ) : HasDerivAt
    (fun t => Real.exp (-(0 : ℝ) * Real.pi ^ 2 * t) * Real.sin (Real.pi * x)) 0 t := by
  have h := EarthScience.heat_mode_hasDerivAt_t (κ := 0) (x := x) (t := t)
  simpa using h
