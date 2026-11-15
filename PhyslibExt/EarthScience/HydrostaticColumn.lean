/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!
# Hydrostatic columns

A hydrostatic column with constant density `rho` and gravity magnitude
`g` has pressure profile `p(z) = p0 - rho * g * z` in height coordinates
(`z` upward), satisfying `dp/dz = -rho * g` and `p(0) = p0`. In depth
coordinates `d = -z` (downward) the same column reads
`p(d) = p0 + rho * g * d`, with `dp/dd = rho * g`.

## i. Overview

Both statements pair the derivative of an affine function with an
evaluation: the surface value `p(0) = p0` in height coordinates, and
agreement with the height profile at `d = -z` in depth coordinates.
Hydrostatic balance is stipulated; the results show that the profile is
a solution of `dp/dz = -rho * g` with `p(0) = p0` (uniqueness is not
proved here), not a derivation of the balance law itself.

## ii. Key results

- `EarthScience.hydrostatic_pressure`: height-coordinate profile,
  derivative and surface value.
- `EarthScience.hydrostatic_pressure_depth`: depth-coordinate profile,
  derivative and agreement with the height form.

## iii. Table of contents

- A. Height coordinates
- B. Depth coordinates

## iv. References

- `HasDerivAt` API in `Mathlib/Analysis/Calculus/Deriv/Add.lean`.
-/

@[expose] public section

namespace EarthScience

/-- Hydrostatic column: `p(z) = p0 - ρ * g * z` satisfies `dp/dz = -ρ * g`
and `p(0) = p0`. -/
theorem hydrostatic_pressure (p0 ρ g : ℝ) (z : ℝ) :
    HasDerivAt (fun z => p0 - ρ * g * z) (-(ρ * g)) z ∧
      (fun z => p0 - ρ * g * z) 0 = p0 := by
  constructor
  · have h1 : HasDerivAt (fun z : ℝ => ρ * g * z) (ρ * g) z := by
      have h := (hasDerivAt_id' z).const_mul (ρ * g)
      simpa only [mul_one] using h
    have h2 : HasDerivAt (fun z : ℝ => p0 - ρ * g * z) (0 - ρ * g) z :=
      (hasDerivAt_const z p0).sub h1
    simpa only [zero_sub] using h2
  · simp

/-- In depth coordinates `d = -z`, the same column reads
`p(d) = p0 + ρ * g * d`, with `dp/dd = ρ * g`. -/
theorem hydrostatic_pressure_depth (p0 ρ g : ℝ) (d : ℝ) :
    HasDerivAt (fun d => p0 + ρ * g * d) (ρ * g) d ∧
      (fun d => p0 + ρ * g * d) d = p0 - ρ * g * (-d) := by
  constructor
  · have h1 : HasDerivAt (fun d : ℝ => ρ * g * d) (ρ * g) d := by
      have h := (hasDerivAt_id' d).const_mul (ρ * g)
      simpa only [mul_one] using h
    have h2 : HasDerivAt (fun d : ℝ => p0 + ρ * g * d) (0 + ρ * g) d :=
      (hasDerivAt_const d p0).add h1
    simpa only [zero_add] using h2
  · ring

end EarthScience
