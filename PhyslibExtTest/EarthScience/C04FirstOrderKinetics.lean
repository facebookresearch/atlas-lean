/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.C04FirstOrderKinetics

/-!
# First-order decay checks

Concrete consumers of `PhyslibExt.EarthScience.C04FirstOrderKinetics`:
a numeric decay, the initial value, the integrated consumption, and
the degenerate zero-rate case.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`k = 2`, `c0 = 5`, the consumption over `[0, 1]` is `5 - 5*exp(-2)`.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.C04FirstOrderKinetics`
-/

/-- Numeric decay: `c(t) = 5*exp(-2*t)` solves `c' = -2*c` at `t = 1`. -/
example : HasDerivAt (fun t : ℝ => 5 * Real.exp (-2 * t))
    (-2 * (5 * Real.exp (-2 * 1))) 1 :=
  EarthScience.firstOrder_decay_hasDerivAt 2 5 1

/-- Numeric initial value: `c(0) = 5`. -/
example : (5 : ℝ) * Real.exp (-2 * 0) = 5 :=
  EarthScience.firstOrder_decay_initial 2 5

/-- Numeric integrated consumption over `[0, 1]`. -/
example : ∫ s in (0 : ℝ)..1, 2 * (5 * Real.exp (-2 * s)) =
    5 - 5 * Real.exp (-2 * 1) :=
  EarthScience.firstOrder_decay_consumption 2 5 1

/-- Degenerate case `k = 0`: no decay, consumption `0` over any interval. -/
example (c0 t : ℝ) : ∫ s in (0 : ℝ)..t, 0 * (c0 * Real.exp (-0 * s)) =
    c0 - c0 * Real.exp (-0 * t) :=
  EarthScience.firstOrder_decay_consumption 0 c0 t

/-- Degenerate case `c0 = 0`: the zero solution stays zero. -/
example (k t : ℝ) : HasDerivAt (fun t : ℝ => 0 * Real.exp (-k * t))
    (-k * (0 * Real.exp (-k * t))) t :=
  EarthScience.firstOrder_decay_hasDerivAt k 0 t
