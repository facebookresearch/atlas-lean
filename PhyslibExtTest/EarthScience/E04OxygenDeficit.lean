/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.E04OxygenDeficit

/-!
# Streeter-Phelps checks

Concrete consumers of `PhyslibExt.EarthScience.E04OxygenDeficit`: the
witness `ka = 2`, `kd = 1`, `L0 = 1`, `D0 = 0` giving
`D(t) = exp(-t) - exp(-2*t)`, the equal-rate branch, and the
zero-demand boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
witness deficit at `t = 1` is `exp(-1) - exp(-2)`.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.E04OxygenDeficit`
-/

/-- Witness: unequal rates `ka = 2`, `kd = 1`, `L0 = 1`, `D0 = 0`. -/
example (t : ℝ) : HasDerivAt
    (fun t : ℝ => 0 * Real.exp (-2 * t) +
      1 * 1 * (Real.exp (-1 * t) - Real.exp (-2 * t)) / (2 - 1))
    (1 * (1 * Real.exp (-1 * t)) -
      2 * (0 * Real.exp (-2 * t) +
      1 * 1 * (Real.exp (-1 * t) - Real.exp (-2 * t)) / (2 - 1))) t :=
  EarthScience.oxygen_deficit_hasDerivAt 2 1 1 0 t (by norm_num) (by norm_num)
    (by norm_num)

/-- Witness: equal rates `k = 1`, `L0 = 1`, `D0 = 0`. -/
example (t : ℝ) : HasDerivAt (fun t : ℝ => (0 + 1 * 1 * t) * Real.exp (-1 * t))
    (1 * (1 * Real.exp (-1 * t)) -
      1 * ((0 + 1 * 1 * t) * Real.exp (-1 * t))) t :=
  EarthScience.oxygen_deficit_equalRate_hasDerivAt 1 1 0 t (by norm_num)

/-- Boundary case `L0 = 0`: no demand, the deficit decays as `D0*exp(-ka*t)`. -/
example (ka D0 t : ℝ) :
    HasDerivAt (fun t : ℝ => D0 * Real.exp (-ka * t))
      (-ka * (D0 * Real.exp (-ka * t))) t :=
  EarthScience.bod_decay_hasDerivAt ka D0 t

/-- BOD decay: `L(t) = 3*exp(-t)` solves `L' = -L`. -/
example (t : ℝ) : HasDerivAt (fun t : ℝ => 3 * Real.exp (-1 * t))
    (-1 * (3 * Real.exp (-1 * t))) t :=
  EarthScience.bod_decay_hasDerivAt 1 3 t
