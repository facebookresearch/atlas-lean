/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ConductiveGeotherm

/-!
# Geotherm checks

Concrete consumers of `PhyslibExt.EarthScience.ConductiveGeotherm`:
`Ts = 0`, `Tb = 1300`, `L = 100`, `k = 3`, `H = 0.02` (so `T(50) = 658.33…`,
`T'(50) = 13 - 1/3`, `T'' = -0.02/3`), plus the zero-production boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric geotherm
- B. Zero-production boundary

## iv. References

- `PhyslibExt.EarthScience.ConductiveGeotherm`
-/

/-- Numeric geotherm: boundary values at `d = 0` and `d = 100`. -/
example : ((0 : ℝ) + ((1300 - 0) / 100 + 0.02 * 100 / (2 * 3)) * 0
      - 0.02 * 0 ^ 2 / (2 * 3)) = (0 : ℝ) ∧
    ((0 : ℝ) + ((1300 - 0) / 100 + 0.02 * 100 / (2 * 3)) * 100
      - 0.02 * 100 ^ 2 / (2 * 3)) = 1300 :=
  EarthScience.geotherm_boundary (Ts := 0) (Tb := 1300) (L := 100) (k := 3) (H := 0.02) (by norm_num) (by norm_num)

/-- Numeric geotherm: first derivative at `d = 50`. -/
example : HasDerivAt
    (fun (d : ℝ) => (0 : ℝ) + ((1300 - 0) / 100 + 0.02 * 100 / (2 * 3)) * d
      - 0.02 * d ^ 2 / (2 * 3))
    ((1300 - 0) / 100 + 0.02 * 100 / (2 * 3) - 0.02 * 50 / 3) 50 :=
  EarthScience.geotherm_hasDerivAt (Ts := 0) (Tb := 1300) (L := 100) (k := 3) (H := 0.02) (d := 50)

/-- Numeric geotherm: second derivative and ODE at `d = 50`. -/
example : HasDerivAt
    (fun (d : ℝ) => (1300 - 0) / 100 + 0.02 * 100 / (2 * 3) - 0.02 * d / 3)
    (-0.02 / 3) 50 ∧ (3 : ℝ) * (-0.02 / 3) + 0.02 = 0 :=
  EarthScience.geotherm_second_deriv (Ts := 0) (Tb := 1300) (L := 100) (k := 3) (H := 0.02) (d := 50) (by norm_num)

/-- Zero-production boundary: `H = 0` gives the linear profile
`T(d) = Ts + (Tb - Ts) * d / L`; at `d = 50`, `T = 650`. -/
example : (0 : ℝ) + ((1300 - 0) / 100 + 0 * 100 / (2 * 3)) * 50
    - 0 * 50 ^ 2 / (2 * 3) = 650 := by norm_num
