/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ManufacturedResidual
import Mathlib.Tactic.NormNum

/-!
# Manufactured-solution residual checks

Concrete consumers of `PhyslibExt.EarthScience.ManufacturedResidual`.

## i. Overview

Numeric case `x = 1.3`, `h = 0.2`: the difference quotient is `20.36`
and the residual is `0.08 = 2 h²`, which also attains the bound
`|residual| ≤ 2 h²`. At `x = 0` the exact second derivative `12 x²`
vanishes, so the quotient equals the residual; with `h = 3` both are
`18 = 2 h²`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric checks

## iv. References

- `PhyslibExt.EarthScience.ManufacturedResidual`
-/

/-- Numeric case: `x = 1.3`, `h = 0.2`, quotient `20.36`. -/
example : ((1.3 + 0.2) ^ 4 - 2 * (1.3 : ℝ) ^ 4 + (1.3 - 0.2) ^ 4) / (0.2 : ℝ) ^ 2 =
    12 * (1.3 : ℝ) ^ 2 + 2 * (0.2 : ℝ) ^ 2 :=
  EarthScience.manufactured_central_second_diff (by norm_num)

/-- Numeric residual: `x = 1.3`, `h = 0.2`, residual `0.08 = 2 h²`. -/
example : ((1.3 + 0.2) ^ 4 - 2 * (1.3 : ℝ) ^ 4 + (1.3 - 0.2) ^ 4) / (0.2 : ℝ) ^ 2 -
    12 * (1.3 : ℝ) ^ 2 = 2 * (0.2 : ℝ) ^ 2 :=
  EarthScience.manufactured_central_second_diff_residual (by norm_num)

/-- At `x = 0` the exact second derivative vanishes, so with `h = 3` the
quotient and the residual are both `18 = 2 h²`. -/
example : ((0 + 3) ^ 4 - 2 * (0 : ℝ) ^ 4 + (0 - 3) ^ 4) / (3 : ℝ) ^ 2 - 12 * (0 : ℝ) ^ 2 =
    2 * (3 : ℝ) ^ 2 :=
  EarthScience.manufactured_central_second_diff_residual (by norm_num)

/-- Residual bound at the numeric case: `|residual| ≤ 2 h²` with equality. -/
example : |((1.3 + 0.2) ^ 4 - 2 * (1.3 : ℝ) ^ 4 + (1.3 - 0.2) ^ 4) / (0.2 : ℝ) ^ 2 -
    12 * (1.3 : ℝ) ^ 2| ≤ 2 * (0.2 : ℝ) ^ 2 :=
  EarthScience.manufactured_central_second_diff_residual_le (by norm_num)
