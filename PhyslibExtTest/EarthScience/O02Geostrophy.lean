/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.O02Geostrophy

/-!
# Geostrophy and ocean thermal wind

Concrete consumers of `PhyslibExt.EarthScience.O02Geostrophy`.

## i. Overview

Numeric geostrophy (`f = 2`, `g = 10`, gradients `(-1, 3)`) and a shear case, plus the `f = 0`
  exclusion is carried by the hypotheses, not tested.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.O02Geostrophy`
-/

/-- Numeric geostrophy: `f = 2`, `g = 10`, `ηx = -1`, `ηy = 3`. -/
example : (2 : ℝ) * (-10 * 3 / 2) = -10 * 3 ∧ (2 : ℝ) * (10 * (-1) / 2) = 10 * (-1) :=
  EarthScience.geostrophic_balance (by norm_num)

/-- Numeric uniqueness: balance determines `u = -15`, `v = -5`. -/
example : (-15 : ℝ) = -10 * 3 / 2 ∧ (-5 : ℝ) = 10 * (-1) / 2 :=
  EarthScience.geostrophic_unique (by norm_num) (by norm_num) (by norm_num)

/-- Numeric thermal-wind shear between two levels. -/
example : (2 : ℝ) * ((-15) - (-10)) = -10 * (3 - 2) ∧
    (2 : ℝ) * ((-5) - 0) = 10 * ((-1) - 0) :=
  EarthScience.thermal_wind_shear (by norm_num) (by norm_num) (by norm_num) (by norm_num)
