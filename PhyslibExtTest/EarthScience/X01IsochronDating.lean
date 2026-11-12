/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.X01IsochronDating

/-!
# Isochron-dating capstone checks

Concrete consumers of `PhyslibExt.EarthScience.X01IsochronDating`:
slope `1` and recovered age `10` at `b = 3`, the `t = 0` boundary,
and the combined slope-plus-age statement.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Slope, age, and zero-age boundary

## iv. References

- `PhyslibExt.EarthScience.X01IsochronDating`
-/

/-- Slope `1` at `b = 3`. -/
example : ((3 + 2 * (Real.exp ((Real.log 2 / 10) * 10) - 1))
      - (3 + 1 * (Real.exp ((Real.log 2 / 10) * 10) - 1))) / (2 - 1) = 1 :=
  EarthScience.isochron_slope_eq_one (b := 3)

/-- Recovered age `10`. -/
example : Real.log (1 + 1) / (Real.log 2 / 10) = 10 :=
  EarthScience.isochron_age_recovery

/-- Zero-age boundary at `b = 3`. -/
example : ((3 + 2 * (Real.exp ((Real.log 2 / 10) * 0) - 1))
      - (3 + 1 * (Real.exp ((Real.log 2 / 10) * 0) - 1))) / (2 - 1) = 0 :=
  EarthScience.isochron_slope_at_zero_age (b := 3)

/-- Combined capstone statement: slope `1` and recovered age `10`. -/
example :
    ((3 + 2 * (Real.exp ((Real.log 2 / 10) * 10) - 1))
      - (3 + 1 * (Real.exp ((Real.log 2 / 10) * 10) - 1))) / (2 - 1) = 1 ∧
      Real.log (1 + 1) / (Real.log 2 / 10) = 10 :=
  ⟨EarthScience.isochron_slope_eq_one (b := 3), EarthScience.isochron_age_recovery⟩
