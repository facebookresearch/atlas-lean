/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.StratigraphicHiatus

/-!
# Stratigraphic-hiatus checks

Concrete consumers of `PhyslibExt.EarthScience.StratigraphicHiatus`: with
`v = 2`, hiatus depth `h = 10` and gap `g = 3`, the age at depth `4` is `2`,
at the hiatus it is `8` (not the no-hiatus value `5`), and a pair straddling
the hiatus differs by `(12 - 4) / 2 + 3 = 7`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The boundary
case is the hiatus itself, where the jump is visible, and a straddling pair
shows the age difference exceeds the constant-accumulation difference.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.StratigraphicHiatus`
-/

open EarthScience

/-- Below the hiatus: with `v = 2`, depth `4` has age `2`. -/
example : hiatusAge 2 10 3 4 = 2 := by
  rw [hiatus_age_below (by norm_num)]
  norm_num

/-- At the hiatus: with `v = 2`, `h = 10`, `g = 3`, the age at depth `10` is `8`. -/
example : hiatusAge 2 10 3 10 = 8 := by
  rw [hiatus_age_jump]
  norm_num

/-- Boundary case: the jump at the hiatus is exactly the gap `g = 3`, not zero. -/
example : hiatusAge 2 10 3 10 - 10 / 2 = 3 := by
  rw [hiatus_age_jump]
  norm_num

/-- Straddling pair: depths `4` and `12` differ in age by `7`, more than the
constant-accumulation difference `(12 - 4) / 2 = 4`. -/
example : hiatusAge 2 10 3 12 - hiatusAge 2 10 3 4 = 7 := by
  rw [hiatus_age_straddle (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- No negative rate: the deeper of the straddling pair is strictly older. -/
example : hiatusAge 2 10 3 4 < hiatusAge 2 10 3 12 :=
  hiatus_age_strictMono (by norm_num) (by norm_num) (by norm_num)
