/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bounded instrument bias gives a deterministic output bound

With known calibration `y = a * x + b + ε`, slope `a ≠ 0`, and a
bounded instrument bias `|ε| ≤ B`, the calibrated estimator
`(y - b) / a` differs from the true value `x` by at most `B / |a|`.

## i. Overview

This is a deterministic worst-case bound; no probability is involved.
The estimator error equals `ε / a` exactly, so the bound is just the
absolute value of that identity combined with `|ε| ≤ B` and
`0 < |a|`. It complements the exact pointwise error and the
unbiasedness result in `PhyslibExt.EarthScience.Calibration`, neither
of which states a bound in terms of a bias cap.

## ii. Key results

- `EarthScience.instrument_bias_output_bound`: the output bound
  `|(y - b) / a - x| ≤ B / |a|`.

## iii. References

- `abs_div`, `div_le_div_iff_of_pos_right`, `abs_pos` (Mathlib).
-/

@[expose] public section

namespace EarthScience

/-- Bounded instrument bias gives a deterministic output bound: with
`y = a * x + b + ε`, `a ≠ 0`, and `|ε| ≤ B`, the calibrated estimator
`(y - b) / a` differs from `x` by at most `B / |a|`. -/
theorem instrument_bias_output_bound {a b x ε B : ℝ} (ha : a ≠ 0)
    (hε : |ε| ≤ B) :
    |((a * x + b + ε - b) / a) - x| ≤ B / |a| := by
  have hpos : 0 < |a| := abs_pos.mpr ha
  have h1 : ((a * x + b + ε - b) / a) - x = ε / a := by
    field_simp
    ring
  rw [h1, abs_div]
  exact (div_le_div_iff_of_pos_right hpos).mpr hε

end EarthScience
