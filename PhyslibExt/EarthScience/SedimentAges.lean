/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Basic
/-!
# Constant-accumulation sediment ages

With constant accumulation speed `v > 0`, no compaction and no hiatus,
the age `t = d/v` is strictly increasing in depth `d ≥ 0`, and depth
`d = v*t` inverts to age `(v*t)/v = t`.

## i. Overview

Explicit no-compaction/no-hiatus model; present surface age zero. Other
age models are not inferred. Depth is positive downward.

## ii. Key results

- `EarthScience.sediment_age_strictMonoOn`: age is strictly increasing
  in depth on `d ≥ 0`.
- `EarthScience.sediment_depth_age_inverse`: `(v*t)/v = t`.

## iii. References

- `div_lt_div_of_pos_right` in `Mathlib/Algebra/Order/GroupWithZero/Basic.lean`.
- `mul_div_cancel_left₀` for the inverse.
-/

@[expose] public section

namespace EarthScience

/-- Constant accumulation: with accumulation speed `v > 0`, the age
`t = d/v` is strictly increasing in depth `d ≥ 0` (no compaction, no hiatus,
present surface age zero). -/
theorem sediment_age_strictMonoOn (v : ℝ) (hv : 0 < v) :
    StrictMonoOn (fun d => d / v) (Set.Ici 0) := by
  exact (strictMono_div_right_of_pos hv).strictMonoOn _

/-- Constant accumulation inverts: depth `d = v*t` has age `(v*t)/v = t`. -/
theorem sediment_depth_age_inverse (v t : ℝ) (hv : 0 < v) :
    v * t / v = t := by
  exact mul_div_cancel_left₀ t (ne_of_gt hv)

end EarthScience
