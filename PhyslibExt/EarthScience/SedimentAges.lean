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

Under a constant accumulation speed `v`, with no compaction, no hiatus, present surface age
zero and depth positive downward, the sediment at depth `d` has age
`sedimentAge v d = d / v`, and the sediment of age `t` lies at depth
`sedimentDepth v t = v * t`.

## i. Overview

Explicit no-compaction/no-hiatus age model; other age models are not inferred. For `v > 0`
the surface has age zero, buried sediment has nonnegative age, age is strictly increasing in
depth on `d ≥ 0` (deeper is older), and `sedimentAge v` and `sedimentDepth v` are inverse to
each other. The age difference between two horizons is their separation divided by the
accumulation speed.

## ii. Key results

- `EarthScience.sedimentAge`, `EarthScience.sedimentDepth`: the age-depth model.
- `EarthScience.sedimentAge_zero`, `EarthScience.sedimentAge_nonneg`: the surface has age
  zero and sediment at depth `d ≥ 0` has nonnegative age.
- `EarthScience.sediment_age_strictMonoOn`: age is strictly increasing in depth on `d ≥ 0`.
- `EarthScience.sediment_depth_age_inverse`, `EarthScience.sedimentDepth_sedimentAge`: age
  and depth invert each other.
- `EarthScience.sedimentAge_sub`: horizons at depths `d₁` and `d₂` differ in age by
  `(d₂ - d₁) / v`.

## iii. References

- `strictMono_div_right_of_pos` for the monotonicity of `d ↦ d / v`.
- `mul_div_cancel_left₀`, `mul_div_cancel₀` and `sub_div` for the inverse pair and the age
  difference.
-/

@[expose] public section

namespace EarthScience

/-- Age of the sediment at depth `d` (positive downward) under constant accumulation speed
`v`, with no compaction, no hiatus and present surface age zero: `d / v`. -/
noncomputable def sedimentAge (v d : ℝ) : ℝ := d / v

/-- Depth (positive downward) of the sediment of age `t` under constant accumulation speed
`v`, with no compaction and no hiatus: `v * t`. -/
noncomputable def sedimentDepth (v t : ℝ) : ℝ := v * t

/-- The present surface, at depth `0`, has age `0`. -/
theorem sedimentAge_zero (v : ℝ) : sedimentAge v 0 = 0 :=
  zero_div v

/-- With accumulation speed `v > 0`, sediment at depth `d ≥ 0` has nonnegative age. -/
theorem sedimentAge_nonneg {v d : ℝ} (hv : 0 < v) (hd : 0 ≤ d) : 0 ≤ sedimentAge v d :=
  div_nonneg hd hv.le

/-- Constant accumulation: with accumulation speed `v > 0`, the age is strictly increasing
in depth `d ≥ 0` (deeper is older). -/
theorem sediment_age_strictMonoOn (v : ℝ) (hv : 0 < v) :
    StrictMonoOn (sedimentAge v) (Set.Ici 0) :=
  (strictMono_div_right_of_pos hv).strictMonoOn _

/-- Constant accumulation inverts: the sediment of age `t` lies at depth `v * t`, and the
sediment there has age `t`. -/
theorem sediment_depth_age_inverse (v t : ℝ) (hv : 0 < v) :
    sedimentAge v (sedimentDepth v t) = t :=
  mul_div_cancel_left₀ t hv.ne'

/-- Conversely, the sediment of the age found at depth `d` lies at depth `d`. -/
theorem sedimentDepth_sedimentAge (v d : ℝ) (hv : 0 < v) :
    sedimentDepth v (sedimentAge v d) = d :=
  mul_div_cancel₀ d hv.ne'

/-- Age difference between horizons: sediment at depths `d₁` and `d₂` differs in age by the
separation `d₂ - d₁` divided by the accumulation speed `v`. -/
theorem sedimentAge_sub (v d₁ d₂ : ℝ) :
    sedimentAge v d₂ - sedimentAge v d₁ = (d₂ - d₁) / v :=
  (sub_div d₂ d₁ v).symm

end EarthScience
