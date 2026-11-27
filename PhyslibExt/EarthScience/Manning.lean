/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Manning discharge monotonicity

## i. Overview

Manning's empirical open-channel law, for fixed section geometry, is
`Q = (1 / n) * A * R ^ (2 / 3) * sqrt S` with roughness `n`, flow area
`A`, hydraulic radius `R`, and slope `S`, in one consistent unit system.
This module records the two parameter monotonicities, on their physical
domains: discharge strictly increases when a nonnegative slope increases,
and strictly decreases when a positive roughness increases. Outside the
positive-parameter domain the totalized definition has no physical
interpretation. It is the empirical law only; no derivation from a fluid
PDE and no calibration is claimed.

## ii. Key results

- `EarthScience.manningDischarge`: the Manning discharge.
- `EarthScience.manningDischarge_lt_of_slope_lt`: strict increase in
  slope.
- `EarthScience.manningDischarge_lt_of_roughness_lt`: strict decrease
  in roughness.

## iii. Table of contents

- A. Discharge and its monotonicities

## iv. References

- R. Manning, on the flow of water in open channels and pipes, 1891.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Discharge and its monotonicities -/

/-- Manning discharge for fixed section geometry:
`Q = (1 / n) * A * R ^ (2 / 3) * sqrt S`, with roughness `n`, flow area
`A`, hydraulic radius `R`, and slope `S`, in one consistent unit system
(the factor-1 SI form; `[n] = T * L^(-1/3)`, so this is not the
US-customary 1.49 form). With the conventions `1 / 0 = 0`, `sqrt x = 0`
for `x < 0`, `0 ^ y = 0` for `y ≠ 0` and `x ^ y = |x| ^ y * cos (π y)` for
`x < 0`, it is `0` when `n = 0`, `R = 0` or `S < 0`. -/
noncomputable def manningDischarge (n A R S : ℝ) : ℝ :=
  (1 / n) * A * R ^ ((2 : ℝ) / 3) * Real.sqrt S

/-- For positive roughness, area, and hydraulic radius, Manning discharge
strictly increases with slope, comparing nonnegative slopes. -/
theorem manningDischarge_lt_of_slope_lt {n A R S1 S2 : ℝ}
    (hn : 0 < n) (hA : 0 < A) (hR : 0 < R)
    (hS1 : 0 ≤ S1) (hS : S1 < S2) :
    manningDischarge n A R S1 < manningDischarge n A R S2 := by
  unfold manningDischarge
  have hRpow : 0 < R ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hR _
  have h1n : 0 < (1 : ℝ) / n := one_div_pos.mpr hn
  have hC : 0 < (1 / n) * A * R ^ ((2 : ℝ) / 3) :=
    mul_pos (mul_pos h1n hA) hRpow
  have hsqrt : Real.sqrt S1 < Real.sqrt S2 := Real.sqrt_lt_sqrt hS1 hS
  exact mul_lt_mul_of_pos_left hsqrt hC

/-- For positive area, hydraulic radius, and slope, Manning discharge
strictly decreases when (positive) roughness increases. -/
theorem manningDischarge_lt_of_roughness_lt {n1 n2 A R S : ℝ}
    (hn1 : 0 < n1) (hn : n1 < n2) (hA : 0 < A) (hR : 0 < R)
    (hS : 0 < S) :
    manningDischarge n2 A R S < manningDischarge n1 A R S := by
  unfold manningDischarge
  have hRpow : 0 < R ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hR _
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hK : 0 < A * R ^ ((2 : ℝ) / 3) * Real.sqrt S :=
    mul_pos (mul_pos hA hRpow) hsqrt
  have h1 : (1 : ℝ) / n2 < 1 / n1 := one_div_lt_one_div_of_lt hn1 hn
  have e1 : (1 / n2) * A * R ^ ((2 : ℝ) / 3) * Real.sqrt S
      = (1 / n2) * (A * R ^ ((2 : ℝ) / 3) * Real.sqrt S) := by ring
  have e2 : (1 / n1) * A * R ^ ((2 : ℝ) / 3) * Real.sqrt S
      = (1 / n1) * (A * R ^ ((2 : ℝ) / 3) * Real.sqrt S) := by ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_right h1 hK

end EarthScience
