/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.P06IdealGasAdiabatic

/-!
# Ideal-gas and potential-temperature checks

Concrete consumers of `PhyslibExt.EarthScience.P06IdealGasAdiabatic`:
`p = 6`, `R = 2`, `T = 3` (so `ρ = 1`), the zero-pressure boundary,
and potential temperature at the reference pressure.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Density
- B. Potential temperature at the reference pressure

## iv. References

- `PhyslibExt.EarthScience.P06IdealGasAdiabatic`
-/

/-- Numeric density: `6 = 1 * 2 * 3` gives `ρ = 1`. -/
example : (1 : ℝ) = 6 / (2 * 3) :=
  EarthScience.idealGas_density (by norm_num) (by norm_num) (by norm_num)

/-- Zero-pressure boundary: density zero. -/
example : (0 : ℝ) = 0 / (2 * 3) :=
  EarthScience.idealGas_density (by norm_num) (by norm_num) (by norm_num)

/-- Potential temperature at the reference pressure equals the temperature. -/
example : (300 : ℝ) * (1000 / 1000) ^ ((287 : ℝ) / 1005) = 300 := by
  norm_num

/-- Halving pressure and temperature with `R / cp = 1` preserves
potential temperature at the original reference pressure. -/
example : (150 : ℝ) * (1000 / 500) ^ ((1 : ℝ) / 1) = 300 := by
  simpa only [div_self (by norm_num : (1000 : ℝ) ≠ 0), Real.one_rpow, mul_one] using
    (EarthScience.potentialTemperature_const_of_poisson
      (T1 := 300) (T2 := 150) (p1 := 1000) (p2 := 500) (p_ref := 1000)
      (R := 1) (cp := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- Public shape of the potential-temperature theorem. -/
example {T1 T2 p1 p2 p_ref R cp : ℝ}
    (hp1 : 0 < p1) (hp2 : 0 < p2) (href : 0 < p_ref)
    (hR : 0 < R) (hcp : 0 < cp) (hT1 : 0 < T1)
    (hpoisson : T2 = T1 * (p2 / p1) ^ (R / cp)) :
    T2 * (p_ref / p2) ^ (R / cp) = T1 * (p_ref / p1) ^ (R / cp) :=
  EarthScience.potentialTemperature_const_of_poisson hp1 hp2 href hR hcp hT1 hpoisson
