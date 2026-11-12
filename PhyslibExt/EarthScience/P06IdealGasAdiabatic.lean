/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Ideal gas density and potential temperature on a reversible adiabat

## i. Overview

Under `p = ρ * R * T` with `R, T > 0`, the density is `ρ = p / (R * T)`.
For a reversible ideal-gas adiabat, the Poisson relation in ratio form
`T2 = T1 * (p2 / p1) ^ (R / cp)` implies the potential temperature
`θ = T * (p_ref / p) ^ (R / cp)` is unchanged. `R` and `cp` are
mass-specific with the same units; the molar gas constant is not mixed in.

## ii. Key results

- `EarthScience.idealGas_density`: `ρ = p / (R * T)`.
- `EarthScience.potentialTemperature_const_of_poisson`: potential temperature
  is constant along the adiabat.

## iii. Table of contents

- A. Density from the ideal-gas law
- B. Potential temperature

## iv. References

- `Real.div_rpow` / `Real.rpow_pos_of_pos` in Mathlib (real powers).
-/

@[expose] public section

namespace EarthScience

/-- Ideal gas law `p = ρ * R * T` with `R, T > 0` gives `ρ = p / (R * T)`. -/
theorem idealGas_density {p rho R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (h : p = rho * R * T) :
    rho = p / (R * T) := by
  have hRT : R * T ≠ 0 := ne_of_gt (mul_pos hR hT)
  field_simp
  linear_combination -h

/-- Potential temperature is constant along a reversible ideal-gas
adiabat: if `T2 = T1 * (p2 / p1) ^ (R / cp)` (Poisson relation in ratio
form) then `θ2 = θ1` for `θ = T * (p_ref / p) ^ (R / cp)`. The
physical domain `0 < R`, `0 < cp`, and `0 < T1` excludes the undefined
`R / 0` case and nonpositive absolute temperature; positivity of `T2`
then follows from the Poisson relation. -/
theorem potentialTemperature_const_of_poisson {T1 T2 p1 p2 p_ref R cp : ℝ}
    (hp1 : 0 < p1) (hp2 : 0 < p2) (href : 0 < p_ref)
    (_hR : 0 < R) (_hcp : 0 < cp) (_hT1 : 0 < T1)
    (hpoisson : T2 = T1 * (p2 / p1) ^ (R / cp)) :
    T2 * (p_ref / p2) ^ (R / cp) = T1 * (p_ref / p1) ^ (R / cp) := by
  rw [hpoisson, Real.div_rpow hp2.le hp1.le, Real.div_rpow href.le hp2.le,
    Real.div_rpow href.le hp1.le]
  have h1 : (p1 : ℝ) ^ (R / cp) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp1 _)
  have h2 : (p2 : ℝ) ^ (R / cp) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp2 _)
  field_simp

end EarthScience
