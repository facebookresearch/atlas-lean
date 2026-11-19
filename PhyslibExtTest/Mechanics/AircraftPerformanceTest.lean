/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.AircraftPerformance

import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Mechanics.AircraftPerformance`

Rounded standard-atmosphere values for the isothermal layer above 11 km, in SI units: reference
density `0.3639 kg/m³` at the layer base, `g = 9.80665 m/s²`, `Rs = 287.05 J/(kg K)`,
`T = 216.65 K`, declared band `[0, 9000] m` above the base.

* the scale height lies between `6341 m` and `6342 m`;
* two admissible heights of the band give different positive densities;
* the same state in kilometres gives `10 ^ 9` times the density in `kg/m³`.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.AircraftPerformance

open _root_.AircraftPerformance

-- The scale height of the fixture layer lies between `6341 m` and `6342 m`.
example :
    6341 < scaleHeight 287.05 216.65 9.80665 ∧ scaleHeight 287.05 216.65 9.80665 < 6342 := by
  have h9 : (0:ℝ) < 9.80665 := by norm_num
  unfold scaleHeight
  rw [abs_of_pos h9]
  constructor
  · rw [lt_div_iff₀ h9]
    norm_num
  · rw [div_lt_iff₀ h9]
    norm_num

-- Two admissible heights of the band give different positive densities.
example :
    (0 : ℝ) ∈ Set.Icc (0 : ℝ) 9000 ∧ (1000 : ℝ) ∈ Set.Icc (0 : ℝ) 9000 ∧
      0 < isothermalDensity 0.3639 9.80665 287.05 216.65 1000 ∧
      isothermalDensity 0.3639 9.80665 287.05 216.65 1000 <
        isothermalDensity 0.3639 9.80665 287.05 216.65 0 := by
  have hρ : (0:ℝ) < 0.3639 := by norm_num
  have hg : (0:ℝ) < 9.80665 := by norm_num
  have hRs : (0:ℝ) < 287.05 := by norm_num
  have hT : (0:ℝ) < 216.65 := by norm_num
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 9000 := ⟨by norm_num, by norm_num⟩
  have h1000 : (1000:ℝ) ∈ Set.Icc (0:ℝ) 9000 := ⟨by norm_num, by norm_num⟩
  have hlt : (0:ℝ) < 1000 := by norm_num
  refine ⟨h0, h1000, isothermalDensity_pos hρ hRs hT _ _, ?_⟩
  exact isothermalDensity_strictAntiOn hρ hg hRs hT _ _ h0 h1000 hlt

-- The same state in kilometres (`l = 1 / 1000`): `ρ0 = 363900000 kg/km³`,
-- `g = 0.00980665 km/s²`, `Rs = 0.00028705 km²/(s² K)` and height `1 km` give `10 ^ 9` times
-- the density in `kg/m³` at `1000 m`.
example :
    isothermalDensity 363900000 0.00980665 0.00028705 216.65 1 =
      10 ^ 9 * isothermalDensity 0.3639 9.80665 287.05 216.65 1000 := by
  have h := isothermalDensity_unitChange (1:ℝ) (l := 1/1000) (s := 1) (k := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (show (0:ℝ) < 287.05 by norm_num) (show (0:ℝ) < 216.65 by norm_num)
    0.3639 9.80665 1000
  have e6 : ((1:ℝ) / (1/1000) ^ 3) = 10 ^ 9 := by norm_num
  have e1 : ((10:ℝ) ^ 9 * 0.3639) = 363900000 := by norm_num
  have e2 : ((1/1000:ℝ) / 1 ^ 2 * 9.80665) = 0.00980665 := by norm_num
  have e3 : ((1/1000:ℝ) ^ 2 / (1 ^ 2 * 1) * 287.05) = 0.00028705 := by norm_num
  have e4 : ((1:ℝ) * 216.65) = 216.65 := by norm_num
  have e5 : ((1/1000:ℝ) * 1000) = 1 := by norm_num
  rw [e6, e1, e2, e3, e4, e5] at h
  exact h

end PhyslibExtTest.Mechanics.AircraftPerformance
