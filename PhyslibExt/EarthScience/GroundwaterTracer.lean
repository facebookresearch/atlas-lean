/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Capstone: groundwater column and tracer budget

## i. Overview

Saturated column, exact rational inputs; decimal numerals in the
contract are the exact stated rational inputs below. Darcy flux
`q = -K * grad h` with `K = 10⁻⁴ m/s` and head gradient `0.01` is
`-10⁻⁶ m/s`; pore velocity `v = q / φ` with porosity `φ = 1 / 4` is
`-4 * 10⁻⁶ m/s`. The Darcy/tracer coupling is the conservative
periodic tracer update on two cells with upwind weight `ν ∈ [0, 1]`:
`c₁' = (1 - ν) * c₁ + ν * c₂`, `c₂' = (1 - ν) * c₂ + ν * c₁`,
which conserves total mass and preserves nonnegativity. This capstone
is proved self-contained from Mathlib primitives; it does not depend
on any sibling development.

## ii. Key results

- `EarthScience.darcy_flux_value`: Darcy flux `-10⁻⁶ m/s`.
- `EarthScience.pore_velocity_value`: pore velocity `-4 * 10⁻⁶ m/s`.
- `EarthScience.tracer_update_mass_conserved`: the periodic update
  conserves total tracer mass.
- `EarthScience.tracer_update_nonneg`: the update preserves nonnegativity.

## iii. Table of contents

- A. Darcy flux and pore velocity
- B. Conservative periodic tracer update

## iv. References

- `add_nonneg`, `mul_nonneg` in Mathlib.

## A. Darcy flux and pore velocity
-/

@[expose] public section

namespace EarthScience

/-- Capstone (groundwater column): Darcy flux `q = -K * grad h` with
`K = 10⁻⁴ m/s` and head gradient `0.01` is `-10⁻⁶ m/s`. All numerals
are exact rationals. -/
theorem darcy_flux_value :
    -(1 / 10000 : ℝ) * (1 / 100) = -1 / 1000000 := by
  norm_num

/-- Pore velocity `v = q / φ` with porosity `φ = 1 / 4` and the Darcy
flux above is `-4 * 10⁻⁶ m/s = -1 / 250000`. -/
theorem pore_velocity_value :
    (-1 / 1000000 : ℝ) / (1 / 4) = -4 / 1000000 := by
  norm_num

/-! ## B. Conservative periodic tracer update -/

/-- Conservative periodic tracer update on two cells: with upwind weight
`ν ∈ [0, 1]`, `c₁' = (1 - ν) * c₁ + ν * c₂` and
`c₂' = (1 - ν) * c₂ + ν * c₁`, total mass is conserved:
`c₁' + c₂' = c₁ + c₂`. -/
theorem tracer_update_mass_conserved {ν c₁ c₂ : ℝ} :
    ((1 - ν) * c₁ + ν * c₂) + ((1 - ν) * c₂ + ν * c₁) = c₁ + c₂ := by
  ring

/-- The same update preserves nonnegativity: for `ν ∈ [0, 1]` and
`c₁, c₂ ≥ 0`, both updated concentrations are nonnegative. -/
theorem tracer_update_nonneg {ν c₁ c₂ : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    0 ≤ (1 - ν) * c₁ + ν * c₂ ∧ 0 ≤ (1 - ν) * c₂ + ν * c₁ := by
  have h1ν : 0 ≤ 1 - ν := by linarith
  constructor
  · exact add_nonneg (mul_nonneg h1ν hc₁) (mul_nonneg hν0 hc₂)
  · exact add_nonneg (mul_nonneg h1ν hc₂) (mul_nonneg hν0 hc₁)

end EarthScience
