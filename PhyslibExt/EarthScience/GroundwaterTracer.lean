/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Groundwater column arithmetic and a two-cell tracer update

## i. Overview

Two independent pieces, stated over exact rationals; decimal numerals
in the docstrings are the exact rational inputs below.

The Darcy flux and pore velocity are evaluations at fixed inputs, not
general laws. Darcy's law `q = -K * dh/dx`, with the sign convention
that flow runs down the head gradient, gives the specific discharge
`q = -10⁻⁶ m/s` for hydraulic conductivity `K = 10⁻⁴ m/s` and head
gradient `dh/dx = 0.01` in a saturated column; the pore (average
linear) velocity `v = q / φ` with effective porosity `φ = 1 / 4` is
`-4 * 10⁻⁶ m/s`.

The tracer results are abstract and independent of those numbers. On
two periodic cells of equal size, the first-order upwind update with
weight `ν` is `c₁' = (1 - ν) * c₁ + ν * c₂`,
`c₂' = (1 - ν) * c₂ + ν * c₁`; with two periodic cells each cell's
upstream neighbour is the other cell, so the update is the same for
either flow direction. It conserves total mass for every `ν` and
preserves nonnegativity under the CFL condition `0 ≤ ν ≤ 1`. Here `ν`
is a free real parameter: for a cell width `Δx` and a time step `Δt`
it would be the Courant number `|v| * Δt / Δx`, but no coupling to the
flux or velocity above is formalized. The module is self-contained
from Mathlib primitives.

## ii. Key results

- `EarthScience.darcy_flux_value`: Darcy flux `-10⁻⁶ m/s` at the
  stated inputs.
- `EarthScience.pore_velocity_value`: pore velocity `-4 * 10⁻⁶ m/s` at
  the stated inputs.
- `EarthScience.tracer_update_mass_conserved`: the two-cell periodic
  update conserves total tracer mass.
- `EarthScience.tracer_update_nonneg`: the update preserves
  nonnegativity for `ν ∈ [0, 1]`.

## iii. Table of contents

- A. Darcy flux and pore velocity
- B. Conservative periodic tracer update

## iv. References

- R. A. Freeze and J. A. Cherry, *Groundwater*, Prentice-Hall (1979),
  Chapter 2 (Physical Properties and Principles), for Darcy's law
  `q = -K dh/dl` and the specific discharge, and Chapter 9
  (Groundwater Contamination), for advective transport at the average
  linear velocity `q / n`.
- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*,
  Cambridge University Press (2002), Chapter 4 (Finite Volume
  Methods), for the conservative first-order upwind method on a
  uniform grid and the CFL condition.
- `add_nonneg`, `mul_nonneg` in Mathlib.

## A. Darcy flux and pore velocity
-/

@[expose] public section

namespace EarthScience

/-- Darcy flux at fixed inputs: `q = -K * dh/dx` with
`K = 10⁻⁴ m/s` and head gradient `0.01` is `-10⁻⁶ m/s`. All numerals
are exact rationals. -/
lemma darcy_flux_value :
    -(1 / 10000 : ℝ) * (1 / 100) = -1 / 1000000 := by
  norm_num

/-- Pore velocity `v = q / φ` with porosity `φ = 1 / 4` and the Darcy
flux above is `-4 * 10⁻⁶ m/s = -1 / 250000`. -/
lemma pore_velocity_value :
    (-1 / 1000000 : ℝ) / (1 / 4) = -4 / 1000000 := by
  norm_num

/-! ## B. Conservative periodic tracer update -/

/-- Conservative periodic tracer update on two cells: for every real
upwind weight `ν`, `c₁' = (1 - ν) * c₁ + ν * c₂` and
`c₂' = (1 - ν) * c₂ + ν * c₁` conserve total mass:
`c₁' + c₂' = c₁ + c₂`. -/
lemma tracer_update_mass_conserved {ν c₁ c₂ : ℝ} :
    ((1 - ν) * c₁ + ν * c₂) + ((1 - ν) * c₂ + ν * c₁) = c₁ + c₂ := by
  ring

/-- The same update preserves nonnegativity: for `ν ∈ [0, 1]` and
`c₁, c₂ ≥ 0`, both updated concentrations are nonnegative. -/
lemma tracer_update_nonneg {ν c₁ c₂ : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    0 ≤ (1 - ν) * c₁ + ν * c₂ ∧ 0 ≤ (1 - ν) * c₂ + ν * c₁ := by
  have h1ν : 0 ≤ 1 - ν := by linarith
  constructor
  · exact add_nonneg (mul_nonneg h1ν hc₁) (mul_nonneg hν0 hc₂)
  · exact add_nonneg (mul_nonneg h1ν hc₂) (mul_nonneg hν0 hc₁)

end EarthScience
