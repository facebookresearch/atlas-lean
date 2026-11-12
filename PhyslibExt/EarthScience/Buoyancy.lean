 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integral buoyancy and flotation

## i. Overview

For a vertical rectangular prism of horizontal area `A` and submerged
height `h` in a uniform fluid, with top pressure `P0` and bottom pressure
`P0 + rho*g*h`, the bottom-minus-top hydrostatic force is `rho*g*A*h`.
This is the prism case only; a general shape requires a proved flux
theorem. Pressure on vertical faces has no vertical component.

## ii. Key results

- `EarthScience.buoyancy_force`: bottom-minus-top force is `rho*g*A*h`.
- `EarthScience.pressure_difference`: bottom-minus-top pressure is `rho*g*h`.
- `EarthScience.neutral_buoyancy`: neutral-buoyancy submerged height balances weight.
- `EarthScience.witness`: `rho = 1000, g = 10, A = 2, h = 3` gives `60000`.

## iii. Table of contents

- A. Main results

## iv. References

- See the individual theorem docstrings.
-/

@[expose] public section

namespace EarthScience


/-- Hydrostatic buoyancy for a vertical rectangular prism: with top
pressure `P0` and bottom pressure `P0 + rho*g*h`, the bottom-minus-top
vertical force is `rho*g*A*h`. -/
theorem buoyancy_force {P0 ρ g A h : ℝ} :
    (P0 + ρ * g * h) * A - P0 * A = ρ * g * A * h := by
  ring

/-- Hydrostatic pressure grows linearly with depth: bottom pressure
minus top pressure is `rho*g*h`. -/
theorem pressure_difference {P0 ρ g h : ℝ} :
    (P0 + ρ * g * h) - P0 = ρ * g * h := by
  ring

/-- Neutral buoyancy: a prism of total height `H` and body density
`rho_b` floating with submerged height `h = (rho_b/rho)*H` has body
weight equal to the buoyancy force `rho*g*A*h`. -/
theorem neutral_buoyancy {ρ ρb g A H : ℝ} (hρ : 0 < ρ) :
    ρb * (A * H) * g = ρ * g * A * ((ρb / ρ) * H) := by
  have hρ' : ρ ≠ 0 := ne_of_gt hρ
  field_simp

/-- Non-vacuous witness: `rho = 1000, g = 10, A = 2, h = 3` gives
buoyancy force `60000`. -/
theorem witness :
    (0 + (1000 : ℝ) * 10 * 3) * 2 - 0 * 2 = 60000 := by
  norm_num


end EarthScience
