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
import Mathlib.Tactic.Ring

/-!
# Top and bottom pressure balance on a rectangular prism

## i. Overview

For a vertical rectangular prism of horizontal area `A` and submerged
height `h` in a uniform fluid, with top pressure `P0` and bottom pressure
`P0 + rho*g*h`, the bottom-minus-top force is `rho*g*A*h`. These are
algebraic identities in the given face pressures: each horizontal face
force is taken to be its pressure times `A`, and the vertical side faces
are assumed to carry no vertical force. No pressure field is integrated
over the surface; a general shape requires a proved flux theorem.

## ii. Key results

- `EarthScience.buoyancy_force`: bottom-minus-top force is `rho*g*A*h`.
- `EarthScience.pressure_difference`: bottom-minus-top pressure is `rho*g*h`.
- `EarthScience.weight_eq_buoyancy_at_ratio_height`: the algebraic identity
  `rho_b*(A*H)*g = rho*g*A*((rho_b/rho)*H)`, not a flotation theorem.

## iii. Table of contents

- A. Main results

## iv. References

- See the individual theorem docstrings.
-/

@[expose] public section

namespace EarthScience


/-- Top/bottom pressure balance for a vertical rectangular prism: with
top pressure `P0` and bottom pressure `P0 + rho*g*h`, each acting on
area `A`, the bottom-minus-top force is `rho*g*A*h`. -/
theorem buoyancy_force {P0 ρ g A h : ℝ} :
    (P0 + ρ * g * h) * A - P0 * A = ρ * g * A * h := by
  ring

/-- With top pressure `P0` and bottom pressure `P0 + rho*g*h`, bottom
pressure minus top pressure is `rho*g*h`. -/
theorem pressure_difference {P0 ρ g h : ℝ} :
    (P0 + ρ * g * h) - P0 = ρ * g * h := by
  ring

/-- Algebraic identity: for a prism of total height `H`, area `A` and body
density `rho_b` in fluid of density `rho > 0`, the weight `rho_b*(A*H)*g`
equals `rho*g*A*h` at `h = (rho_b/rho)*H`. This is a division identity,
not a flotation theorem: without `0 ≤ rho_b ≤ rho`, `h` need not lie in
`[0, H]`. -/
theorem weight_eq_buoyancy_at_ratio_height {ρ ρb g A H : ℝ} (hρ : 0 < ρ) :
    ρb * (A * H) * g = ρ * g * A * ((ρb / ρ) * H) := by
  have hρ' : ρ ≠ 0 := ne_of_gt hρ
  field_simp


end EarthScience
