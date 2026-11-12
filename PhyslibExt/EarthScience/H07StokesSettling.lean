 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Stokes settling (H07)

## i. Overview

Under Stokes drag `6*pi*eta*a*v` and the stipulated spherical
displaced-fluid weight `(4/3)*pi*a^3*(rho_s - rho_f)*g`, the terminal
velocity is `v = 2*(rho_s - rho_f)*g*a^2/(9*eta)`, for `a, eta, g > 0`.
Here `a` is the radius, not the diameter; the creeping-flow
isolated-sphere regime is assumed, and no high-Reynolds drag claim is
made. The spherical buoyancy identity is stipulated until a geometric
proof is available.

## ii. Key results

- `EarthScience.h07_terminal_velocity`: force balance implies the terminal velocity formula.
- `EarthScience.h07_terminal_velocity_balances`: the formula velocity satisfies the force balance.
- `EarthScience.h07_neutral_buoyancy`: equal densities give zero velocity.
- `EarthScience.h07_buoyant_rises`: `rho_s < rho_f` gives negative (rising) velocity.

## iii. Table of contents

- A. Main results

## iv. References

- See the individual theorem docstrings.
-/

@[expose] public section

namespace EarthScience


set_option linter.unusedVariables false in
/-- Stokes settling: if the terminal velocity `v` balances Stokes drag
`6*pi*eta*a*v` against the stipulated spherical buoyant weight
`(4/3)*pi*a^3*(rho_s - rho_f)*g`, then
`v = 2*(rho_s - rho_f)*g*a^2/(9*eta)`. -/
theorem h07_terminal_velocity {a η g ρs ρf v : ℝ} (ha : 0 < a) (hη : 0 < η) (hg : 0 < g)
    (h : 6 * Real.pi * η * a * v = (4 / 3) * Real.pi * a ^ 3 * (ρs - ρf) * g) :
    v = 2 * (ρs - ρf) * g * a ^ 2 / (9 * η) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have ha' : a ≠ 0 := ne_of_gt ha
  have hη' : η ≠ 0 := ne_of_gt hη
  have h6 : (6 : ℝ) * Real.pi * η * a ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) hη') ha'
  have h9 : (9 : ℝ) * η ≠ 0 := mul_ne_zero (by norm_num) hη'
  have hv : v = ((4 / 3) * Real.pi * a ^ 3 * (ρs - ρf) * g) / (6 * Real.pi * η * a) := by
    rw [eq_div_iff h6]
    linear_combination h
  rw [hv, div_eq_div_iff h6 h9]
  ring

set_option linter.unusedVariables false in
/-- Stokes settling: the formula velocity satisfies the force balance. -/
theorem h07_terminal_velocity_balances {a η g ρs ρf : ℝ} (ha : 0 < a) (hη : 0 < η) (hg : 0 < g) :
    6 * Real.pi * η * a * (2 * (ρs - ρf) * g * a ^ 2 / (9 * η))
      = (4 / 3) * Real.pi * a ^ 3 * (ρs - ρf) * g := by
  have h9 : (9 : ℝ) * η ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hη)
  rw [← mul_div_assoc, div_eq_iff h9]
  ring

set_option linter.unusedVariables false in
/-- Neutral buoyancy: equal densities give zero terminal velocity. -/
theorem h07_neutral_buoyancy {a η g ρ : ℝ} (ha : 0 < a) (hη : 0 < η) (hg : 0 < g) :
    2 * (ρ - ρ) * g * a ^ 2 / (9 * η) = 0 := by
  simp

/-- Upward buoyant particle: if `rho_s < rho_f` the terminal velocity
is negative (rises). -/
theorem h07_buoyant_rises {a η g ρs ρf : ℝ} (ha : 0 < a) (hη : 0 < η) (hg : 0 < g)
    (h : ρs < ρf) :
    2 * (ρs - ρf) * g * a ^ 2 / (9 * η) < 0 := by
  have h1 : ρs - ρf < 0 := sub_neg.mpr h
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have h2 : (2 : ℝ) * (ρs - ρf) < 0 := mul_neg_of_pos_of_neg (by norm_num) h1
  have h3 : (2 : ℝ) * (ρs - ρf) * g < 0 := mul_neg_of_neg_of_pos h2 hg
  have hnum : (2 : ℝ) * (ρs - ρf) * g * a ^ 2 < 0 := mul_neg_of_neg_of_pos h3 ha2
  have hden : (0 : ℝ) < 9 * η := mul_pos (by norm_num) hη
  exact div_neg_of_neg_of_pos hnum hden


end EarthScience
