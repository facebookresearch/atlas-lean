/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rossby-wave dispersion formula: algebraic forms

The linearized barotropic vorticity equation on a beta-plane, about a
uniform zonal flow `U`, for a perturbation streamfunction `psi(x, y, t)`
(`x` east, `y` north, `beta = df/dy`) is
`(∂/∂t + U * ∂/∂x) (∇² psi) + beta * ∂psi/∂x = 0`. Substituting the plane
wave `psi = Re (Psi * exp (i * (k * x + l * y - omega * t)))` gives the
Rossby-wave dispersion relation `(omega - U * k) * (k^2 + l^2) = -beta * k`,
i.e. `omega = U * k - beta * k / (k^2 + l^2)` for `k^2 + l^2 ≠ 0`. With this
sign convention the intrinsic phase speed `omega / k - U = -beta / (k^2 + l^2)`
is westward for `beta > 0`.

This file does not formalize the vorticity equation, the plane-wave
substitution, or that derivation: every result assumes the dispersion
formula and proves algebraic facts about it. Clearing the denominator
`k^2 + l^2` relates the solved and product forms, the product form
determines `omega`, and for `k ≠ 0` dividing by `k` gives the phase speed;
`beta = 0` gives pure advection `omega = U * k`. This is a model dispersion
identity, not nonlinear existence or stability.

## i. Overview

The dispersion relation and its solved form are related by clearing
the denominator `k^2 + l^2`; dividing by `k` gives the phase speed.

## ii. Key results

- `EarthScience.rossby_dispersion_clear_denom`: the solved formula implies the product form.
- `EarthScience.rossby_dispersion_iff`: the product form determines `omega` uniquely.
- `EarthScience.rossby_phase_speed`: phase speed formula.

## iii. Table of contents

- A. Rossby dispersion formula

## iv. References

- J. R. Holton, *An Introduction to Dynamic Meteorology*, 4th ed.,
  Elsevier Academic Press (2004), Chapter 7 (Atmospheric Oscillations:
  Linear Perturbation Theory), Section 7.7.1 (Free Barotropic Rossby
  Waves): the perturbation vorticity equation (7.90), the plane-wave
  solution `Re (Psi * exp (i * (k * x + l * y - ν * t)))`, the dispersion
  relation (7.91) and the phase speed (7.92); Holton writes `ν` for `omega`
  and `ū` for `U`.
- `field_simp` / `linear_combination` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Clearing the denominator of the Rossby dispersion formula (algebra only;
no plane mode or vorticity equation is involved): if
`omega = U * k - beta * k / (k^2 + l^2)` and `k^2 + l^2 ≠ 0`, then
`(omega - U * k) * (k^2 + l^2) = -beta * k`. -/
theorem rossby_dispersion_clear_denom {U beta k l omega : ℝ} (h : k ^ 2 + l ^ 2 ≠ 0)
    (homega : omega = U * k - beta * k / (k ^ 2 + l ^ 2)) :
    (omega - U * k) * (k ^ 2 + l ^ 2) = -beta * k := by
  rw [homega]
  field_simp
  ring

/-- The dispersion relation determines `omega` uniquely: for
`k^2 + l^2 ≠ 0`, `omega = U * k - beta * k / (k^2 + l^2)` iff
`(omega - U * k) * (k^2 + l^2) = -beta * k`. -/
theorem rossby_dispersion_iff {U beta k l omega : ℝ} (h : k ^ 2 + l ^ 2 ≠ 0) :
    omega = U * k - beta * k / (k ^ 2 + l ^ 2) ↔
      (omega - U * k) * (k ^ 2 + l ^ 2) = -beta * k := by
  constructor
  · intro homega
    exact rossby_dispersion_clear_denom h homega
  · intro hmul
    have heq : omega - U * k = -beta * k / (k ^ 2 + l ^ 2) := by
      rw [eq_div_iff h]
      linarith
    linear_combination heq

/-- Phase speed: for `k ≠ 0`, `omega / k = U - beta / (k^2 + l^2)`;
in particular `beta = 0` gives `omega = U * k` (pure advection). Over `ℝ`,
`k ≠ 0` already gives `k^2 + l^2 ≠ 0`. -/
theorem rossby_phase_speed {U beta k l omega : ℝ} (hk : k ≠ 0)
    (homega : omega = U * k - beta * k / (k ^ 2 + l ^ 2)) :
    omega / k = U - beta / (k ^ 2 + l ^ 2) := by
  have h : k ^ 2 + l ^ 2 ≠ 0 := by positivity
  rw [homega]
  field_simp


end EarthScience
