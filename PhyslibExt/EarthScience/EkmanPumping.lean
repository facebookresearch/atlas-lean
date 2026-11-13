/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ekman pumping: divergence of Ekman transport

For wind-stress components `tau0, tau1` (functions of horizontal
position `(x, y)`), density `rho0 > 0` and Coriolis parameter `f`,
the Ekman transport is `M = (tau1 / (rho0 * f), -tau0 / (rho0 * f))`.
Its divergence equals the vertical curl of the stress divided by
`rho0 * f`; that quotient is the Ekman pumping velocity (positive is
upwelling). With `rho0 > 0`, positive stress curl gives upwelling for
`f > 0` (northern hemisphere) and downwelling for `f < 0` (southern
hemisphere).

## i. Overview

The divergence identity follows from `HasDerivAt.div_const` and
`HasDerivAt.neg` applied to the partial derivatives of the stress.
The sign statement rewrites the divergence with the identity and uses
`div_pos` / `div_neg_of_pos_of_neg`.

## ii. Key results

- `EarthScience.ekman_pumping_divergence`: `div M = curl(tau) / (rho0 * f)`.
- `EarthScience.ekman_pumping_sign`: hemispheric sign of the pumping.

## iii. Table of contents

- A. Ekman pumping

## iv. References

- B. Cushman-Roisin and J.-M. Beckers, *Introduction to Geophysical
  Fluid Dynamics: Physical and Numerical Aspects*, 2nd ed., Academic
  Press (2011), Chapter 8: Ekman pumping from the divergence of the
  Ekman transport.
- `HasDerivAt.div_const`, `HasDerivAt.neg` in Mathlib.

## A. Ekman pumping
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Ekman pumping: for stress components `τ₀, τ₁` (functions of `(x, y)`),
density `ρ₀ > 0` and Coriolis parameter `f ≠ 0`, the divergence of the
Ekman transport `M = (τ₁ / (ρ₀ f), -τ₀ / (ρ₀ f))` equals the vertical
curl of the stress divided by `ρ₀ f`, i.e. the Ekman pumping velocity. -/
theorem ekman_pumping_divergence (τ₀ τ₁ : ℝ → ℝ → ℝ) (ρ₀ f x y : ℝ)
    (hρf : ρ₀ * f ≠ 0)
    (hτ₁x : HasDerivAt (fun x' => τ₁ x' y) (deriv (fun x' => τ₁ x' y) x) x)
    (hτ₀y : HasDerivAt (fun y' => τ₀ x y') (deriv (fun y' => τ₀ x y') y) y) :
    deriv (fun x' => τ₁ x' y / (ρ₀ * f)) x +
        deriv (fun y' => -(τ₀ x y' / (ρ₀ * f))) y =
      (deriv (fun x' => τ₁ x' y) x - deriv (fun y' => τ₀ x y') y) / (ρ₀ * f) := by
  have h1 : deriv (fun x' => τ₁ x' y / (ρ₀ * f)) x
      = deriv (fun x' => τ₁ x' y) x / (ρ₀ * f) :=
    (hτ₁x.div_const (ρ₀ * f)).deriv
  have h2 : deriv (fun y' => -(τ₀ x y' / (ρ₀ * f))) y
      = -(deriv (fun y' => τ₀ x y') y / (ρ₀ * f)) :=
    ((hτ₀y.div_const (ρ₀ * f)).neg).deriv
  rw [h1, h2, sub_div, sub_eq_add_neg]

/-- Hemispheric sign of Ekman pumping: with `ρ₀ > 0`, positive wind-stress
curl gives upwelling (`div M > 0`) for `f > 0` (northern hemisphere) and
downwelling (`div M < 0`) for `f < 0` (southern hemisphere). -/
theorem ekman_pumping_sign (τ₀ τ₁ : ℝ → ℝ → ℝ) (ρ₀ f x y : ℝ)
    (hρ : 0 < ρ₀) (hτ₁x : HasDerivAt (fun x' => τ₁ x' y) (deriv (fun x' => τ₁ x' y) x) x)
    (hτ₀y : HasDerivAt (fun y' => τ₀ x y') (deriv (fun y' => τ₀ x y') y) y)
    (hcurl : 0 < deriv (fun x' => τ₁ x' y) x - deriv (fun y' => τ₀ x y') y) :
    (0 < f →
      0 < deriv (fun x' => τ₁ x' y / (ρ₀ * f)) x +
        deriv (fun y' => -(τ₀ x y' / (ρ₀ * f))) y) ∧
    (f < 0 →
      deriv (fun x' => τ₁ x' y / (ρ₀ * f)) x +
        deriv (fun y' => -(τ₀ x y' / (ρ₀ * f))) y < 0) := by
  constructor
  · intro hf
    have hρf : ρ₀ * f ≠ 0 := ne_of_gt (mul_pos hρ hf)
    have hdiv := ekman_pumping_divergence τ₀ τ₁ ρ₀ f x y hρf hτ₁x hτ₀y
    rw [hdiv]
    exact div_pos hcurl (mul_pos hρ hf)
  · intro hf
    have hρf : ρ₀ * f ≠ 0 := ne_of_lt (mul_neg_of_pos_of_neg hρ hf)
    have hdiv := ekman_pumping_divergence τ₀ τ₁ ρ₀ f x y hρf hτ₁x hτ₀y
    rw [hdiv]
    exact div_neg_of_pos_of_neg hcurl (mul_neg_of_pos_of_neg hρ hf)

end EarthScience
