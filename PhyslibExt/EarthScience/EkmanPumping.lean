/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.EkmanLayers
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

For a wind-stress field `τ (x, y) : Fin 3 → ℝ` over horizontal position
`(x, y)`, density `ρ₀ > 0` and constant Coriolis parameter `f`
(f-plane), the Ekman transport at `(x, y)` is
`M (x, y) = ekmanTransport ρ₀ f (τ x y)`, the canonical transport of
`PhyslibExt.EarthScience.EkmanLayers`, with horizontal components
`M 0 = τ 1 / (ρ₀ f)` and `M 1 = -τ 0 / (ρ₀ f)`. Its horizontal
divergence `∂ₓ (M 0) + ∂ᵧ (M 1)` equals the vertical curl
`∂ₓ (τ 1) - ∂ᵧ (τ 0)` of the stress divided by `ρ₀ f`. By mass
continuity this divergence is the vertical velocity at the base of the
Ekman layer, the Ekman pumping velocity (positive is upwelling); that
continuity step is the physical reading of the result and is not
formalized here. With `ρ₀ > 0`, positive stress curl gives positive
divergence (upwelling) for `f > 0` (northern hemisphere) and negative
divergence (downwelling) for `f < 0` (southern hemisphere).

## i. Overview

The components of `ekmanTransport` unfold to `τ 1 / (ρ₀ f)` and
`-(τ 0 / (ρ₀ f))`, so the divergence identity follows from
`HasDerivAt.div_const` and `HasDerivAt.neg` applied to the partial
derivatives of the stress. The sign statement rewrites the divergence
with the identity and uses `div_pos` / `div_neg_of_pos_of_neg`.

## ii. Key results

- `EarthScience.ekman_pumping_divergence`: the divergence of
  `ekmanTransport ρ₀ f (τ x y)` is `curl(τ) / (ρ₀ f)`.
- `EarthScience.ekman_pumping_sign`: hemispheric sign of that divergence.

## iii. Table of contents

- A. Ekman pumping

## iv. References

- B. Cushman-Roisin and J.-M. Beckers, *Introduction to Geophysical
  Fluid Dynamics: Physical and Numerical Aspects*, 2nd ed., Academic
  Press (2011), Chapter 8: Ekman pumping from the divergence of the
  Ekman transport.
- `EarthScience.ekmanTransport` in `PhyslibExt.EarthScience.EkmanLayers`.
- `HasDerivAt.div_const`, `HasDerivAt.neg` in Mathlib.

## A. Ekman pumping
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Ekman pumping: for a wind-stress field `τ (x, y)`, density `ρ₀` and
constant Coriolis parameter `f` with `ρ₀ f ≠ 0`, the horizontal divergence
`∂ₓ (M 0) + ∂ᵧ (M 1)` of the Ekman transport
`M (x, y) = ekmanTransport ρ₀ f (τ x y)` equals the vertical curl
`∂ₓ (τ 1) - ∂ᵧ (τ 0)` of the stress divided by `ρ₀ f`. -/
theorem ekman_pumping_divergence (τ : ℝ → ℝ → Fin 3 → ℝ) (ρ₀ f x y : ℝ)
    (hρf : ρ₀ * f ≠ 0)
    (hτ₁x : HasDerivAt (fun x' => τ x' y 1) (deriv (fun x' => τ x' y 1) x) x)
    (hτ₀y : HasDerivAt (fun y' => τ x y' 0) (deriv (fun y' => τ x y' 0) y) y) :
    deriv (fun x' => ekmanTransport ρ₀ f (τ x' y) 0) x +
        deriv (fun y' => ekmanTransport ρ₀ f (τ x y') 1) y =
      (deriv (fun x' => τ x' y 1) x - deriv (fun y' => τ x y' 0) y) / (ρ₀ * f) := by
  have h1 : deriv (fun x' => ekmanTransport ρ₀ f (τ x' y) 0) x
      = deriv (fun x' => τ x' y 1) x / (ρ₀ * f) :=
    (hτ₁x.div_const (ρ₀ * f)).deriv
  have h2 : deriv (fun y' => ekmanTransport ρ₀ f (τ x y') 1) y
      = -(deriv (fun y' => τ x y' 0) y / (ρ₀ * f)) :=
    ((hτ₀y.div_const (ρ₀ * f)).neg).deriv
  rw [h1, h2, sub_div, sub_eq_add_neg]

/-- Hemispheric sign of Ekman pumping: with `ρ₀ > 0`, positive wind-stress
curl gives a positive divergence of the Ekman transport
`M (x, y) = ekmanTransport ρ₀ f (τ x y)` (upwelling) for `f > 0` (northern
hemisphere) and a negative divergence (downwelling) for `f < 0` (southern
hemisphere). -/
theorem ekman_pumping_sign (τ : ℝ → ℝ → Fin 3 → ℝ) (ρ₀ f x y : ℝ)
    (hρ : 0 < ρ₀) (hτ₁x : HasDerivAt (fun x' => τ x' y 1) (deriv (fun x' => τ x' y 1) x) x)
    (hτ₀y : HasDerivAt (fun y' => τ x y' 0) (deriv (fun y' => τ x y' 0) y) y)
    (hcurl : 0 < deriv (fun x' => τ x' y 1) x - deriv (fun y' => τ x y' 0) y) :
    (0 < f →
      0 < deriv (fun x' => ekmanTransport ρ₀ f (τ x' y) 0) x +
        deriv (fun y' => ekmanTransport ρ₀ f (τ x y') 1) y) ∧
    (f < 0 →
      deriv (fun x' => ekmanTransport ρ₀ f (τ x' y) 0) x +
        deriv (fun y' => ekmanTransport ρ₀ f (τ x y') 1) y < 0) := by
  constructor
  · intro hf
    have hρf : ρ₀ * f ≠ 0 := ne_of_gt (mul_pos hρ hf)
    have hdiv := ekman_pumping_divergence τ ρ₀ f x y hρf hτ₁x hτ₀y
    rw [hdiv]
    exact div_pos hcurl (mul_pos hρ hf)
  · intro hf
    have hρf : ρ₀ * f ≠ 0 := ne_of_lt (mul_neg_of_pos_of_neg hρ hf)
    have hdiv := ekman_pumping_divergence τ ρ₀ f x y hρf hτ₁x hτ₀y
    rw [hdiv]
    exact div_neg_of_pos_of_neg hcurl (mul_neg_of_pos_of_neg hρ hf)

end EarthScience
