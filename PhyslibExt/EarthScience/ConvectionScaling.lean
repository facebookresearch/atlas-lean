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
import Mathlib.Tactic.Positivity

/-!
# Geodynamics and convection scaling: the Rayleigh number

## i. Overview

For real parameters `g, α, ΔT, H, ν, κ`, the Rayleigh number of a fluid
layer, in its kinematic-viscosity form, is
`Ra = g * α * ΔT * H ^ 3 / (ν * κ)`. Here `α` is the thermal expansion
coefficient (inverse Kelvin), `ν` the kinematic viscosity, `κ` the
thermal diffusivity, `H` the layer depth, `ΔT` the temperature
difference, and `g` gravity. This file takes that formula as given and
proves algebraic facts about it. The Boussinesq equations and their
nondimensionalization are not formalized here, so the derivation of `Ra`
from them is not kernel-checked.

## ii. Key results

- `EarthScience.rayleigh_number_factorisation`: `Ra` is the product of
  `g * α * ΔT * H / ν` and `H ^ 2 / κ` (an algebraic identity).
- `EarthScience.rayleigh_number_pos`: `Ra > 0` for positive parameters.
- `EarthScience.rayleigh_number_zero_buoyancy`: `ΔT = 0` gives `Ra = 0`.

No universal critical Rayleigh number is claimed: onset is
boundary-dependent and remains separate.

## iii. Table of contents

- A. Rayleigh-number factorisation, positivity, and zero buoyancy

## iv. References

- S. Chandrasekhar, *Hydrodynamic and Hydromagnetic Stability*, Oxford
  University Press, 1961, Chapter II (the Rayleigh number of a fluid layer
  heated from below, in the form `g α β d ^ 4 / (κ ν)` with temperature
  gradient `β = ΔT / d` and depth `d = H`).
- D. L. Turcotte and G. Schubert, *Geodynamics*, 3rd ed., Cambridge
  University Press, 2014, Chapter 6 (thermal convection; the Rayleigh
  number is written there with the reference density `ρ₀` and the dynamic
  viscosity `μ = ρ₀ ν`).
- `div_pos`, `mul_pos` in Mathlib (field / order lemmas).

## A. Rayleigh-number factorisation, positivity, and zero buoyancy
-/

@[expose] public section

namespace EarthScience

/-- Algebraic factorization of the Rayleigh number: the product of
`g * α * ΔT * H / ν` and `H ^ 2 / κ` is `g * α * ΔT * H ^ 3 / (ν * κ)`.
This is an identity between the two expressions; it does not derive the
Rayleigh number from the Boussinesq equations. -/
theorem rayleigh_number_factorisation {g α ΔT H ν κ : ℝ} (hν : 0 < ν) (hκ : 0 < κ) :
    (g * α * ΔT * H / ν) * (H ^ 2 / κ) = g * α * ΔT * H ^ 3 / (ν * κ) := by
  field_simp

/-- The Rayleigh number is positive for positive `g, α, ΔT, H, ν, κ`. -/
theorem rayleigh_number_pos {g α ΔT H ν κ : ℝ} (hg : 0 < g) (hα : 0 < α)
    (hΔT : 0 < ΔT) (hH : 0 < H) (hν : 0 < ν) (hκ : 0 < κ) :
    0 < g * α * ΔT * H ^ 3 / (ν * κ) := by
  have hden : 0 < ν * κ := mul_pos hν hκ
  have hnum : 0 < g * α * ΔT * H ^ 3 := by positivity
  exact div_pos hnum hden

/-- Zero buoyancy (`ΔT = 0`) gives Rayleigh number `0`. -/
theorem rayleigh_number_zero_buoyancy {g α H ν κ : ℝ} (hν : 0 < ν) (hκ : 0 < κ) :
    g * α * 0 * H ^ 3 / (ν * κ) = 0 := by
  have _ := hν
  have _ := hκ
  simp

end EarthScience
