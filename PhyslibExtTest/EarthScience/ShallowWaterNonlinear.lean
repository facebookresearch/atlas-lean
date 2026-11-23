/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ShallowWaterNonlinear
import MathlibExt.Analysis.ODE.ContinuumBalances
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Nonlinear shallow-water checks

Consumers of `PhyslibExt.EarthScience.ShallowWaterNonlinear`: the public
shape of the conservative-primitive equivalence, the constant state (as an
example, not a public theorem), the same constant state read through the
equivalence, a concrete centred rarefaction (`h = 4 / 9`,
`∂ₓh = -4 / 9`) carried through the equivalence to primitive form, and a
dry-state instance at `g = 9.8`.

## i. Overview

These are elaboration and boundary checks, not new results. The
rarefaction point is `g = c₀ = t = 1`, `x = 0`, on the wet side of the
dry edge.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Public shapes and the constant state
- B. Rarefaction and dry-state controls

## iv. References

- `PhyslibExt.EarthScience.ShallowWaterNonlinear`
-/

open MathlibExt.Analysis.ODE.ContinuumBalances

/-- The public statement shape of the conservative-primitive equivalence. -/
example
    {h u : ℝ → ℝ → ℝ} {g t x hₜ hₓ uₜ uₓ : ℝ}
    (hpos : 0 < h t x)
    (dht : HasDerivAt (fun τ => h τ x) hₜ t)
    (dhx : HasDerivAt (h t) hₓ x)
    (dut : HasDerivAt (fun τ => u τ x) uₜ t)
    (dux : HasDerivAt (u t) uₓ x) :
    (localConservation h (fun τ y => h τ y * u τ y) 0 t x ∧
      localConservation (fun τ y => h τ y * u τ y)
        (fun τ y => h τ y * u τ y ^ 2 + g * h τ y ^ 2 / 2) 0 t x) ↔
    (hₜ + u t x * hₓ + h t x * uₓ = 0 ∧
      uₜ + u t x * uₓ + g * hₓ = 0) :=
  EarthScience.shallow_water_conservative_iff_primitive hpos dht dhx dut dux

/-- Constant state: a uniform depth `h₀` moving at uniform velocity
`u₀` satisfies both conservative equations at every point, for every
`g`. Its primitive partials are all zero. -/
example (g h₀ u₀ t x : ℝ) :
    localConservation (fun _ _ => h₀) (fun _ _ => h₀ * u₀) 0 t x ∧
      localConservation (fun _ _ => h₀ * u₀)
        (fun _ _ => h₀ * u₀ ^ 2 + g * h₀ ^ 2 / 2) 0 t x := by
  simp [localConservation, deriv_const]

example (g t x : ℝ) :
    (0 : ℝ) + 0 * 0 + 1 * 0 = 0 ∧ (0 : ℝ) + 0 * 0 + g * 0 = 0 := by
  have hiff := EarthScience.shallow_water_conservative_iff_primitive
    (h := fun _ _ => 1) (u := fun _ _ => 0) (g := g) (t := t) (x := x)
    (hₜ := 0) (hₓ := 0) (uₜ := 0) (uₓ := 0)
    (by norm_num) (hasDerivAt_const t 1) (hasDerivAt_const x 1)
    (hasDerivAt_const t 0) (hasDerivAt_const x 0)
  have hcons : localConservation (fun _ _ => (1 : ℝ)) (fun τ y => (1 : ℝ) * 0) 0 t x ∧
      localConservation (fun τ y => (1 : ℝ) * 0)
        (fun τ y => (1 : ℝ) * 0 ^ 2 + g * (1 : ℝ) ^ 2 / 2) 0 t x := by
    simp [localConservation, deriv_const]
  exact hiff.mp hcons

example :
    (localConservation (fun (τ : ℝ) (y : ℝ) => (2 * 1 - y / τ) ^ 2 / (9 * 1))
        (fun (τ : ℝ) (y : ℝ) => (2 * 1 - y / τ) ^ 2 / (9 * 1) *
          (2 * (y / τ + 1) / 3)) 0 1 0 ∧
      localConservation
        (fun (τ : ℝ) (y : ℝ) => (2 * 1 - y / τ) ^ 2 / (9 * 1) *
          (2 * (y / τ + 1) / 3))
        (fun (τ : ℝ) (y : ℝ) => (2 * 1 - y / τ) ^ 2 / (9 * 1) *
            (2 * (y / τ + 1) / 3) ^ 2 +
          1 * ((2 * 1 - y / τ) ^ 2 / (9 * 1)) ^ 2 / 2) 0 1 0) ∧
    (0 : ℝ) < (2 * 1 - 0 / 1) ^ 2 / (9 * 1) ∧
    deriv (fun (y : ℝ) => (2 * 1 - y / 1) ^ 2 / (9 * 1)) 0 ≠ 0 :=
  EarthScience.shallow_water_conservative_rarefaction (g := 1) (c₀ := 1) (t := 1) (x := 0)
    (by norm_num) (by norm_num) (by norm_num)

example : (2 * 1 - 0 / 1 : ℝ) ^ 2 / (9 * 1) = 4 / 9 := by norm_num

example : deriv (fun (y : ℝ) => (2 * 1 - y / 1) ^ 2 / (9 * 1)) 0 = -4 / 9 := by
  have s1 : HasDerivAt (fun (y : ℝ) => y / 1) (1 / 1) 0 :=
    (hasDerivAt_id (0 : ℝ)).div_const 1
  have h1 : HasDerivAt (fun (y : ℝ) => 2 * 1 - y / 1) (0 - 1 / 1) 0 :=
    (hasDerivAt_const (0 : ℝ) (2 * 1)).sub s1
  have hH : HasDerivAt (fun (y : ℝ) => (2 * 1 - y / 1) ^ 2 / (9 * 1)) (-4 / 9) 0 := by
    have h2 := (h1.pow 2).div_const (9 * 1)
    convert h2 using 1
    norm_num
  exact hH.deriv

example :
    deriv (fun (τ : ℝ) => (2 * 1 - 0 / τ) ^ 2 / (9 * 1)) 1 +
        (2 * (0 / 1 + 1) / 3) *
          deriv (fun (y : ℝ) => (2 * 1 - y / 1) ^ 2 / (9 * 1)) 0 +
        ((2 * 1 - 0 / 1) ^ 2 / (9 * 1)) *
          deriv (fun (y : ℝ) => 2 * (y / 1 + 1) / 3) 0 = 0 ∧
      deriv (fun (τ : ℝ) => 2 * (0 / τ + 1) / 3) 1 +
        (2 * (0 / 1 + 1) / 3) *
          deriv (fun (y : ℝ) => 2 * (y / 1 + 1) / 3) 0 +
        1 * deriv (fun (y : ℝ) => (2 * 1 - y / 1) ^ 2 / (9 * 1)) 0 = 0 := by
  have h3 := EarthScience.shallow_water_conservative_rarefaction
    (g := 1) (c₀ := 1) (t := 1) (x := 0) (by norm_num) (by norm_num) (by norm_num)
  have dht : DifferentiableAt ℝ (fun (τ : ℝ) => (2 * 1 - 0 / τ) ^ 2 / (9 * 1)) 1 := by
    fun_prop (disch := norm_num)
  have dhx : DifferentiableAt ℝ (fun (y : ℝ) => (2 * 1 - y / 1) ^ 2 / (9 * 1)) 0 := by
    fun_prop
  have dut : DifferentiableAt ℝ (fun (τ : ℝ) => 2 * (0 / τ + 1) / 3) 1 := by
    fun_prop (disch := norm_num)
  have dux : DifferentiableAt ℝ (fun (y : ℝ) => 2 * (y / 1 + 1) / 3) 0 := by
    fun_prop
  have hiff := EarthScience.shallow_water_conservative_iff_primitive
    (h := fun (τ : ℝ) (y : ℝ) => (2 * 1 - y / τ) ^ 2 / (9 * 1))
    (u := fun (τ : ℝ) (y : ℝ) => 2 * (y / τ + 1) / 3) (g := 1) (t := 1) (x := 0)
    h3.2.1 dht.hasDerivAt dhx.hasDerivAt dut.hasDerivAt dux.hasDerivAt
  exact hiff.mp h3.1

example (t x : ℝ) : ∃ (h u : ℝ → ℝ → ℝ) (hₜ hₓ uₜ uₓ : ℝ), h t x = 0 ∧
      HasDerivAt (fun τ => h τ x) hₜ t ∧ HasDerivAt (h t) hₓ x ∧
      HasDerivAt (fun τ => u τ x) uₜ t ∧ HasDerivAt (u t) uₓ x ∧
      (localConservation h (fun τ y => h τ y * u τ y) 0 t x ∧
        localConservation (fun τ y => h τ y * u τ y)
          (fun τ y => h τ y * u τ y ^ 2 + (9.8 : ℝ) * h τ y ^ 2 / 2) 0 t x) ∧
      ¬ (hₜ + u t x * hₓ + h t x * uₓ = 0 ∧
        uₜ + u t x * uₓ + (9.8 : ℝ) * hₓ = 0) :=
  EarthScience.exists_dry_conservative_not_primitive (9.8 : ℝ) t x
