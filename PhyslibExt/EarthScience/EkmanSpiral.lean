/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Order.Group

/-!
# Ekman spiral profile

For constant eddy viscosity `nu` and Coriolis parameter `f`, the
steady half-space Ekman profile in the depth coordinate `zeta >= 0`
(downward from the surface) is
`u(zeta) = exp(-a zeta) cos(a zeta)`,
`v(zeta) = -exp(-a zeta) sin(a zeta)`, where `a` is the inverse Ekman
depth, `2 * nu * a^2 = f`. It satisfies the coupled Ekman ODEs
`nu * u'' = -f * v` and `nu * v'' = f * u`, the surface values
`u(0) = 1`, `v(0) = 0`, the surface shear `u'(0) = -a`, `v'(0) = -a`,
and, for `a > 0`, both components decay to `0` as `zeta -> infinity`.

Sign convention: these are the component equations
`nu * d²u/dz² = -f * v`, `nu * d²v/dz² = f * u` of the Ekman balance with
`z` upward, the convention of `PhyslibExt.EarthScience.EkmanLayers`
(`ρ₀ f k̂ × M = τ`, `f > 0` in the northern hemisphere); the downward
depth `zeta = -z` leaves second derivatives unchanged. For `nu > 0` the
relation `2 * nu * a^2 = f` forces `f ≥ 0`, so for `a > 0` this is the
northern-hemisphere spiral: the velocity
`exp(-a zeta) (cos(-a zeta), sin(-a zeta))` turns clockwise (to the
right) with depth, and the surface stress, which points along
`-(u'(0), v'(0)) = (a, a)` (stress `ρ₀ nu d(u, v)/dz` with `z` upward), is
at 45 degrees to the left of the surface current `(1, 0)`: the surface
current is 45 degrees to the right of the stress.

## i. Overview

The derivative formulas are proved with `HasDerivAt` lemmas for
`Real.exp`, `Real.cos`, and `Real.sin`. The ODEs follow from the
second-derivative formulas and the relation `2 * nu * a^2 = f`. Decay
follows by squeezing each component between `0` and the envelope
`exp(-a * zeta)`.

## ii. Key results

- `EarthScience.ekmanSpiralU`, `EarthScience.ekmanSpiralV`: the profile.
- `EarthScience.ekman_spiral_hasDerivAt_u`,
  `EarthScience.ekman_spiral_hasDerivAt_v`,
  `EarthScience.ekman_spiral_hasDerivAt_uPrime`,
  `EarthScience.ekman_spiral_hasDerivAt_vPrime`: first and second
  derivative formulas.
- `EarthScience.ekman_spiral_ode`: the Ekman ODEs.
- `EarthScience.ekman_spiral_boundary`: surface values and shear.
- `EarthScience.ekman_spiral_decay`: decay at depth.

## iii. Table of contents

- A. The Ekman spiral profile

## iv. References

- V. W. Ekman, *On the influence of the earth's rotation on
  ocean-currents*, Arkiv foer Matematik, Astronomi och Fysik 2 (11)
  (1905), 1-52: the Ekman spiral.
- B. Cushman-Roisin and J.-M. Beckers, *Introduction to Geophysical
  Fluid Dynamics: Physical and Numerical Aspects*, 2nd ed., Academic
  Press (2011), Chapter 8: the surface Ekman layer.

## A. The Ekman spiral profile
-/

@[expose] public section

namespace EarthScience

/-- Ekman spiral, depth coordinate `ζ ≥ 0` downward from the surface:
`u(ζ) = exp(-a ζ) cos(a ζ)`, with `a = 1 / Ekman depth`. -/
noncomputable def ekmanSpiralU (a : ℝ) : ℝ → ℝ :=
  fun ζ => Real.exp (-a * ζ) * Real.cos (a * ζ)

/-- Ekman spiral cross-component: `v(ζ) = -exp(-a ζ) sin(a ζ)`. -/
noncomputable def ekmanSpiralV (a : ℝ) : ℝ → ℝ :=
  fun ζ => -(Real.exp (-a * ζ) * Real.sin (a * ζ))

/-- First derivative of `u`: `-a * exp(-a ζ) * (cos(a ζ) + sin(a ζ))`. -/
noncomputable def ekmanSpiralUPrime (a : ℝ) : ℝ → ℝ :=
  fun ζ => -a * Real.exp (-a * ζ) * (Real.cos (a * ζ) + Real.sin (a * ζ))

/-- First derivative of `v`: `a * exp(-a ζ) * (sin(a ζ) - cos(a ζ))`. -/
noncomputable def ekmanSpiralVPrime (a : ℝ) : ℝ → ℝ :=
  fun ζ => a * Real.exp (-a * ζ) * (Real.sin (a * ζ) - Real.cos (a * ζ))

/-- Second derivative of `u`: `2 a² * exp(-a ζ) * sin(a ζ)`. -/
noncomputable def ekmanSpiralUSecond (a : ℝ) : ℝ → ℝ :=
  fun ζ => 2 * a ^ 2 * Real.exp (-a * ζ) * Real.sin (a * ζ)

/-- Second derivative of `v`: `2 a² * exp(-a ζ) * cos(a ζ)`. -/
noncomputable def ekmanSpiralVSecond (a : ℝ) : ℝ → ℝ :=
  fun ζ => 2 * a ^ 2 * Real.exp (-a * ζ) * Real.cos (a * ζ)

lemma ekman_spiral_hasDerivAt_u (a ζ : ℝ) :
    HasDerivAt (ekmanSpiralU a) (ekmanSpiralUPrime a ζ) ζ := by
  have hlin1 : HasDerivAt (fun ζ : ℝ => -a * ζ) (-a) ζ := by
    have h := (hasDerivAt_id (x := ζ)).const_mul (-a)
    simpa using h
  have hlin2 : HasDerivAt (fun ζ : ℝ => a * ζ) a ζ := by
    have h := (hasDerivAt_id (x := ζ)).const_mul a
    simpa using h
  have hexp := hlin1.exp
  have hcos := hlin2.cos
  have h := hexp.mul hcos
  unfold ekmanSpiralU ekmanSpiralUPrime
  convert h using 1
  ring

lemma ekman_spiral_hasDerivAt_v (a ζ : ℝ) :
    HasDerivAt (ekmanSpiralV a) (ekmanSpiralVPrime a ζ) ζ := by
  have hlin1 : HasDerivAt (fun ζ : ℝ => -a * ζ) (-a) ζ := by
    have h := (hasDerivAt_id (x := ζ)).const_mul (-a)
    simpa using h
  have hlin2 : HasDerivAt (fun ζ : ℝ => a * ζ) a ζ := by
    have h := (hasDerivAt_id (x := ζ)).const_mul a
    simpa using h
  have hexp := hlin1.exp
  have hsin := hlin2.sin
  have h := (hexp.mul hsin).neg
  unfold ekmanSpiralV ekmanSpiralVPrime
  convert h using 1
  ring

lemma ekman_spiral_hasDerivAt_uPrime (a ζ : ℝ) :
    HasDerivAt (ekmanSpiralUPrime a) (ekmanSpiralUSecond a ζ) ζ := by
  have hlin1 : HasDerivAt (fun ζ : ℝ => -a * ζ) (-a) ζ := by
    have h := (hasDerivAt_id (x := ζ)).const_mul (-a)
    simpa using h
  have hlin2 : HasDerivAt (fun ζ : ℝ => a * ζ) a ζ := by
    have h := (hasDerivAt_id (x := ζ)).const_mul a
    simpa using h
  have hexp := hlin1.exp
  have hcos := hlin2.cos
  have hsin := hlin2.sin
  have h := (hexp.const_mul (-a)).mul (hcos.add hsin)
  simp only [Pi.add_apply] at h
  unfold ekmanSpiralUPrime ekmanSpiralUSecond
  convert h using 1
  ring

lemma ekman_spiral_hasDerivAt_vPrime (a ζ : ℝ) :
    HasDerivAt (ekmanSpiralVPrime a) (ekmanSpiralVSecond a ζ) ζ := by
  have hlin1 : HasDerivAt (fun ζ : ℝ => -a * ζ) (-a) ζ := by
    have h := (hasDerivAt_id (x := ζ)).const_mul (-a)
    simpa using h
  have hlin2 : HasDerivAt (fun ζ : ℝ => a * ζ) a ζ := by
    have h := (hasDerivAt_id (x := ζ)).const_mul a
    simpa using h
  have hexp := hlin1.exp
  have hcos := hlin2.cos
  have hsin := hlin2.sin
  have h := (hexp.const_mul a).mul (hsin.sub hcos)
  simp only [Pi.sub_apply] at h
  unfold ekmanSpiralVPrime ekmanSpiralVSecond
  convert h using 1
  ring

/-- Ekman ODEs in depth coordinates, given `2 * ν * a² = f`:
`ν * u'' = -f * v` and `ν * v'' = f * u`, the sign convention of `EkmanLayers`. -/
theorem ekman_spiral_ode (a ν f ζ : ℝ) (h : 2 * ν * a ^ 2 = f) :
    ν * deriv (fun ζ => deriv (ekmanSpiralU a) ζ) ζ = -f * ekmanSpiralV a ζ ∧
      ν * deriv (fun ζ => deriv (ekmanSpiralV a) ζ) ζ = f * ekmanSpiralU a ζ := by
  have hderU : (fun ζ : ℝ => deriv (ekmanSpiralU a) ζ) = ekmanSpiralUPrime a := by
    ext ζ
    exact (ekman_spiral_hasDerivAt_u a ζ).deriv
  have hderV : (fun ζ : ℝ => deriv (ekmanSpiralV a) ζ) = ekmanSpiralVPrime a := by
    ext ζ
    exact (ekman_spiral_hasDerivAt_v a ζ).deriv
  have hderU2 := (ekman_spiral_hasDerivAt_uPrime a ζ).deriv
  have hderV2 := (ekman_spiral_hasDerivAt_vPrime a ζ).deriv
  rw [hderU, hderV, hderU2, hderV2]
  simp only [ekmanSpiralUSecond, ekmanSpiralVSecond, ekmanSpiralU, ekmanSpiralV]
  constructor
  · rw [← h]
    ring
  · rw [← h]
    ring

/-- Surface values and surface shear: `u(0) = 1`, `v(0) = 0`,
`u'(0) = -a`, `v'(0) = -a`. For `a > 0` and `ν > 0` the surface stress,
along `-(u'(0), v'(0)) = (a, a)`, is at 45° to the left of the surface
current `(1, 0)`. -/
theorem ekman_spiral_boundary (a : ℝ) :
    ekmanSpiralU a 0 = 1 ∧ ekmanSpiralV a 0 = 0 ∧
      ekmanSpiralUPrime a 0 = -a ∧ ekmanSpiralVPrime a 0 = -a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [ekmanSpiralU, ekmanSpiralV, ekmanSpiralUPrime, ekmanSpiralVPrime,
      mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, mul_one, add_zero,
      neg_zero, zero_sub, mul_neg]

/-- Helper: the exponential envelope `exp(-a * ζ)` tends to `0` as `ζ → ∞`. -/
private lemma ekman_exp_decay (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun ζ : ℝ => Real.exp (-a * ζ)) Filter.atTop (nhds 0) := by
  have hid : Filter.Tendsto (fun ζ : ℝ => ζ) Filter.atTop Filter.atTop :=
    Filter.tendsto_id
  have h1 : Filter.Tendsto (fun ζ : ℝ => a * ζ) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop ha hid
  have h2 : Filter.Tendsto (fun ζ : ℝ => -(a * ζ)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atBot_iff.mpr h1
  have heq : (fun ζ : ℝ => -(a * ζ)) =ᶠ[Filter.atTop] (fun ζ : ℝ => -a * ζ) :=
    Filter.Eventually.of_forall (fun ζ => by ring)
  have h3 : Filter.Tendsto (fun ζ : ℝ => -a * ζ) Filter.atTop Filter.atBot :=
    Filter.Tendsto.congr' heq h2
  exact Real.tendsto_exp_comp_nhds_zero.mpr h3

/-- Decay at depth: both components tend to `0` as `ζ → ∞`, for `a > 0`. -/
theorem ekman_spiral_decay (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (ekmanSpiralU a) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (ekmanSpiralV a) Filter.atTop (nhds 0) := by
  have hexp0 := ekman_exp_decay a ha
  constructor
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun ζ => abs_nonneg _) ?_ hexp0
    intro ζ
    change |ekmanSpiralU a ζ| ≤ Real.exp (-a * ζ)
    change |Real.exp (-a * ζ) * Real.cos (a * ζ)| ≤ Real.exp (-a * ζ)
    calc |Real.exp (-a * ζ) * Real.cos (a * ζ)|
        = |Real.exp (-a * ζ)| * |Real.cos (a * ζ)| := abs_mul _ _
      _ ≤ |Real.exp (-a * ζ)| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = Real.exp (-a * ζ) := by rw [abs_of_nonneg (Real.exp_nonneg _), mul_one]
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun ζ => abs_nonneg _) ?_ hexp0
    intro ζ
    change |ekmanSpiralV a ζ| ≤ Real.exp (-a * ζ)
    change |-(Real.exp (-a * ζ) * Real.sin (a * ζ))| ≤ Real.exp (-a * ζ)
    rw [abs_neg]
    calc |Real.exp (-a * ζ) * Real.sin (a * ζ)|
        = |Real.exp (-a * ζ)| * |Real.sin (a * ζ)| := abs_mul _ _
      _ ≤ |Real.exp (-a * ζ)| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = Real.exp (-a * ζ) := by rw [abs_of_nonneg (Real.exp_nonneg _), mul_one]

end EarthScience
