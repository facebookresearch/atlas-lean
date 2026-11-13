/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elastic seismic waves: P- and S-wave speeds and the plane wave

In homogeneous isotropic linear elasticity, a longitudinal plane wave has
`cP ^ 2 = (K + 4 * μ / 3) / ρ` and a transverse wave has `cS ^ 2 = μ / ρ`.

## i. Overview

`K` is the bulk modulus, `μ` the shear modulus, `ρ` the density
(`K, μ` in Pa, squared speeds in `L ^ 2 / T ^ 2`). The speeds are defined
by the square-root formulas; this file proves the squared formulas, that
P waves are faster than S waves for `K > 0`, `μ > 0`, `ρ > 0`, the first
and second time and space derivatives of a plane wave
`cos (k * x - ω * t)`, and that the dispersion relation
`ω ^ 2 = c ^ 2 * k ^ 2` makes the second time derivative equal `c ^ 2`
times the second space derivative. Small strain, no arbitrary anisotropy;
flux coefficients are separately scoped.

## ii. Key results

- `EarthScience.elastic_p_wave_speed_sq`: `cP ^ 2 = (K + 4 * μ / 3) / ρ`.
- `EarthScience.elastic_s_wave_speed_sq`: `cS ^ 2 = μ / ρ`.
- `EarthScience.elastic_p_faster_than_s`: P waves are faster than S waves.
- `EarthScience.hasDerivAt_planeWave_time`,
  `EarthScience.hasDerivAt_planeWave_time2`,
  `EarthScience.hasDerivAt_planeWave_space`,
  `EarthScience.hasDerivAt_planeWave_space2`: plane-wave derivatives.
- `EarthScience.planeWave_waveEquation`: dispersion implies the wave equation
  on second-derivative values.

## iii. Table of contents

- A. Wave speeds
- B. Plane-wave derivatives and the wave equation

## iv. References

- P. M. Shearer, *Introduction to Seismology*, 2nd ed., Cambridge University Press,
  2009, Chapter 3 (the seismic wave equation: squared P- and S-wave speeds of a
  homogeneous isotropic linear elastic solid, in Lamé form `(λ + 2 * μ) / ρ` and `μ / ρ`;
  `K = λ + 2 * μ / 3` gives the form used here).
- L. D. Landau, E. M. Lifshitz, *Theory of Elasticity*, 3rd ed., Pergamon, 1986, §22
  (elastic waves in isotropic bodies: longitudinal and transverse waves).
- `Real.sq_sqrt`, `Real.sqrt_lt_sqrt` in Mathlib.
- `HasDerivAt.cos` / `HasDerivAt.sin` in Mathlib.

## A. Wave speeds
-/

@[expose] public section

namespace EarthScience

/-- P-wave speed squared: `cP ^ 2 = (K + 4 * μ / 3) / ρ`, for `K ≥ 0`, `μ ≥ 0`, `ρ > 0`. -/
theorem elastic_p_wave_speed_sq {K μ ρ : ℝ} (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hρ : 0 < ρ) :
    (Real.sqrt ((K + 4 * μ / 3) / ρ)) ^ 2 = (K + 4 * μ / 3) / ρ := by
  exact Real.sq_sqrt (div_nonneg (by linarith) (le_of_lt hρ))

/-- S-wave speed squared: `cS ^ 2 = μ / ρ`. -/
theorem elastic_s_wave_speed_sq {μ ρ : ℝ} (hρ : 0 < ρ) (hμ : 0 ≤ μ) :
    (Real.sqrt (μ / ρ)) ^ 2 = μ / ρ := by
  exact Real.sq_sqrt (div_nonneg hμ (le_of_lt hρ))

/-- P waves are faster than S waves for `K > 0`, `μ > 0`, `ρ > 0`. -/
theorem elastic_p_faster_than_s {K μ ρ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (hK : 0 < K) :
    Real.sqrt (μ / ρ) < Real.sqrt ((K + 4 * μ / 3) / ρ) := by
  apply Real.sqrt_lt_sqrt (div_nonneg (le_of_lt hμ) (le_of_lt hρ))
  exact div_lt_div_of_pos_right (by linarith) hρ

/-! ## B. Plane-wave derivatives and the wave equation -/

private theorem hasDerivAt_inner_time {k ω x t : ℝ} :
    HasDerivAt (fun u : ℝ => k * x - ω * u) (-ω) t := by
  have hid : HasDerivAt (fun u : ℝ => ω * u) ω t := by
    simpa using (hasDerivAt_id' t).const_mul ω
  simpa using hid.const_sub (k * x)

private theorem hasDerivAt_inner_space {k ω x t : ℝ} :
    HasDerivAt (fun u : ℝ => k * u - ω * t) k x := by
  have hid : HasDerivAt (fun u : ℝ => k * u) k x := by
    simpa using (hasDerivAt_id' x).const_mul k
  simpa using hid.sub_const (ω * t)

/-- First time derivative of a longitudinal plane wave `cos (k * x - ω * t)`. -/
theorem hasDerivAt_planeWave_time {k ω x t : ℝ} :
    HasDerivAt (fun t => Real.cos (k * x - ω * t)) (ω * Real.sin (k * x - ω * t)) t := by
  have h := hasDerivAt_inner_time (k := k) (ω := ω) (x := x) (t := t)
  have hc := h.cos
  convert hc using 1
  ring

/-- Second time derivative of the plane wave. -/
theorem hasDerivAt_planeWave_time2 {k ω x t : ℝ} :
    HasDerivAt (fun t => ω * Real.sin (k * x - ω * t))
      (-ω ^ 2 * Real.cos (k * x - ω * t)) t := by
  have h := hasDerivAt_inner_time (k := k) (ω := ω) (x := x) (t := t)
  have hm := h.sin.const_mul ω
  convert hm using 1
  ring

/-- First space derivative of the plane wave. -/
theorem hasDerivAt_planeWave_space {k ω x t : ℝ} :
    HasDerivAt (fun x => Real.cos (k * x - ω * t)) (-k * Real.sin (k * x - ω * t)) x := by
  have h := hasDerivAt_inner_space (k := k) (ω := ω) (x := x) (t := t)
  have hc := h.cos
  convert hc using 1
  ring

/-- Second space derivative of the plane wave. -/
theorem hasDerivAt_planeWave_space2 {k ω x t : ℝ} :
    HasDerivAt (fun x => -k * Real.sin (k * x - ω * t))
      (-k ^ 2 * Real.cos (k * x - ω * t)) x := by
  have h := hasDerivAt_inner_space (k := k) (ω := ω) (x := x) (t := t)
  have hm := h.sin.const_mul (-k)
  convert hm using 1
  ring

/-- Dispersion relation `ω ^ 2 = c ^ 2 * k ^ 2` makes the second time
derivative equal `c ^ 2` times the second space derivative. -/
theorem planeWave_waveEquation {k ω c x t : ℝ} (hdisp : ω ^ 2 = c ^ 2 * k ^ 2) :
    -ω ^ 2 * Real.cos (k * x - ω * t) = c ^ 2 * (-k ^ 2 * Real.cos (k * x - ω * t)) := by
  rw [hdisp]
  ring

end EarthScience
