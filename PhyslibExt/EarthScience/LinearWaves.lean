/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves

/-!
# Linear waves and oscillations

The travelling wave `u(t, x) = A cos (k x - c k t)` solves the wave equation
`u_tt = c^2 u_xx`. The second time derivative is `-(c k)^2 u` and the
second space derivative is `-k^2 u`; the wave equation follows by
comparing them.

## i. Overview

The wave is the repository's plane-wave model
`PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.planeWave A k omega x t
= A * cos (k * x - omega * t)` with `omega = c * k`, i.e. `planeWave A k (c * k)`.
Derivatives are iterated `deriv` with the other variable held fixed. The
first-derivative helpers are stated as separate lemmas so the second
derivatives can be computed by rewriting the inner derivative. Zero
amplitude and zero wavenumber are allowed.

## ii. Key results

- `EarthScience.wave_second_deriv_time`: the second time derivative.
- `EarthScience.wave_second_deriv_space`: the second space derivative.
- `EarthScience.wave_travelling_solves`: `u_tt = c^2 u_xx`.

## iii. Table of contents

- A. First and second derivatives of the travelling wave

## iv. References

- `PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.planeWave`, the
  plane-wave model.
- `HasDerivAt.cos` / `HasDerivAt.sin` in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean` (Mathlib).

## A. First and second derivatives of the travelling wave
-/

@[expose] public section

namespace EarthScience

open PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves (planeWave)

/-- First time derivative of the travelling wave `planeWave A k (c * k)`. -/
theorem wave_first_deriv_time (A k c x t : ℝ) :
    deriv (fun t' => planeWave A k (c * k) x t') t =
      A * (-Real.sin (k * x - c * k * t)) * (-(c * k)) := by
  unfold planeWave
  have hlin : HasDerivAt (fun t' : ℝ => k * x - c * k * t') (-(c * k)) t := by
    have h1 : HasDerivAt (fun t' : ℝ => t') 1 t := hasDerivAt_id' t
    have h2 := h1.const_mul (c * k)
    have h3 := h2.const_sub (k * x)
    simpa using h3
  have hcos := hlin.cos
  have hmul := hcos.const_mul A
  have h : deriv (fun t' : ℝ => A * Real.cos (k * x - c * k * t')) t =
      A * (-Real.sin (k * x - c * k * t) * (-(c * k))) := hmul.deriv
  linear_combination h

/-- First space derivative of the travelling wave `planeWave A k (c * k)`. -/
theorem wave_first_deriv_space (A k c x t : ℝ) :
    deriv (fun x' => planeWave A k (c * k) x' t) x =
      A * (-Real.sin (k * x - c * k * t)) * k := by
  unfold planeWave
  have hlin : HasDerivAt (fun x' : ℝ => k * x' - c * k * t) k x := by
    have h1 : HasDerivAt (fun x' : ℝ => x') 1 x := hasDerivAt_id' x
    have h2 := h1.const_mul k
    have h3 := h2.sub_const (c * k * t)
    simpa using h3
  have hcos := hlin.cos
  have hmul := hcos.const_mul A
  have h : deriv (fun x' : ℝ => A * Real.cos (k * x' - c * k * t)) x =
      A * (-Real.sin (k * x - c * k * t) * k) := hmul.deriv
  linear_combination h

/-- Second time derivative of the travelling wave
`u(t, x) = planeWave A k (c * k) x t = A cos (k x - c k t)` at fixed `x`. -/
theorem wave_second_deriv_time (A k c x t : ℝ) :
    deriv (fun t => deriv (fun t' => planeWave A k (c * k) x t') t) t =
      -(c * k) ^ 2 * planeWave A k (c * k) x t := by
  unfold planeWave
  have h1 : ∀ s : ℝ, deriv (fun t' => A * Real.cos (k * x - c * k * t')) s =
      A * (-Real.sin (k * x - c * k * s)) * (-(c * k)) :=
    fun s => wave_first_deriv_time A k c x s
  have hfun : (fun t => deriv (fun t' => A * Real.cos (k * x - c * k * t')) t) =
      (fun t => A * (-Real.sin (k * x - c * k * t)) * (-(c * k))) := funext h1
  rw [hfun]
  have hlin : HasDerivAt (fun t' : ℝ => k * x - c * k * t') (-(c * k)) t := by
    have g1 : HasDerivAt (fun t' : ℝ => t') 1 t := hasDerivAt_id' t
    have g2 := g1.const_mul (c * k)
    have g3 := g2.const_sub (k * x)
    simpa using g3
  have hsin := hlin.sin
  have hneg := hsin.neg
  have hmul := hneg.const_mul A
  have hmc := hmul.mul_const (-(c * k))
  have h : deriv (fun t => A * (-Real.sin (k * x - c * k * t)) * (-(c * k))) t =
      (A * (-(Real.cos (k * x - c * k * t) * (-(c * k))))) * (-(c * k)) :=
    hmc.deriv
  linear_combination h

/-- Second space derivative of the travelling wave
`u(t, x) = planeWave A k (c * k) x t = A cos (k x - c k t)` at fixed `t`. -/
theorem wave_second_deriv_space (A k c x t : ℝ) :
    deriv (fun x => deriv (fun x' => planeWave A k (c * k) x' t) x) x =
      -(k ^ 2) * planeWave A k (c * k) x t := by
  unfold planeWave
  have h1 : ∀ s : ℝ, deriv (fun x' => A * Real.cos (k * x' - c * k * t)) s =
      A * (-Real.sin (k * s - c * k * t)) * k :=
    fun s => wave_first_deriv_space A k c s t
  have hfun : (fun x => deriv (fun x' => A * Real.cos (k * x' - c * k * t)) x) =
      (fun x => A * (-Real.sin (k * x - c * k * t)) * k) := funext h1
  rw [hfun]
  have hlin : HasDerivAt (fun x' : ℝ => k * x' - c * k * t) k x := by
    have g1 : HasDerivAt (fun x' : ℝ => x') 1 x := hasDerivAt_id' x
    have g2 := g1.const_mul k
    have g3 := g2.sub_const (c * k * t)
    simpa using g3
  have hsin := hlin.sin
  have hneg := hsin.neg
  have hmul := hneg.const_mul A
  have hmc := hmul.mul_const k
  have h : deriv (fun x => A * (-Real.sin (k * x - c * k * t)) * k) x =
      (A * (-(Real.cos (k * x - c * k * t) * k))) * k := hmc.deriv
  linear_combination h

/-- The travelling wave `u(t, x) = planeWave A k (c * k) x t = A cos (k x - c k t)`
solves the wave equation `u_tt = c² u_xx`: the second time derivative equals
`c²` times the second space derivative. -/
theorem wave_travelling_solves (A k c x t : ℝ) :
    deriv (fun t => deriv (fun t' => planeWave A k (c * k) x t') t) t =
      c ^ 2 * deriv (fun x => deriv (fun x' => planeWave A k (c * k) x' t) x) x := by
  rw [wave_second_deriv_time, wave_second_deriv_space]
  ring

end EarthScience
