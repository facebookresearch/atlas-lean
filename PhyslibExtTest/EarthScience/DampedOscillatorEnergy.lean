/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.DampedOscillatorEnergy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Damped oscillator energy checks

Concrete consumers of `PhyslibExt.EarthScience.DampedOscillatorEnergy`.

## i. Overview

The decaying solution `x(t) = exp(-t)` satisfies
`x'' + 2 x' + x = 0` (so `γ = 1`, `ω₀ = 1`): its energy is `exp(-2t)`,
nonincreasing. The boundary case `γ = 0` with constant displacement has
constant energy.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete and boundary checks

## iv. References

- `PhyslibExt.EarthScience.DampedOscillatorEnergy`
-/

/-- First-derivative data for `x(t) = exp(-t)`. -/
example : ∀ t, HasDerivAt (fun τ => Real.exp (-τ)) (deriv (fun τ => Real.exp (-τ)) t) t := by
  intro t
  have h : HasDerivAt (fun τ => Real.exp (-τ)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  rw [h.deriv]
  exact h

/-- Second-derivative data for `x(t) = exp(-t)`. -/
example : ∀ t, HasDerivAt (deriv (fun τ => Real.exp (-τ)))
    (deriv (deriv (fun τ => Real.exp (-τ))) t) t := by
  intro t
  have h1 : HasDerivAt (fun τ => Real.exp (-τ)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have hderiv : deriv (fun τ => Real.exp (-τ)) = -fun τ => Real.exp (-τ) := by
    funext τ
    have h : HasDerivAt (fun τ => Real.exp (-τ)) (-Real.exp (-τ)) τ := by
      simpa using (hasDerivAt_neg τ).exp
    exact h.deriv
  rw [hderiv]
  have h2 : HasDerivAt (-fun τ => Real.exp (-τ)) (Real.exp (-t)) t := by
    simpa using ((hasDerivAt_neg t).exp).neg
  rw [h2.deriv]
  exact h2

/-- Concrete energy values for `x(t) = exp(-t)`, `γ = 1`, `ω₀ = 1`:
energy `1` at `t = 0` and `exp(-2)` at `t = 1`, so it decreases. -/
example : (fun t => (deriv (fun τ => Real.exp (-τ)) t) ^ 2 / 2 +
    (1 : ℝ) ^ 2 * (Real.exp (-t)) ^ 2 / 2) 0 = 1 ∧
    (fun t => (deriv (fun τ => Real.exp (-τ)) t) ^ 2 / 2 +
    (1 : ℝ) ^ 2 * (Real.exp (-t)) ^ 2 / 2) 1 = Real.exp (-2) := by
  have hderiv : deriv (fun τ => Real.exp (-τ)) = fun τ => -Real.exp (-τ) := by
    funext τ
    have h : HasDerivAt (fun τ => Real.exp (-τ)) (-Real.exp (-τ)) τ := by
      simpa using (hasDerivAt_neg τ).exp
    exact h.deriv
  rw [hderiv]
  constructor
  · simp only [Real.exp_zero, neg_zero]
    norm_num
  · show (-Real.exp (-(1 : ℝ))) ^ 2 / 2 + (1 : ℝ) ^ 2 * (Real.exp (-(1 : ℝ))) ^ 2 / 2 =
        Real.exp (-2)
    rw [show (-2 : ℝ) = -1 + -1 by norm_num, Real.exp_add]
    ring

/-- Boundary case `γ = 0`: zero displacement has constant energy, so
the antitone conclusion holds with equality. -/
example : Antitone (fun t => (deriv (fun _ : ℝ => (0 : ℝ)) t) ^ 2 / 2 +
    (3 : ℝ) ^ 2 * ((fun _ : ℝ => (0 : ℝ)) t) ^ 2 / 2) := by
  have hx1 : ∀ t, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (deriv (fun _ : ℝ => (0 : ℝ)) t) t :=
    fun t => by simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  have hx2 : ∀ t, HasDerivAt (deriv (fun _ : ℝ => (0 : ℝ)))
      (deriv (deriv (fun _ : ℝ => (0 : ℝ))) t) t := by
    intro t
    have hd : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
      funext τ
      simp
    rw [hd]
    simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  have hode : ∀ t, deriv (deriv (fun _ : ℝ => (0 : ℝ))) t +
      2 * (0 : ℝ) * deriv (fun _ : ℝ => (0 : ℝ)) t + (3 : ℝ) ^ 2 * (fun _ : ℝ => (0 : ℝ)) t = 0 := by
    intro t
    have hd : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
      funext τ
      simp
    rw [hd]
    simp
  exact EarthScience.damped_oscillator_energy_antitone hx1 hx2 hode (le_refl 0)
