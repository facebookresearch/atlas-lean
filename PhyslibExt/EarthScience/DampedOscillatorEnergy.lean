/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Damped oscillator energy

For the damped linear oscillator `x'' + 2γ x' + ω₀² x = 0`, the energy
`E(t) = (x'(t))² / 2 + ω₀² (x(t))² / 2` has derivative
`E'(t) = -2γ (x'(t))²`. For `γ ≥ 0` the energy is therefore nonincreasing;
`γ = 0` recovers conservation. No boundary or initial conditions are
assumed. The differentiability hypotheses are the `HasDerivAt` data the
proofs use; the derivative identity needs them, and the oscillator equation,
only at the point `t`.

## i. Overview

Differentiating the energy and substituting the oscillator equation gives
the dissipation identity. Nonpositivity of the derivative for `γ ≥ 0`
then gives antitonicity through the mean-value theorem.

## ii. Key results

- `EarthScience.damped_oscillator_energy_hasDerivAt`: `E'(t) = -2γ (x'(t))²`.
- `EarthScience.damped_oscillator_energy_antitone`: `E` is antitone for
  `γ ≥ 0`.

## iii. Table of contents

- A. Energy dissipation and monotonicity

## iv. References

- `HasDerivAt.mul`, `HasDerivAt.add`, `HasDerivAt.div_const`,
  `HasDerivAt.const_mul` in Mathlib.
- `antitone_of_deriv_nonpos` in Mathlib.

## A. Energy dissipation and monotonicity
-/

@[expose] public section

namespace EarthScience

/-- Energy derivative for the damped oscillator `x'' + 2γ x' + ω₀² x = 0`:
with `E(t) = (x'(t))²/2 + ω₀² (x(t))²/2`, `E'(t) = -2γ (x'(t))²`. The
differentiability data and the oscillator equation are needed only at `t`. -/
theorem damped_oscillator_energy_hasDerivAt {γ ω₀ : ℝ} {x : ℝ → ℝ} (t : ℝ)
    (hx1 : HasDerivAt x (deriv x t) t)
    (hx2 : HasDerivAt (deriv x) (deriv (deriv x) t) t)
    (hode : deriv (deriv x) t + 2 * γ * deriv x t + ω₀ ^ 2 * x t = 0) :
    HasDerivAt (fun τ => (deriv x τ) ^ 2 / 2 + ω₀ ^ 2 * (x τ) ^ 2 / 2)
      (-2 * γ * (deriv x t) ^ 2) t := by
  have h1 : HasDerivAt (fun τ => deriv x τ * deriv x τ)
      (deriv (deriv x) t * deriv x t + deriv x t * deriv (deriv x) t) t :=
    hx2.mul hx2
  have h1d := h1.div_const (2 : ℝ)
  have h2 : HasDerivAt (fun τ => x τ * x τ)
      (deriv x t * x t + x t * deriv x t) t :=
    hx1.mul hx1
  have h2c := h2.const_mul (ω₀ ^ 2)
  have h2d := h2c.div_const (2 : ℝ)
  have hE := h1d.add h2d
  have hxx : deriv (deriv x) t = -2 * γ * deriv x t - ω₀ ^ 2 * x t := by
    linarith
  convert hE using 1
  · funext τ
    simp [pow_two]
  · rw [hxx]
    ring

/-- Damping gives nonincreasing energy: for `γ ≥ 0`, the damped-oscillator
energy `E(t) = (x'(t))²/2 + ω₀² (x(t))²/2` is antitone in `t`. -/
theorem damped_oscillator_energy_antitone {γ ω₀ : ℝ} {x : ℝ → ℝ}
    (hx1 : ∀ t, HasDerivAt x (deriv x t) t)
    (hx2 : ∀ t, HasDerivAt (deriv x) (deriv (deriv x) t) t)
    (hode : ∀ t, deriv (deriv x) t + 2 * γ * deriv x t + ω₀ ^ 2 * x t = 0)
    (hγ : 0 ≤ γ) :
    Antitone (fun t => (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2) := by
  have hE : ∀ t, HasDerivAt (fun τ => (deriv x τ) ^ 2 / 2 + ω₀ ^ 2 * (x τ) ^ 2 / 2)
      (-2 * γ * (deriv x t) ^ 2) t :=
    fun t => damped_oscillator_energy_hasDerivAt t (hx1 t) (hx2 t) (hode t)
  have hdiff : Differentiable ℝ
      (fun t => (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2) :=
    fun t => (hE t).differentiableAt
  have hnonpos : ∀ t, deriv
      (fun t => (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2) t ≤ 0 := by
    intro t
    have hderiv := (hE t).deriv
    rw [hderiv]
    have hsq : 0 ≤ (deriv x t) ^ 2 := sq_nonneg _
    have hprod : 0 ≤ γ * (deriv x t) ^ 2 := mul_nonneg hγ hsq
    nlinarith
  exact antitone_of_deriv_nonpos hdiff hnonpos

end EarthScience
