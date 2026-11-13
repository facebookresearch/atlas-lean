/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.UndampedOscillatorEnergy

/-!
# Undamped-oscillator energy checks

Concrete consumers of
`PhyslibExt.EarthScience.UndampedOscillatorEnergy`: the harmonic motion
`x(t) = 3 * cos (2 * t)` has energy `18`, and the conservation theorem
applied to an abstract solution of the oscillator equation.

## i. Overview

These are elaboration and non-vacuity checks, not new results. For
`ω₀ = 2`, `A = 3`, `E = ω₀ ^ 2 * A ^ 2 / 2 = 18`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Harmonic motion energy with numbers
- B. Conservation, abstract solution

## iv. References

- `PhyslibExt.EarthScience.UndampedOscillatorEnergy`
-/

/-- Harmonic motion with numbers: `E = 18` at `t = 1 / 2`. -/
example : (deriv (fun t => (3 : ℝ) * Real.cos (2 * t)) (1 / 2 : ℝ)) ^ 2 / 2 +
    (2 : ℝ) ^ 2 * ((fun t => (3 : ℝ) * Real.cos (2 * t)) (1 / 2 : ℝ)) ^ 2 / 2 = 18 := by
  have h := EarthScience.oscillator_energy_harmonic (A := (3 : ℝ)) (ω₀ := (2 : ℝ))
    (t := (1 / 2 : ℝ))
  rw [show (2 : ℝ) ^ 2 * (3 : ℝ) ^ 2 / 2 = 18 by norm_num] at h
  exact h

/-- Conservation for an abstract solution: energies at `0` and `1` agree. -/
example (x : ℝ → ℝ) (ω₀ : ℝ)
    (hx : ∀ t, HasDerivAt x (deriv x t) t)
    (hx' : ∀ t, HasDerivAt (deriv x) (-ω₀ ^ 2 * x t) t) :
    (deriv x 0) ^ 2 / 2 + ω₀ ^ 2 * (x 0) ^ 2 / 2 =
      (deriv x 1) ^ 2 / 2 + ω₀ ^ 2 * (x 1) ^ 2 / 2 :=
  EarthScience.oscillator_energy_const hx hx' 0 1
