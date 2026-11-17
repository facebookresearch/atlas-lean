/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

import PhyslibExt.ClassicalMechanics.RelativeOscillator

/-!
# Relative-oscillator checks

Focused checks for
`PhyslibExt.ClassicalMechanics.RelativeOscillator`: the witness
`m = c = k = 1`, `x = t^2`, `y = t` satisfies the absolute equation
with `pf` read off from it, and the public theorem then gives the
relative velocity and energy derivative at `t = 2`.

These are elaboration and non-vacuity checks, not new results.
-/

open RelativeOscillator

/-- Witness application: at `t = 2`, `u = 2`, velocity `3`,
energy `(9 + 4) / 2`-style terms through the public theorem. -/
example : HasDerivAt (fun t : ℝ => t ^ 2 - t) ((2 * 2 - 1 : ℝ)) 2
    ∧ (1 : ℝ) * ((fun _ : ℝ => (2:ℝ)) 2 - (fun _ : ℝ => (0:ℝ)) 2)
        + 1 * ((fun t : ℝ => 2 * t) 2 - (fun _ : ℝ => (1:ℝ)) 2)
        + 1 * (fun t : ℝ => t ^ 2 - t) 2
      = (fun t : ℝ => 1 * (2:ℝ) + 1 * (2 * t - 1) + 1 * (t ^ 2 - t)) 2
        - 1 * (fun _ : ℝ => (0:ℝ)) 2 := by
  have h := relative_equation_and_energy (m := 1) (c := 1) (k := 1)
    (x := fun t : ℝ => t ^ 2) (y := fun t : ℝ => t)
    (u := fun t : ℝ => t ^ 2 - t) (xv := fun t : ℝ => 2 * t)
    (yv := fun _ : ℝ => 1) (xa := fun _ : ℝ => 2) (ya := fun _ : ℝ => 0)
    (pf := fun t : ℝ => 1 * (2:ℝ) + 1 * (2 * t - 1) + 1 * (t ^ 2 - t))
    (fun t => by ring) 2
    (by simpa using (hasDerivAt_pow 2 (2:ℝ)))
    (hasDerivAt_id (x := (2:ℝ)))
    (by simpa using (HasDerivAt.const_mul (2:ℝ) (hasDerivAt_id (x := (2:ℝ)))))
    (hasDerivAt_const (2:ℝ) (1:ℝ))
    (by ring)
  exact ⟨h.1, h.2.1⟩
