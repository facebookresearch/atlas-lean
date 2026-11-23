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
`m = c = k = 1`, `x = t^2`, `y = t` satisfies the balance at
`t = 2`, and the public theorem gives the relative velocity
derivative, the relative equation, and the energy derivative
`12` there.

These are elaboration and non-vacuity checks, not new results.
-/

open RelativeOscillator

/-- Witness application at `t = 2`. -/
example : (1 : ℝ) * ((fun _ : ℝ => (2:ℝ)) 2 - (fun _ : ℝ => (0:ℝ)) 2)
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
  exact h.2.2.1

/-- Energy conclusion on the witness: derivative `12` at `t = 2`. -/
example : HasDerivAt (fun s : ℝ => (1:ℝ) / 2 * (2 * s - 1) ^ 2
      + (1:ℝ) / 2 * (s ^ 2 - s) ^ 2) 12 2 := by
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
  have h3 := h.2.2.2
  convert h3 using 1
  norm_num
