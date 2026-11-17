/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.ContinuumMechanics.ControlVolumes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Moving-endpoint transport checks

Concrete consumer of `PhyslibExt.ContinuumMechanics.ControlVolumes`:
the field `u t x = t * x` with endpoints `a(t) = 0`, `b(t) = t + 1`.
At `t = 1` the moving integral `∫₀² x dx` plus the endpoint term
`u(1, 2) * 1 = 2` gives energy derivative `4`, matching
`d/dt [t (t+1)^2 / 2]` at `t = 1`. The flux form with `f = 0`,
`src = u_t` gives the same value through the relative fluxes.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Linear field with unit-speed endpoint

## iv. References

None.

## A. Linear field with unit-speed endpoint

-/

/-- Leibniz identity for `u t x = t * x`, `a = 0`, `b(t) = t + 1`
at `t = 1`: the value is `4`. -/
example :
    deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..(τ + 1), τ * x) 1 = 4 := by
  have h := ControlVolumes.movingEndpoint_deriv
    (u := fun t x : ℝ => t * x) (ut := fun _ x : ℝ => x)
    (a := fun _ : ℝ => 0) (b := fun τ : ℝ => τ + 1)
    (a' := fun _ : ℝ => 0) (b' := fun _ : ℝ => 1)
    1
    (hasDerivAt_const 1 (0 : ℝ))
    (by simpa using (hasDerivAt_id 1).add_const (1 : ℝ))
    (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_id t).mul_const x)
    (by fun_prop)
  rw [h]
  rw [integral_id]
  norm_num

/-- Relative-flux form for the same field with `f = 0`: the value
is again `4`. -/
example :
    deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..(τ + 1), τ * x) 1 = 4 := by
  have h := ControlVolumes.movingEndpoint_deriv_flux
    (u := fun t x : ℝ => t * x) (ut := fun _ x : ℝ => x)
    (f := fun _ _ : ℝ => 0) (fx := fun _ _ : ℝ => 0)
    (src := fun _ x : ℝ => x)
    (a := fun _ : ℝ => 0) (b := fun τ : ℝ => τ + 1)
    (a' := fun _ : ℝ => 0) (b' := fun _ : ℝ => 1)
    1
    (hasDerivAt_const 1 (0 : ℝ))
    (by simpa using (hasDerivAt_id 1).add_const (1 : ℝ))
    (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_id t).mul_const x)
    (by fun_prop)
    (fun x => hasDerivAt_const x (0 : ℝ))
    continuousOn_const
    (fun _ => by ring)
    (by simpa using (continuous_id.intervalIntegrable (0 : ℝ) (2 : ℝ)))
  rw [h]
  rw [integral_id]
  norm_num

/-- Jump transport for the stationary fields `uL t x = x`,
`uR t x = 2x` with interface `s t = t` on `[0, 2]`: at `t = 1`
the derivative of the split integral is the interface jump
`1 * (1 - 2) = -1`. -/
example :
    HasDerivAt
      (fun τ : ℝ => (∫ x in (0 : ℝ)..τ, x) + (∫ x in τ..(2 : ℝ), 2 * x))
      (-1) 1 := by
  have h := ControlVolumes.movingJumpTransport_interior
    (uL := fun _ x : ℝ => x) (uR := fun _ x : ℝ => 2 * x)
    (vL := fun _ _ : ℝ => 0) (vR := fun _ _ : ℝ => 0)
    (s := fun τ : ℝ => τ) (s' := fun _ : ℝ => 1) (a := 0) (b := 2)
    (fun τ => hasDerivAt_id τ)
    (by fun_prop) (fun t x => by simpa using (hasDerivAt_const t (x : ℝ)))
    (by fun_prop) (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_const t (2 * x : ℝ)))
    (by fun_prop) 1 (by
      exact Filter.eventually_of_mem (Ioo_mem_nhds (by norm_num) (by norm_num))
        (fun τ hτ => ⟨hτ.1.le, hτ.2.le⟩))
  rw [show (-1 : ℝ) = (1 : ℝ) - 2 by norm_num]
  simpa using h
