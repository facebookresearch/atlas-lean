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

private lemma aux_swap (t y : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..y, τ * x)
      (∫ x in (0 : ℝ)..y, x) t := by
  have hInt : ∀ τ : ℝ, (∫ x in (0 : ℝ)..y, τ * x) = τ * (y ^ 2 / 2) := by
    intro τ
    rw [intervalIntegral.integral_const_mul]
    rw [integral_id]
    ring
  rw [funext hInt]
  have hd : HasDerivAt (fun τ : ℝ => τ * (y ^ 2 / 2)) (y ^ 2 / 2) t := by
    simpa using (hasDerivAt_id t).mul_const (y ^ 2 / 2)
  convert hd using 1
  rw [integral_id]
  ring

/-- Leibniz identity for `u t x = t * x`, `a = 0`, `b(t) = t + 1`
at `t = 1`: the value is `4`. -/
example :
    deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..(τ + 1), τ * x) 1 = 4 := by
  have h := ControlVolumes.movingEndpoint_deriv
    (u := fun t x : ℝ => t * x) (ut := fun _ x : ℝ => x)
    (a := fun _ : ℝ => 0) (b := fun τ : ℝ => τ + 1)
    (a' := fun _ : ℝ => 0) (b' := fun _ : ℝ => 1)
    (fun t => hasDerivAt_const t (0 : ℝ))
    (fun t => by simpa using (hasDerivAt_id t).add_const (1 : ℝ))
    (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_id t).mul_const x)
    (by fun_prop)
    (fun t y => (continuous_const.mul continuous_id).continuousOn)
    aux_swap 1
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
    (fun t => hasDerivAt_const t (0 : ℝ))
    (fun t => by simpa using (hasDerivAt_id t).add_const (1 : ℝ))
    (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_id t).mul_const x)
    (by fun_prop)
    (fun t y => (continuous_const.mul continuous_id).continuousOn)
    aux_swap
    (fun t x => hasDerivAt_const x (0 : ℝ))
    (fun _ => continuousOn_const)
    (fun _ _ => by ring)
    (fun t => by simpa using (continuous_id.intervalIntegrable (0 : ℝ) (t + 1)))
    (fun t => by simpa using (continuous_id.intervalIntegrable (0 : ℝ) (t + 1)))
    1
  rw [h]
  rw [integral_id]
  norm_num
