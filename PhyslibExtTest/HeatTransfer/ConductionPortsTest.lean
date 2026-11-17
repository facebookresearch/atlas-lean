/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.HeatTransfer.ConductionPorts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Quadratic heat-energy identity checks

Concrete consumer of `PhyslibExt.HeatTransfer.ConductionPorts`: the
field `u t x = (t + 2) * x` on `[0, 2]` with `D = 3`, which
satisfies `u_t = D * u_xx + src` with `src t x = x`, `u_x = t + 2`,
`u_xx = 0`. At `t = 1` the energy derivative is `8`: the bulk
dissipation `-3 * 18` and the boundary work `3 * 18` cancel, and
the source power is `∫₀² 3x^2 dx = 8`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Linear field at `t = 1`

## iv. References

None.

## A. Linear field at `t = 1`

-/

/-- Energy identity for `u t x = (t + 2) * x` at `t = 1`, `L = 2`,
`D = 3`: both sides equal `8`. -/
example :
    deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2) 1 =
      -3 * (∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) ^ 2) +
        3 * (((1 : ℝ) + 2) * 2 * ((1 : ℝ) + 2) - ((1 : ℝ) + 2) * 0 * ((1 : ℝ) + 2)) +
          ∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) * x * x := by
  have hswap : ∀ t : ℝ,
      deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2) t =
        ∫ x in (0 : ℝ)..(2 : ℝ), (t + 2) * x * x := by
    intro t
    have hInt : ∀ τ : ℝ, (∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2) =
        (τ + 2) ^ 2 * (4 / 3) := by
      intro τ
      have h1 : (∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2) =
          (τ + 2) ^ 2 / 2 * ∫ x in (0 : ℝ)..(2 : ℝ), x ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring
      rw [h1, integral_pow]; ring
    have hd : HasDerivAt (fun τ : ℝ => (τ + 2) ^ 2 * (4 / 3))
        ((2 * (t + 2)) * (4 / 3)) t := by
      have h := ((hasDerivAt_id t).add_const (2 : ℝ)).pow 2
      simpa using h.mul_const (4 / 3)
    rw [funext hInt, hd.deriv]
    have h2 : (∫ x in (0 : ℝ)..(2 : ℝ), (t + 2) * x * x) =
        (t + 2) * ∫ x in (0 : ℝ)..(2 : ℝ), x ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [h2, integral_pow]; ring
  have h := ConductionPorts.heatEnergy_deriv (D := 3) (L := 2)
    (u := fun t x : ℝ => (t + 2) * x) (ut := fun _ x : ℝ => x)
    (ux := fun t _x : ℝ => t + 2) (uxx := fun _ _ : ℝ => 0)
    (src := fun _ x : ℝ => x)
    (by norm_num)
    (fun t x => by simpa using (hasDerivAt_id x).const_mul (t + 2))
    (fun t x => hasDerivAt_const x (t + 2))
    (fun _ _ => by ring)
    (fun t => (continuous_const.mul continuous_id).continuousOn)
    (fun _ => continuousOn_const)
    (fun _ => continuousOn_const)
    hswap
    (fun _ => ((continuous_const.mul continuous_id).mul
      continuous_id).intervalIntegrable 0 2)
    1
  convert h using 2 <;> norm_num [integral_pow]
