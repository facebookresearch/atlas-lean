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
`u_xx = 0`. At `t = 1` the energy has derivative `8`: the diffusion
contribution `-3 * 18` and the boundary work `3 * 18` cancel, and
the source power is `∫₀² 3x^2 dx = 8`. The diffusion contribution
at those values is `-54 ≤ 0`, as `diffusion_contribution_nonpos`
asserts for `0 ≤ D`.

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
`D = 3`: the energy has derivative `8`. -/
example :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2)
      8 1 := by
  have hE : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..(2 : ℝ), ((τ + 2) * x) ^ 2 / 2)
      (∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) * x * x) 1 := by
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
        ((2 * ((1 : ℝ) + 2)) * (4 / 3)) 1 := by
      have h := ((hasDerivAt_id (1 : ℝ)).add_const (2 : ℝ)).pow 2
      simpa using h.mul_const (4 / 3)
    rw [funext hInt]
    convert hd using 1
    have e1 : (∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) * x * x) =
        ((1 : ℝ) + 2) * ∫ x in (0 : ℝ)..(2 : ℝ), x ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [e1, integral_pow]
    norm_num
  have h := ConductionPorts.heatEnergy_hasDerivAt (D := 3) (L := 2)
    (u := fun t x : ℝ => (t + 2) * x) (ut := fun _ x : ℝ => x)
    (ux := fun t _x : ℝ => t + 2) (uxx := fun _ _ : ℝ => 0)
    (src := fun _ x : ℝ => x) (t := 1)
    (by norm_num)
    (fun x _ => by simpa using ((hasDerivAt_id (1 : ℝ)).add_const 2).mul_const x)
    (fun x _ => by simpa using (hasDerivAt_id x).const_mul ((1 : ℝ) + 2))
    (fun x _ => hasDerivAt_const x ((1 : ℝ) + 2))
    (fun _ _ => by ring)
    ((continuous_const.mul continuous_id).continuousOn)
    (continuousOn_const)
    (continuousOn_const)
    hE
    (((continuous_const.mul continuous_id).mul
      continuous_id).intervalIntegrable 0 2)
  convert h using 1
  have e2 : (∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) * x * x) =
      ((1 : ℝ) + 2) * ∫ x in (0 : ℝ)..(2 : ℝ), x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [e2, integral_pow]
  norm_num [intervalIntegral.integral_const]

/-- The diffusion contribution at the same values is `-54 ≤ 0`. -/
example :
    -3 * (∫ x in (0 : ℝ)..(2 : ℝ), ((1 : ℝ) + 2) ^ 2) ≤ 0 :=
  ConductionPorts.diffusion_contribution_nonpos (by norm_num) (by norm_num)
    (fun t _x : ℝ => t + 2) 1
    (continuousOn_const.intervalIntegrable 0 2)
