/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.ClassicalMechanics.Acoustics.EffectiveLoss
import Mathlib.Tactic.NormNum

/-!
# Effective-loss checks

Focused checks for
`PhyslibExt.ClassicalMechanics.Acoustics.EffectiveLoss`: patches
with `τ = 0.001` and `τ = 0.1` (losses `30` and `10` dB) have
effective loss strictly below the `20` dB decibel average, and
between the two patch losses.

These are elaboration and non-vacuity checks, not new results.
-/

open Acoustics

/-- Effective loss is below the decibel average. -/
example : -10 * Real.logb 10 (((0.001 : ℝ) + 0.1) / 2)
    < (-10 * Real.logb 10 0.001 + -10 * Real.logb 10 0.1) / 2 :=
  effective_loss_lt_db_average (by norm_num) (by norm_num) (by norm_num)

/-- Effective loss is between the patch losses. -/
example : -10 * Real.logb 10 (max (0.001 : ℝ) 0.1)
      ≤ -10 * Real.logb 10 ((0.001 + 0.1) / 2)
    ∧ -10 * Real.logb 10 ((0.001 + 0.1) / 2)
      ≤ -10 * Real.logb 10 (min (0.001 : ℝ) 0.1) :=
  effective_loss_between (by norm_num) (by norm_num)

/-- The two-patch effective coefficient is the arithmetic mean
at the concrete witness, through the transmission API. -/
example : effectivePowerTransmission (fun _ : Fin 2 => (1 : ℝ))
      (fun _ : Fin 2 => (1 : ℝ))
      (fun i : Fin 2 => if i = 0 then (0.001 : ℝ) else 0.1)
      Finset.univ
    = (0.001 + 0.1) / 2 :=
  effectivePowerTransmission_two_patch_eq (by norm_num) (by norm_num)

/-- Its loss is below the decibel average, through the
transmission API form. -/
example : -10 * Real.logb 10
      (effectivePowerTransmission (fun _ : Fin 2 => (1 : ℝ))
        (fun _ : Fin 2 => (1 : ℝ))
        (fun i : Fin 2 => if i = 0 then (0.001 : ℝ) else 0.1)
        Finset.univ)
    < (-10 * Real.logb 10 0.001 + -10 * Real.logb 10 0.1) / 2 :=
  effectivePowerTransmission_loss_lt_db_average (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
