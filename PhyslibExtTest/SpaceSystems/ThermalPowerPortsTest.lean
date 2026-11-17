/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.SpaceSystems.ThermalPowerPorts

/-!
# Radiator box-trapping checks

Concrete consumers of `PhyslibExt.SpaceSystems.ThermalPowerPorts`
at `C = 2`, `Krad = 1`, `Q = 16` on the box `[1, 2]`: the rate at
the lower end is `15 / 2 ≥ 0`, at the upper end is `0`, the clipped
and physical rates agree at `T = 3 / 2` with value `175 / 32`, and
the global Lipschitz bound holds with constant `16`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit-parameter box

## iv. References

None.

## A. Unit-parameter box

-/

/-- Clipped and physical rates agree at `T = 3 / 2`, value
`175 / 32`. -/
example :
    ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 (3 / 2) = 175 / 32 := by
  rw [ThermalPowerPorts.clippedRadiatorRate_eq_of_mem (by norm_num)]
  norm_num [ThermalPowerPorts.radiatorRate]

/-- Inward signs at the box ends and the Lipschitz bound with
constant `16`. -/
example :
    0 ≤ ThermalPowerPorts.radiatorRate 2 1 16 1 ∧
    ThermalPowerPorts.radiatorRate 2 1 16 2 ≤ 0 ∧
    |ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 0 -
      ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 3| ≤ 16 * |0 - 3| :=
  ⟨ThermalPowerPorts.radiatorRate_nonneg_at_min (C := 2) (Krad := 1) (Q := 16)
     (Tmin := 1) (by norm_num) (by norm_num),
   ThermalPowerPorts.radiatorRate_nonpos_at_max (C := 2) (Krad := 1) (Q := 16)
     (Tmax := 2) (by norm_num) (by norm_num),
   by
     have h := ThermalPowerPorts.clippedRadiatorRate_lipschitz (C := 2)
       (Krad := 1) (Q := 16) (Tmin := 1) (Tmax := 2) (by norm_num)
       (by norm_num) (by norm_num) (by norm_num) 0 3
     calc |ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 0 -
           ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 3|
         ≤ 1 * (4 * 2 ^ 3) / 2 * |(0 : ℝ) - 3| := h
       _ = 16 * |(0 : ℝ) - 3| := by norm_num⟩

/-- The constant equilibrium trajectory `T ≡ 2` (where
`radiatorRate 2 1 16 2 = 0`) is trapped in the box `[1, 2]`. -/
example :
    ∀ t : ℝ, 0 ≤ t → (fun _ : ℝ => (2 : ℝ)) t ∈ Set.Icc 1 2 :=
  fun t ht =>
    ThermalPowerPorts.radiator_solution_trapped (C := 2) (Krad := 1) (Q := 16)
      (Tmin := 1) (Tmax := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (fun s _ => by
        have h0 : ThermalPowerPorts.radiatorRate 2 1 16 2 = 0 := by
          norm_num [ThermalPowerPorts.radiatorRate]
        rw [h0]
        exact (hasDerivAt_const s (2 : ℝ)).hasDerivWithinAt)
      (by norm_num) ht
