/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

import PhyslibExt.Engineering.ThermalSeries

/-!
# Thermal-series checks

Focused checks for `PhyslibExt.Engineering.ThermalSeries`: one
layer with unit area, film coefficients `10` and `20`,
thickness `1 / 5`, and unit conductivity has total resistance
`7 / 20`; interface temperatures `20, 18, 14, 13` satisfying the
drop laws at heat rate `20` recover `Q = 20` from the total
difference `7`.

These are elaboration and non-vacuity checks, not new results.
-/

/-- Total resistance at the witness. -/
example : thermalSeriesResistance (n := 1) 1 10 20 (fun _ => 1 / 5)
    (fun _ => 1) = 7 / 20 := by
  norm_num [thermalSeriesResistance, Finset.sum_range_one]

/-- Heat-rate recovery at the witness temperatures. -/
example : (20 : ℝ) = (20 - 13)
    / thermalSeriesResistance (n := 1) 1 10 20 (fun _ => 1 / 5)
      (fun _ => 1) := by
  have h := thermalSeriesHeatRate_of_drops (n := 1) (A := 1)
    (hin := 10) (hout := 20) (Q := 20) (L := fun _ => (1 : ℝ) / 5)
    (k := fun _ => 1)
    (Temp := fun i => if i = 0 then (20 : ℝ)
      else if i = 1 then 18 else if i = 2 then 14 else 13)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i _; norm_num) (by intro i _; norm_num)
    (by norm_num) (by intro i hi; interval_cases i <;> norm_num)
    (by norm_num)
  simpa using h
