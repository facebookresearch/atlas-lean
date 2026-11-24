/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.UpwardSeepage
import PhyslibExt.EarthScience.HydrostaticColumn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Upward-seepage threshold checks

Concrete consumers of
`PhyslibExt.EarthScience.Geotechnical.UpwardSeepage`: the
critical gradient for `Gs = 2.65`, `e = 0.6`, the no-flow
hydrostatic case, and a supercritical gradient giving
negative effective stress.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Critical gradient and signs

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.UpwardSeepage`
-/

open EarthScience

namespace PhyslibExtTest.EarthScience.Geotechnical.UpwardSeepage

/-! ## A. Critical gradient and signs -/

/-- The textbook critical gradient at `Gs = 2.65`, `e = 0.6`
is `1.03125`. -/
example : ((2.65 : ℝ) - 1) / (1 + 0.6) = 1.03125 := by norm_num

/-- At zero gradient the profile is the submerged-weight
line `z * γ_sub` (with `γw = 10`, `γ_sub = 1.65 * 10 / 1.6`). -/
example (z : ℝ) :
    bulkUnitWeight 2.65 1 0.6 10 * z
        - porePressureOfHead 10 (upwardHead 0 z) z
      = z * submergedUnitWeight 2.65 0.6 10 := by
  have h := upwardSeepage_effectiveStress (Gs := 2.65) (e := 0.6)
    (γw := 10) (i := 0) (z := z) (by norm_num)
  simpa using h

/-- The hydrostatic bridge at concrete values: with
`γw = ρ * g = 2 * 3`, the no-flow pore pressure at depth
`4` is `24`, through
`porePressureOfHead_upwardHead_zero_eq_hydrostatic`. -/
example : porePressureOfHead (2 * 3) (upwardHead 0 4) 4 = 24 := by
  have h := porePressureOfHead_upwardHead_zero_eq_hydrostatic (2 : ℝ) 3 4
  rw [h]
  norm_num

/-- The same value through the named hydrostatics API:
`hydrostatic_pressure_depth` at zero surface gauge
pressure, consumed here as an external client (the
seepage module does not re-export it). -/
example : porePressureOfHead (2 * 3) (upwardHead 0 4) 4
    = (0 : ℝ) - 2 * 3 * (-4) := by
  rw [porePressureOfHead_upwardHead_zero_eq_hydrostatic]
  exact (hydrostatic_pressure_depth 0 2 3 4).2

/-- The no-flow profile has the hydrostatic depth slope
`ρ * g`, from `hydrostatic_pressure_depth`. -/
example (z : ℝ) :
    HasDerivAt (fun d => (0 : ℝ) + 2 * 3 * d) (2 * 3) z :=
  (hydrostatic_pressure_depth 0 2 3 z).1

/-- Total-minus-pore threshold, subcritical direction:
at `i = 1 / 2` (below the critical `1.03125`) the total
stress minus pore pressure is nonnegative at every
positive depth, through `upwardSeepage_nonneg_total_iff`. -/
example : ∀ z > 0, 0 ≤ bulkUnitWeight 2.65 1 0.6 10 * z
    - porePressureOfHead 10 (upwardHead (1 / 2) z) z :=
  (upwardSeepage_nonneg_total_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Total-minus-pore threshold, supercritical direction:
at `i = 2` the profile cannot stay nonnegative at every
positive depth. -/
example : ¬ ∀ z > 0, 0 ≤ bulkUnitWeight 2.65 1 0.6 10 * z
    - porePressureOfHead 10 (upwardHead 2 z) z := by
  intro h
  have hle := (upwardSeepage_nonneg_total_iff (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).mp h
  norm_num at hle

/-- A supercritical gradient (`i = 2` above the critical
`1.03125`) gives negative effective stress at depth `1`. -/
example : (1 : ℝ) * (submergedUnitWeight 2.65 0.6 10 - 2 * 10) < 0 := by
  have hiff := upwardSeepage_nonneg_iff (Gs := 2.65) (e := 0.6)
    (γw := (10 : ℝ)) (i := 2) (by norm_num) (by norm_num) (by norm_num)
  by_contra hcon
  have hnn : 0 ≤ (1 : ℝ) * (submergedUnitWeight 2.65 0.6 10 - 2 * 10) :=
    le_of_not_gt hcon
  have hall : ∀ z > 0, 0 ≤ z * (submergedUnitWeight 2.65 0.6 10 - 2 * 10) := by
    intro z hz
    exact mul_nonneg hz.le (by simpa using hnn)
  have hle := hiff.mp hall
  norm_num at hle

/-- At the critical gradient the effective stress vanishes at
every depth (closed form at `i = γ_sub / γw`). -/
example (z : ℝ) :
    z * (submergedUnitWeight 2.65 0.6 10
      - (submergedUnitWeight 2.65 0.6 10 / 10) * 10) = 0 := by
  norm_num [submergedUnitWeight]

/-- With `γw < 0` the nonnegativity conclusion fails even at
zero gradient: the positivity hypothesis is essential. -/
example : ¬ ∀ z > 0,
    0 ≤ z * (submergedUnitWeight 2.65 0.6 (-10) - 0 * (-10)) := by
  intro h
  have h1 := h 1 one_pos
  norm_num [submergedUnitWeight] at h1

#print axioms EarthScience.upwardSeepage_effectiveStress
#print axioms EarthScience.upwardSeepage_nonneg_iff
#print axioms EarthScience.upwardSeepage_nonneg_total_iff

end PhyslibExtTest.EarthScience.Geotechnical.UpwardSeepage
