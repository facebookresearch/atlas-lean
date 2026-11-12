/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Airy isostasy: elevation, crustal root, and compensation pressure

For Airy columns with crust density `ρc` and mantle density `ρm > ρc`,
extra elevation `h` requires a crustal root `r = ρc * h / (ρm - ρc)`
under equal compensation pressure.

## i. Overview

The pressure of a column is density times thickness (the gravitational
acceleration cancels). A reference column of crust thickness `T` over
mantle down to compensation depth `D` has pressure
`ρc * T + ρm * (D - T)`. An elevated column with elevation `h` and root
`r` has crust thickness `T + h + r` and mantle thickness `D - T - r`,
so its pressure is `ρc * (T + h + r) + ρm * (D - T - r)`. Equal
compensation pressure forces `r = ρc * h / (ρm - ρc)`, and that root
indeed equalizes the pressures. Same compensation depth, no flexural
support, constant densities; `h` and `r` are lengths. This pressure-column
argument does not prove an arbitrary terrain gravity correction.

## ii. Key results

- `EarthScience.airy_root_pressure_eq`: the Airy root equalizes pressure.
- `EarthScience.airy_root_of_pressure_eq`: equal pressure forces the root.
- `EarthScience.airy_root_nonneg_pos`: the root is nonnegative, positive
  for positive relief.

## iii. Table of contents

- A. Airy root and compensation pressure

## iv. References

- None; proved from ordered-field algebra in Mathlib.

## A. Airy root and compensation pressure
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Airy root: the root `r = ρc * h / (ρm - ρc)` makes the elevated column
pressure equal the reference column pressure at a common compensation depth. -/
theorem airy_root_pressure_eq {ρc ρm h T D : ℝ} (hρc : 0 < ρc) (hρm : ρc < ρm) :
    ρc * (T + h + ρc * h / (ρm - ρc)) + ρm * (D - T - ρc * h / (ρm - ρc))
      = ρc * T + ρm * (D - T) := by
  have hne : (ρm - ρc) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hρm)
  field_simp
  ring

set_option linter.unusedVariables false in
/-- Converse: equal compensation pressure forces the Airy root formula. -/
theorem airy_root_of_pressure_eq {ρc ρm h T D r : ℝ} (hρc : 0 < ρc) (hρm : ρc < ρm)
    (hpress : ρc * (T + h + r) + ρm * (D - T - r) = ρc * T + ρm * (D - T)) :
    r = ρc * h / (ρm - ρc) := by
  have hne : (ρm - ρc) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hρm)
  rw [eq_div_iff hne]
  linear_combination -hpress

/-- Airy root is nonnegative, and positive for positive relief. -/
theorem airy_root_nonneg_pos {ρc ρm h : ℝ} (hρc : 0 < ρc) (hρm : ρc < ρm) (hh : 0 ≤ h) :
    0 ≤ ρc * h / (ρm - ρc) ∧ (0 < h → 0 < ρc * h / (ρm - ρc)) := by
  have hd : 0 < ρm - ρc := sub_pos.mpr hρm
  refine ⟨div_nonneg (mul_nonneg (le_of_lt hρc) hh) (le_of_lt hd), fun hhpos => ?_⟩
  exact div_pos (mul_pos hρc hhpos) hd

end EarthScience
