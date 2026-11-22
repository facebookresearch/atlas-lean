/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

The columns are physical only when every layer has nonnegative thickness:
`0 ≤ h`, `0 ≤ T`, and a compensation depth at or below the base of the
root, `T + r ≤ D`. The Airy theorems assume exactly this. The underlying
identities are also recorded as signed-algebra lemmas over all reals,
where they can describe negative thicknesses: `ρc = 1`, `ρm = 2`, `h = 1`,
`T = 10`, `D = 5` gives root `1` and mantle thickness `D - T - r = -6`.

## ii. Key results

- `EarthScience.airy_root_pressure_eq`: for a physical column the Airy root
  gives nonnegative layer thicknesses and equalizes pressure.
- `EarthScience.airy_root_of_pressure_eq`: for a physical column equal
  pressure forces the root.
- `EarthScience.airy_root_pressure_eq_signed`,
  `EarthScience.airy_root_of_pressure_eq_signed`: the same identities as
  signed algebra over all reals.
- `EarthScience.airy_root_nonneg_pos`: the root is nonnegative, positive
  for positive relief.

## iii. Table of contents

- A. Airy root and compensation pressure

## iv. References

- Turcotte, D. L. and Schubert, G., *Geodynamics*, 2nd ed., Cambridge
  University Press, 2002, Chapter 5 (Isostasy): the Airy model, in which
  topographic relief is compensated locally by a crustal root, with equal
  pressure at a common compensation depth.
- The expanded identity itself is proved from ordered-field algebra in
  Mathlib; Mathlib does not justify the Airy column model.

Convention mapping to the Lean statement: `ρc` is the crust density and `ρm`
the mantle density (`ρc < ρm`); `h` is the elevation above the reference
column; `r = ρc * h / (ρm - ρc)` is the crustal root below the reference
crust; `T` is the reference crust thickness and `D` the common compensation
depth. Column pressure is density times thickness, with the gravitational
acceleration cancelling between the two columns, as in the overview.
Assumptions from the source model carried into the statement: local (Airy)
compensation at the same compensation depth, no flexural support, constant
densities, and nonnegative layer thicknesses (`0 ≤ h`, `0 ≤ T`,
`T + r ≤ D`).

## A. Airy root and compensation pressure
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Signed algebra behind `airy_root_pressure_eq`: the root `r = ρc * h / (ρm - ρc)`
balances the two pressure expressions for all real `h`, `T`, `D`, including
negative layer thicknesses that describe no physical column. -/
theorem airy_root_pressure_eq_signed {ρc ρm h T D : ℝ} (hρc : 0 < ρc) (hρm : ρc < ρm) :
    ρc * (T + h + ρc * h / (ρm - ρc)) + ρm * (D - T - ρc * h / (ρm - ρc))
      = ρc * T + ρm * (D - T) := by
  have hne : (ρm - ρc) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hρm)
  field_simp
  ring

set_option linter.unusedVariables false in
/-- Signed algebra behind `airy_root_of_pressure_eq`: equal pressure expressions
force the root formula for all real `h`, `T`, `D`, `r`, including negative layer
thicknesses that describe no physical column. -/
theorem airy_root_of_pressure_eq_signed {ρc ρm h T D r : ℝ} (hρc : 0 < ρc) (hρm : ρc < ρm)
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

/-- **Airy root equalizes compensation pressure** for a physical column:
nonnegative relief `h` and reference crust thickness `T`, the Airy root
`r = ρc * h / (ρm - ρc)`, and a compensation depth `D` at or below the base of
the root, `T + r ≤ D`. Every layer of the elevated column then has nonnegative
thickness (root `r`, crust `T + h + r`, mantle `D - T - r`), and its pressure
equals that of the reference column. -/
theorem airy_root_pressure_eq {ρc ρm h T D r : ℝ} (hρc : 0 < ρc) (hρm : ρc < ρm)
    (hh : 0 ≤ h) (hT : 0 ≤ T) (hr : r = ρc * h / (ρm - ρc)) (hD : T + r ≤ D) :
    0 ≤ r ∧ 0 ≤ T + h + r ∧ 0 ≤ D - T - r ∧
      ρc * (T + h + r) + ρm * (D - T - r) = ρc * T + ρm * (D - T) := by
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact (airy_root_nonneg_pos hρc hρm hh).1
  refine ⟨hr0, by linarith, by linarith, ?_⟩
  rw [hr]
  exact airy_root_pressure_eq_signed hρc hρm

/-- **Equal compensation pressure forces the Airy root** for a physical column:
nonnegative relief `h` and reference crust thickness `T`, and a root `r` whose
base lies at or above the compensation depth, `T + r ≤ D`. The forced root and
every layer of the elevated column have nonnegative thickness. -/
theorem airy_root_of_pressure_eq {ρc ρm h T D r : ℝ} (hρc : 0 < ρc) (hρm : ρc < ρm)
    (hh : 0 ≤ h) (hT : 0 ≤ T) (hD : T + r ≤ D)
    (hpress : ρc * (T + h + r) + ρm * (D - T - r) = ρc * T + ρm * (D - T)) :
    r = ρc * h / (ρm - ρc) ∧ 0 ≤ r ∧ 0 ≤ T + h + r ∧ 0 ≤ D - T - r := by
  have hr := airy_root_of_pressure_eq_signed hρc hρm hpress
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact (airy_root_nonneg_pos hρc hρm hh).1
  exact ⟨hr, hr0, by linarith, by linarith⟩

end EarthScience
