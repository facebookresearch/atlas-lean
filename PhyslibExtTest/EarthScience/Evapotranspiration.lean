/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.Evapotranspiration

/-!
# Latent flux and evaporation checks

Concrete consumers of `PhyslibExt.EarthScience.Evapotranspiration`:
`LE = 200, rho_w = 1000, Lv = 2.5` (`E = 0.08`), zero flux, and
`LE = 50` (`E = 0.02`), plus the SI witness.

## i. Overview

These are elaboration and non-vacuity checks, not new results. As in the
module's scaled witness, `LE` is in `W/m^2`, `rho_w` in `kg/m^3`, and
`Lv = 2.5` in `MJ/kg`, so each `E` is in `10^-6 m/s`: `E = 0.08` is
`8 * 10^-8 m/s`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.Evapotranspiration`
-/

/-- Numeric evaporation: `LE = 200` gives `E = 0.08` (in `10^-6 m/s`). -/
example : (1000:ℝ) * 2.5 * ((200:ℝ) / (1000 * 2.5)) = 200 :=
  EarthScience.evaporation_rate (by norm_num) (by norm_num)

/-- Numeric evaporation: `LE = 50` gives `E = 0.02` (in `10^-6 m/s`). -/
example : (50:ℝ) / (1000 * 2.5) = 0.02 := by norm_num

/-- Nonnegativity: `LE = 200` gives `E >= 0`. -/
example : 0 ≤ (200:ℝ) / (1000 * 2.5) :=
  EarthScience.evaporation_nonneg (by norm_num) (by norm_num) (by norm_num)

/-- Zero flux gives zero evaporation. -/
example : (0:ℝ) / (1000 * 2.5) = 0 :=
  (EarthScience.evaporation_eq_zero_iff (by norm_num) (by norm_num)).mpr rfl

/-- Zero evaporation forces zero latent flux. -/
example {LE : ℝ} (h : LE / (1000 * 2.5) = 0) : LE = 0 :=
  (EarthScience.evaporation_eq_zero_iff (by norm_num) (by norm_num)).mp h

/-- Witness from the module: `LE = 100` gives `E = 0.04` (in `10^-6 m/s`). -/
example : (100:ℝ) / (1000 * 2.5) = 0.04 :=
  EarthScience.evaporation_witness

/-- SI witness: `Lv = 2.5 * 10^6 J/kg` gives `E = 4 * 10^-8 m/s`. -/
example : (100:ℝ) / (1000 * (2.5 * 10 ^ 6)) = 4 / 10 ^ 8 :=
  EarthScience.evaporation_witness_si
