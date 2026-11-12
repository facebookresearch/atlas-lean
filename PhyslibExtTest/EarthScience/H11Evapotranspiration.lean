 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.H11Evapotranspiration

/-!
# Latent flux and evaporation checks

Concrete consumers of `PhyslibExt.EarthScience.H11Evapotranspiration`:
`LE = 200, rho_w = 1000, Lv = 2.5` (`E = 0.08`), zero flux, and
`LE = 50` (`E = 0.02`).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.H11Evapotranspiration`
-/

/-- Numeric evaporation: `LE = 200` gives `E = 0.08`. -/
example : (1000:ℝ) * 2.5 * ((200:ℝ) / (1000 * 2.5)) = 200 :=
  EarthScience.h11_evaporation_rate (by norm_num) (by norm_num)

/-- Numeric evaporation: `LE = 50` gives `E = 0.02`. -/
example : (50:ℝ) / (1000 * 2.5) = 0.02 := by norm_num

/-- Nonnegativity: `LE = 200` gives `E >= 0`. -/
example : 0 ≤ (200:ℝ) / (1000 * 2.5) :=
  EarthScience.h11_evaporation_nonneg (by norm_num) (by norm_num) (by norm_num)

/-- Zero flux gives zero evaporation. -/
example : (0:ℝ) / (1000 * 2.5) = 0 :=
  EarthScience.h11_evaporation_zero (by norm_num) (by norm_num)

/-- Witness from the module: `LE = 100` gives `E = 0.04`. -/
example : (100:ℝ) / (1000 * 2.5) = 0.04 :=
  EarthScience.h11_evaporation_witness

