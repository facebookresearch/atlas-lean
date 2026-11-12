 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.StokesSettling

/-!
# Stokes settling checks

Concrete consumers of `PhyslibExt.EarthScience.StokesSettling`:
the balance for `a = 1, eta = 1, g = 10, rho_s = 2000, rho_f = 1000`,
neutral buoyancy, and a buoyant rise.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.StokesSettling`
-/

/-- Balance: the formula velocity satisfies the force balance at numeric values. -/
example :
    6 * Real.pi * 1 * 1 * (2 * (2000 - 1000) * 10 * (1:ℝ) ^ 2 / (9 * 1))
      = (4 / 3) * Real.pi * (1:ℝ) ^ 3 * (2000 - 1000) * 10 :=
  EarthScience.terminal_velocity_balances (by norm_num) (by norm_num) (by norm_num)

/-- Terminal velocity from the balance, at numeric values (hypothesis as premise). -/
example {v : ℝ} (h : 6 * Real.pi * 1 * 1 * v = (4 / 3) * Real.pi * (1:ℝ) ^ 3 * (2000 - 1000) * 10) :
    v = 2 * (2000 - 1000) * 10 * (1:ℝ) ^ 2 / (9 * 1) :=
  EarthScience.terminal_velocity (by norm_num) (by norm_num) (by norm_num) h

/-- Neutral buoyancy: equal densities give zero velocity. -/
example : 2 * ((1000:ℝ) - 1000) * 10 * (1:ℝ) ^ 2 / (9 * 1) = 0 :=
  EarthScience.neutral_buoyancy (by norm_num) (by norm_num) (by norm_num)

/-- Buoyant rise: `rho_s = 500 < rho_f = 1000` gives negative velocity. -/
example : 2 * ((500:ℝ) - 1000) * 10 * (1:ℝ) ^ 2 / (9 * 1) < 0 :=
  EarthScience.buoyant_rises (by norm_num) (by norm_num) (by norm_num) (by norm_num)

