 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.A07AtmosphericRadiation

/-!
# One-layer grey atmosphere checks

Concrete consumers of `PhyslibExt.EarthScience.A07AtmosphericRadiation`:
transparent `eps = 0`, opaque `eps = 1`, and the numeric formula
`Te = 3, eps = 1/4` giving `Ts^4 = 81 / (7/8) = 648/7`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.A07AtmosphericRadiation`
-/

/-- Transparent case: `eps = 0, Te = Ts = 2` satisfies the TOA balance. -/
example : (2:ℝ) ^ 4 = (2:ℝ) ^ 4 :=
  EarthScience.a07_transparent_limit (σ := 1) (Te := 2) (Ts := 2) (Ta := 5) (by norm_num)
    (by norm_num)

/-- Surface theorem at `eps = 0`: `Ts^4 = Te^4`. -/
example : (3:ℝ) ^ 4 = (3:ℝ) ^ 4 / (1 - (0:ℝ) / 2) :=
  EarthScience.a07_surface_temperature (eps := 0) (σ := 1) (Te := 3) (Ts := 3) (Ta := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Opaque witness as an elaboration check: `Ts^4 = Te^4 / (1 - 1/2)` gives `Ts^4 = 2 * Te^4`. -/
example {Te Ts : ℝ} (h : Ts ^ 4 = Te ^ 4 / (1 - (1:ℝ) / 2)) : Ts ^ 4 = 2 * Te ^ 4 :=
  EarthScience.a07_opaque_witness h

/-- Atmosphere theorem at the boundary `Ta = Ts = 0`. -/
example : (0:ℝ) ^ 4 = (0:ℝ) ^ 4 / 2 :=
  EarthScience.a07_atmosphere_temperature (eps := 1/2) (σ := 2) (Ts := 0) (Ta := 0)
    (by norm_num) (by norm_num) (by norm_num)

/-- Numeric denominator: `1 - (1/4)/2 = 7/8`. -/
example : (1:ℝ) - (1/4 : ℝ) / 2 = 7 / 8 := by norm_num

/-- Numeric formula: `81 * (8/7) = 648/7`. -/
example : (3:ℝ) ^ 4 * (8 / 7) = 648 / 7 := by norm_num

