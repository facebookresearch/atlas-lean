/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.InternalEnergyMonotonic

/-!
# Internal-energy monotonicity checks

Concrete consumers of
`PhyslibExt.EarthScience.InternalEnergyMonotonic`: with `C = 5`,
`U0 = 10`, `T0 = 273`, the energy rises from `10` at `273` to `15` at
`274` and `145` at `300`, and its derivative is `5`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.InternalEnergyMonotonic`
-/

/-- `U(273) < U(274)` for `C = 5`, `U0 = 10`, `T0 = 273`. -/
example :
    (10 : ℝ) + 5 * (273 - 273) < 10 + 5 * (274 - 273) := by
  have h := EarthScience.internalEnergy_strictMono (C := (5 : ℝ)) (U0 := 10) (T0 := 273)
    (by norm_num)
  exact h (by norm_num)

/-- `U(273) = 10` and `U(300) = 145`: the rise is genuine, not a constant shift. -/
example : (10 : ℝ) + 5 * (273 - 273) = 10 ∧ (10 : ℝ) + 5 * (300 - 273) = 145 := by
  constructor <;> norm_num

/-- Derivative is the heat capacity `5` at `T = 300`. -/
example : HasDerivAt (fun T : ℝ => (10 : ℝ) + 5 * (T - 273)) 5 300 :=
  EarthScience.internalEnergy_hasDerivAt (C := (5 : ℝ)) (U0 := 10) (T0 := 273) 300

/-- Boundary case: equal temperatures give equal energies. -/
example :
    (10 : ℝ) + 5 * (300 - 273) = 10 + 5 * (300 - 273) := rfl
