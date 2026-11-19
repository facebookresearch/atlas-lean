/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.ConsolidationMode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Drained consolidation mode checks

Concrete consumers of
`PhyslibExt.EarthScience.Geotechnical.ConsolidationMode` at
`(u0, H, cv) = (100, 4, 2)`: the explicit form, both drained
faces, the initial profile and midpoint, decay at mid-depth,
and the drainage-path misreading control.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Focused mode values
- B. Decay and misreading controls

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.ConsolidationMode`
-/

open Real
open EarthScience

namespace PhyslibExtTest.EarthScience.Geotechnical.ConsolidationMode

/-! ## A. Focused mode values -/

/-- Explicit form at the focused data. -/
example : consolidationMode 100 4 2 3 1
    = 100 * Real.exp (-2 * (Real.pi / 4) ^ 2 * 3)
      * Real.sin (Real.pi * 1 / 4) :=
  consolidationMode_eq (by norm_num)

/-- Both drained faces vanish. -/
example : consolidationMode 100 4 2 3 0 = 0 :=
  consolidationMode_zero_left 100 4 2 3

example : consolidationMode 100 4 2 3 4 = 0 :=
  consolidationMode_zero_right (by norm_num)

/-- The initial profile and its mid-depth peak. -/
example : consolidationMode 100 4 2 0 1
    = 100 * Real.sin (Real.pi * 1 / 4) :=
  consolidationMode_time_zero (by norm_num)

example : consolidationMode 100 4 2 0 2 = 100 := by
  have h := consolidationMode_midpoint_time_zero (u0 := 100) (H := 4)
    (cv := 2) (by norm_num)
  norm_num at h
  exact h

/-- The PDE at the focused data, as a client of the general
statement. -/
example : deriv (fun τ => consolidationMode 100 4 2 τ 1) 3
    = 2 * iteratedDeriv 2 (consolidationMode 100 4 2 3) 1 :=
  consolidationMode_pde (by norm_num) 3 1

/-! ## B. Decay and misreading controls -/

/-- Mid-depth decays below the initial amplitude. -/
example : consolidationMode 100 4 2 3 2 < 100 := by
  rw [consolidationMode_eq (by norm_num)]
  have hs : Real.sin (Real.pi * 2 / 4) = 1 := by
    have harg : Real.pi * 2 / 4 = Real.pi / 2 := by ring
    rw [harg, Real.sin_pi_div_two]
  rw [hs, mul_one]
  have harg : (-2 : ℝ) * (Real.pi / 4) ^ 2 * 3 < 0 := by
    have hpos : (0 : ℝ) < 2 * (Real.pi / 4) ^ 2 * 3 := by positivity
    linarith
  have he : Real.exp (-2 * (Real.pi / 4) ^ 2 * 3) < 1 := by
    calc Real.exp (-2 * (Real.pi / 4) ^ 2 * 3)
        < Real.exp 0 := Real.exp_strictMono harg
      _ = 1 := Real.exp_zero
  nlinarith [he, Real.exp_pos (-2 * (Real.pi / 4) ^ 2 * 3)]

/-- The wrong-sign exponent gives a different (growing) value,
so the decay sign in the explicit form is the checked one. -/
example : ¬ consolidationMode 100 4 2 3 2
    = 100 * Real.exp (2 * (Real.pi / 4) ^ 2 * 3)
      * Real.sin (Real.pi * 2 / 4) := by
  rw [consolidationMode_eq (by norm_num)]
  have hs : Real.sin (Real.pi * 2 / 4) = 1 := by
    have harg : Real.pi * 2 / 4 = Real.pi / 2 := by ring
    rw [harg, Real.sin_pi_div_two]
  rw [hs, mul_one, mul_one]
  have hlt : Real.exp (-2 * (Real.pi / 4) ^ 2 * 3)
      < Real.exp (2 * (Real.pi / 4) ^ 2 * 3) := by
    apply Real.exp_strictMono
    have hpos : (0 : ℝ) < 2 * (Real.pi / 4) ^ 2 * 3 := by positivity
    linarith
  intro h
  have h100 : (100 : ℝ) * Real.exp (-2 * (Real.pi / 4) ^ 2 * 3)
      < 100 * Real.exp (2 * (Real.pi / 4) ^ 2 * 3) :=
    mul_lt_mul_of_pos_left hlt (by norm_num)
  exact (ne_of_lt h100) h

/-- Drainage-path misreading control: with `H` halved, the mode
vanishes at `z = 2` (its own right face), unlike the true
mid-depth peak above. -/
example : consolidationMode 100 2 2 0 2 = 0 :=
  consolidationMode_zero_right (by norm_num)

#print axioms EarthScience.consolidationMode_eq
#print axioms EarthScience.consolidationMode_pde
#print axioms EarthScience.consolidationMode_zero_left
#print axioms EarthScience.consolidationMode_zero_right
#print axioms EarthScience.consolidationMode_time_zero
#print axioms EarthScience.consolidationMode_midpoint_time_zero

end PhyslibExtTest.EarthScience.Geotechnical.ConsolidationMode
