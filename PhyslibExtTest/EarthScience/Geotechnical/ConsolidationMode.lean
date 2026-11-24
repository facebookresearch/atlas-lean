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
the drainage-path misreading control, and the depth average
and settlement contribution.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Focused mode values
- B. Decay and misreading controls
- C. Average and settlement checks

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

/-- The initial profile and its mid-depth amplitude value. -/
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

/-- Physical decay bound at the focused data. -/
example : |consolidationMode 100 4 2 3 1| ≤ 100 := by
  have h := consolidationMode_abs_le_amplitude (u0 := 100) (H := 4)
    (cv := 2) (t := 3) (z := 1) (by norm_num) (by norm_num)
    (by norm_num)
  simpa using h

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
mid-depth amplitude value above. -/
example : consolidationMode 100 2 2 0 2 = 0 :=
  consolidationMode_zero_right (by norm_num)

/-! ## C. Average and settlement checks -/

/-- The sine integral at the focused thickness: `8 / π`. -/
example : (∫ z in (0 : ℝ)..(4 : ℝ), Real.sin (Real.pi * z / 4))
    = 8 / Real.pi := by
  have h := integral_sin_pi_mul_div (H := (4 : ℝ)) (by norm_num)
  rw [h]
  ring

/-- Initial depth average: the sine factor `2 / π` times the
amplitude, contrasting a uniform initial pressure. -/
example : consolidationModeAverage 100 4 2 0 = 200 / Real.pi := by
  rw [consolidationModeAverage_eq (by norm_num)]
  simp
  norm_num

/-- Depth average at the focused time, as a client of the
general statement. -/
example : consolidationModeAverage 100 4 2 3
    = 2 * 100 / Real.pi * Real.exp (-2 * (Real.pi / 4) ^ 2 * 3) :=
  consolidationModeAverage_eq (by norm_num)

/-- No settlement has accrued at `t = 0`. -/
example : consolidationModeSettlement (1 / 10) 100 4 2 0 = 0 := by
  rw [consolidationModeSettlement_eq _ (by norm_num)]
  simp

/-- Scalar settlement at the focused time, as a client of
the general statement. -/
example : consolidationModeSettlement (1 / 10) 100 4 2 3
    = 2 * (1 / 10) * 100 * 4 / Real.pi
      * (1 - Real.exp (-2 * (Real.pi / 4) ^ 2 * 3)) :=
  consolidationModeSettlement_eq _ (by norm_num)

/-- The scalar settlement is `mv` times the depth integral
of the effective stress increase for an arbitrary constant
total stress field: the stress terms cancel. -/
example (mv u0 H cv t : ℝ) (σ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) :
    consolidationModeSettlement mv u0 H cv t
      = mv * ∫ z in (0 : ℝ)..H,
        (effectiveStressCompressionPositive (σ z)
            (consolidationMode u0 H cv t z) 0 0
          - effectiveStressCompressionPositive (σ z)
            (consolidationMode u0 H cv 0 z) 0 0) :=
  consolidationModeSettlement_eq_effectiveStress_integral mv σ 0 u0 H cv t

/-- Nonnegative settlement at the focused data. -/
example : 0 ≤ consolidationModeSettlement (1 / 10) 100 4 2 3 :=
  consolidationModeSettlement_nonneg (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

#print axioms EarthScience.consolidationMode_eq
#print axioms EarthScience.consolidationMode_pde
#print axioms EarthScience.consolidationMode_zero_left
#print axioms EarthScience.consolidationMode_zero_right
#print axioms EarthScience.consolidationMode_time_zero
#print axioms EarthScience.consolidationMode_midpoint_time_zero
#print axioms EarthScience.consolidationMode_abs_le_amplitude
#print axioms EarthScience.consolidationModeAverage_eq
#print axioms EarthScience.consolidationModeSettlement_eq
#print axioms EarthScience.consolidationModeSettlement_nonneg
#print axioms
  EarthScience.consolidationModeSettlement_eq_effectiveStress_integral

end PhyslibExtTest.EarthScience.Geotechnical.ConsolidationMode
