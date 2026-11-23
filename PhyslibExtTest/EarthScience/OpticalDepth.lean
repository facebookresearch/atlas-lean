/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.OpticalDepth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Optical depth checks

Concrete consumers of `PhyslibExt.EarthScience.OpticalDepth` with
constant absorption coefficient `kappa = 2`: the depths over `[0, 1]`
and `[1, 3]` are `2` and `4`, the total over `[0, 3]` is `6`, and the
Beer-Lambert transmission over `[0, 3]` is `exp(-2) * exp(-4)`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Constant-coefficient layers and transmission

## iv. References

- `PhyslibExt.EarthScience.OpticalDepth`
-/

open MeasureTheory intervalIntegral

/-- Constant absorption `kappa = 2` over `[0, 1]`: depth `2`. -/
example : EarthScience.opticalDepth (fun _ => (2 : ℝ)) 0 1 = 2 := by
  simp only [EarthScience.opticalDepth]; rw [intervalIntegral.integral_const]; norm_num

/-- Constant absorption `kappa = 2` over `[1, 3]`: depth `4`. -/
example : EarthScience.opticalDepth (fun _ => (2 : ℝ)) 1 3 = 4 := by
  simp only [EarthScience.opticalDepth]; rw [intervalIntegral.integral_const]; norm_num

/-- Additivity for the constant-coefficient layers: `6 = 2 + 4`. -/
example : EarthScience.opticalDepth (fun _ => (2 : ℝ)) 0 3 =
    EarthScience.opticalDepth (fun _ => (2 : ℝ)) 0 1 +
      EarthScience.opticalDepth (fun _ => (2 : ℝ)) 1 3 :=
  EarthScience.optical_depth_add (fun _ => (2 : ℝ)) 0 1 3 (by norm_num) (by norm_num)
    intervalIntegrable_const intervalIntegrable_const

/-- The total depth over `[0, 3]` is `6` (non-vacuous: nonzero). -/
example : EarthScience.opticalDepth (fun _ => (2 : ℝ)) 0 3 = 6 := by
  have h := EarthScience.optical_depth_add (fun _ => (2 : ℝ)) 0 1 3 (by norm_num) (by norm_num) intervalIntegrable_const intervalIntegrable_const
  have h1 : EarthScience.opticalDepth (fun _ => (2 : ℝ)) 0 1 = 2 := by simp only [EarthScience.opticalDepth]; rw [intervalIntegral.integral_const]; norm_num
  have h2 : EarthScience.opticalDepth (fun _ => (2 : ℝ)) 1 3 = 4 := by simp only [EarthScience.opticalDepth]; rw [intervalIntegral.integral_const]; norm_num
  rw [h, h1, h2]; norm_num

/-- Beer-Lambert transmission over `[0, 3]` multiplies:
`exp(-6) = exp(-2) * exp(-4)`. -/
example : Real.exp (-EarthScience.opticalDepth (fun _ => (2 : ℝ)) 0 3) =
    Real.exp (-(2 : ℝ)) * Real.exp (-(4 : ℝ)) := by
  have h := EarthScience.transmission_mul_two_layers (fun _ => (2 : ℝ)) 0 1 3 (by norm_num) (by norm_num) intervalIntegrable_const intervalIntegrable_const
  have h1 : EarthScience.opticalDepth (fun _ => (2 : ℝ)) 0 1 = 2 := by simp only [EarthScience.opticalDepth]; rw [intervalIntegral.integral_const]; norm_num
  have h2 : EarthScience.opticalDepth (fun _ => (2 : ℝ)) 1 3 = 4 := by simp only [EarthScience.opticalDepth]; rw [intervalIntegral.integral_const]; norm_num
  rw [h, h1, h2]

/-- Nonnegativity for constant absorption: depth over `[0, 3]` is `>= 0`. -/
example : 0 ≤ EarthScience.opticalDepth (fun _ => (2 : ℝ)) 0 3 :=
  (EarthScience.optical_depth_nonneg (fun _ => (2 : ℝ)) 0 3 (by norm_num)
    (fun x _ => by norm_num) intervalIntegrable_const).1

/-- Transmission multiplies across finitely many layers: a consumer of
the finite-layer theorem with per-layer depths `tau_i = 2 * i`. -/
example : Real.exp (-∑ i ∈ Finset.range 2, (fun i => (2 * i : ℝ)) i) =
    ∏ i ∈ Finset.range 2, Real.exp (-(fun i => (2 * i : ℝ)) i) :=
  EarthScience.transmission_mul_layers (fun i => (2 * i : ℝ)) 2
