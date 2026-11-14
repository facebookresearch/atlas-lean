/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.DarcyFlow

/-!
# Darcy flow checks

Concrete consumers of `PhyslibExt.EarthScience.DarcyFlow`: head profile
`h0 = 10`, `hL = 4`, `L = 100`, `K = 1 / 10000`, `φ = 1 / 4` (so the slope
is `-3 / 50`, the Darcy flux is `3 / 500000` and the pore velocity is
`3 / 125000`), plus the equal-heads and reversed-gradient boundaries.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric Darcy flow
- B. Boundary cases

## iv. References

- `PhyslibExt.EarthScience.DarcyFlow`
-/

/-- Numeric Darcy flow: head endpoints at `x = 0` and `x = 100`. -/
example : ((10 : ℝ) + (4 - 10) * 0 / 100 = 10) ∧
    ((10 : ℝ) + (4 - 10) * 100 / 100 = 4) :=
  EarthScience.linear_head_profile_endpoints (h0 := 10) (hL := 4) (L := 100) (by norm_num)

/-- Numeric Darcy flow: head gradient `-3 / 50` at `x = 50`. -/
example : HasDerivAt (fun x : ℝ => (10 : ℝ) + (4 - 10) * x / 100) (-3 / 50) 50 :=
  (EarthScience.linear_head_profile_hasDerivAt (h0 := 10) (hL := 4) (L := 100)
    (x := 50)).congr_deriv (by norm_num)

/-- Numeric Darcy flow: flux `3 / 500000` for `K = 1 / 10000`. -/
example : -(1 / 10000 : ℝ) * ((4 - 10) / 100) = 3 / 500000 := by
  have h := EarthScience.darcy_flux_linear_head (K := 1 / 10000) (h0 := 10) (hL := 4)
    (L := 100)
  rw [h]
  norm_num

/-- Numeric Darcy flow: pore velocity `3 / 125000` for `φ = 1 / 4`. -/
example : (-(1 / 10000 : ℝ) * (4 - 10) / 100) / (1 / 4) = 3 / 125000 := by
  have h := EarthScience.pore_velocity_linear_head (K := 1 / 10000) (h0 := 10) (hL := 4)
    (L := 100) (phi := 1 / 4) (by norm_num) (by norm_num)
  rw [h]
  norm_num

/-- Equal-heads boundary: `hL = h0` gives zero Darcy flux. -/
example : -(1 / 10000 : ℝ) * ((10 - 10) / 100) = 0 := by
  have h := EarthScience.darcy_flux_linear_head (K := 1 / 10000) (h0 := 10) (hL := 10)
    (L := 100)
  rw [h]
  norm_num

/-- Reversed-gradient boundary: `h0 = 4`, `hL = 10` gives flux `-3 / 500000`. -/
example : -(1 / 10000 : ℝ) * ((10 - 4) / 100) = -3 / 500000 := by
  have h := EarthScience.darcy_flux_linear_head (K := 1 / 10000) (h0 := 4) (hL := 10)
    (L := 100)
  rw [h]
  norm_num
