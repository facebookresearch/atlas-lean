/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.PoissonAdiabat

/-!
# Poisson-adiabat checks

Concrete consumers of `PhyslibExt.EarthScience.PoissonAdiabat`: the
exponent identity for dry air (`R = 287`, `cp = 1005`), and the Poisson
relation in a small exact case (`γ = 2`, `R = 1`, `cp = 2`, where
`T₂ = T₁ * (p₂ / p₁) ^ (1 / 2)`).

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`p₁ = 1`, `p₂ = 4`, `v₁ = 2`, `v₂ = 1`, `T₁ = 2`, `T₂ = 4`, the ideal-gas
law holds at both states (`1 * 2 = 1 * 2`, `4 * 1 = 1 * 4`) and the
adiabat holds (`1 * 2 ^ 2 = 4 * 1 ^ 2 = 4`), so the Poisson relation gives
`4 = 2 * (4 / 1) ^ (1 / 2) = 2 * 2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Exponent identity for dry air
- B. Poisson relation, exact `γ = 2` case

## iv. References

- `PhyslibExt.EarthScience.PoissonAdiabat`
-/

/-- Exponent identity for dry air: `(γ - 1) / γ = R / cp` with
`R = 287`, `cp = 1005`. -/
example : ((1005 : ℝ) / (1005 - 287) - 1) / (1005 / (1005 - 287)) = 287 / 1005 :=
  EarthScience.poisson_exponent_identity (by norm_num) (by norm_num)

/-- Poisson relation, exact case: `γ = 2`, pressures `1 → 4`, temperatures
`2 → 4`. -/
example : (4 : ℝ) = 2 * (4 / 1 : ℝ) ^ ((1 : ℝ) / 2) := by
  have h := EarthScience.poisson_temperature_ratio
    (p₁ := (1 : ℝ)) (p₂ := (4 : ℝ)) (v₁ := (2 : ℝ)) (v₂ := (1 : ℝ))
    (T₁ := (2 : ℝ)) (T₂ := (4 : ℝ)) (R := (1 : ℝ)) (cp := (2 : ℝ)) (γ := (2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hrw : ((4 : ℝ) / 1) ^ ((1 : ℝ) / 2) = 2 := by
    rw [div_one, ← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hrw] at h
  rw [hrw]
  exact h
