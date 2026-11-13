/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.IsochronSlopeUncertainty

import Mathlib.Tactic.NormNum

/-!
# Isochron slope-uncertainty propagation checks

Concrete consumers of `PhyslibExt.EarthScience.IsochronSlopeUncertainty`:
a generic elaboration check, the zero-perturbation boundary case
`δ = 0`, and the helper log bound at `u = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.IsochronSlopeUncertainty`
-/

/-- Generic elaboration: the theorem applies to any `λ > 0`,
`m > 0`, and `δ ≥ 0`. -/
example {lam m δ : ℝ} (hlam : 0 < lam) (hm : 0 < m) (hδ : 0 ≤ δ) :
    |(Real.log (1 + (m + δ)) / lam - Real.log (1 + m) / lam)
        - δ / (lam * (1 + m))|
      ≤ δ ^ 2 / (2 * lam * (1 + m) ^ 2) :=
  EarthScience.isochron_age_slope_uncertainty hlam hm hδ

/-- Zero-perturbation boundary: with `δ = 0` the age change is `0`,
the derivative term is `0`, and the remainder is `0`. -/
example {lam m : ℝ} (hlam : 0 < lam) (hm : 0 < m) :
    |(Real.log (1 + (m + (0 : ℝ))) / lam - Real.log (1 + m) / lam)
        - (0 : ℝ) / (lam * (1 + m))|
      ≤ (0 : ℝ) ^ 2 / (2 * lam * (1 + m) ^ 2) :=
  EarthScience.isochron_age_slope_uncertainty hlam hm (le_refl 0)

/-- Helper bound at `u = 0`: `|log 1 - 0| = 0 ≤ 0`. -/
example : |Real.log (1 + (0 : ℝ)) - (0 : ℝ)| ≤ (0 : ℝ) ^ 2 / 2 :=
  EarthScience.log_one_add_abs_sub_le 0 (le_refl 0)
