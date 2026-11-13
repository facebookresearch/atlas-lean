/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.IsochronAgeInvertsSlope

import Mathlib.Tactic.NormNum

/-!
# Isochron slope inversion checks

Concrete consumers of `PhyslibExt.EarthScience.IsochronAgeInvertsSlope`:
a generic elaboration check, the unit case `λ = 1, m = 1` (age
`log 2`), and a second concrete case `λ = 2, m = 3`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.IsochronAgeInvertsSlope`
-/

/-- Generic elaboration: the theorem applies to any `λ > 0` and
`m > 0`. -/
example {lam m : ℝ} (hlam : 0 < lam) (hm : 0 < m) :
    Real.exp (lam * (Real.log (1 + m) / lam)) - 1 = m
      ∧ 0 ≤ Real.log (1 + m) / lam :=
  EarthScience.isochron_age_inverts_slope hlam hm

/-- Unit case: `λ = 1, m = 1` gives age `log 2`, whose slope is
`exp (log 2) - 1 = 1`. -/
example :
    Real.exp (1 * (Real.log (1 + (1 : ℝ)) / 1)) - 1 = 1
      ∧ 0 ≤ Real.log (1 + (1 : ℝ)) / 1 :=
  EarthScience.isochron_age_inverts_slope (by norm_num) (by norm_num)

/-- Concrete case: `λ = 2, m = 3` gives age `log 4 / 2`, whose slope
is `3`. -/
example :
    Real.exp (2 * (Real.log (1 + (3 : ℝ)) / 2)) - 1 = 3
      ∧ 0 ≤ Real.log (1 + (3 : ℝ)) / 2 :=
  EarthScience.isochron_age_inverts_slope (by norm_num) (by norm_num)
