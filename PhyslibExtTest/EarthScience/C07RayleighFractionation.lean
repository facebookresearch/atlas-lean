/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.C07RayleighFractionation

/-!
# Rayleigh fractionation checks

Concrete consumers of `PhyslibExt.EarthScience.C07RayleighFractionation`:
a numeric Rayleigh derivative, the endpoint `R(1) = R0`, and the
degenerate `α = 1` case where `R` is constant.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`R0 = 2`, `α = 3/2`, `f = 1/4`, the ratio is `1` and `dR/df = 2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.C07RayleighFractionation`
-/

/-- Numeric Rayleigh derivative with `R0 = 2`, `α = 3/2`, `f = 1/4`. -/
example : HasDerivAt (fun f : ℝ => 2 * f ^ ((3/2 : ℝ) - 1))
    (((3/2 : ℝ) - 1) * (2 * (1/4 : ℝ) ^ ((3/2 : ℝ) - 1)) / (1/4)) (1/4 : ℝ) :=
  EarthScience.rayleigh_hasDerivAt 2 (3/2) (1/4) (by norm_num)

/-- Numeric endpoint: `R(1) = 2`. -/
example : (2 : ℝ) * (1 : ℝ) ^ ((3/2 : ℝ) - 1) = 2 :=
  EarthScience.rayleigh_at_one 2 (3/2)

/-- Degenerate case `α = 1`: `R(f) = R0` is constant, derivative `0`. -/
example (R0 f : ℝ) (hf : 0 < f) :
    HasDerivAt (fun f : ℝ => R0 * f ^ ((1 : ℝ) - 1))
      (((1 : ℝ) - 1) * (R0 * f ^ ((1 : ℝ) - 1)) / f) f :=
  EarthScience.rayleigh_hasDerivAt R0 1 f hf
