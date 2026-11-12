/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.C05RadioactiveDecay

/-!
# Radioactive decay checks

Concrete consumers of `PhyslibExt.EarthScience.C05RadioactiveDecay`: a
numeric decay law, the half-life value, uniqueness, and the `t = 0`
boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`λ = 1/2` and `N0 = 10`, the half-life is `2*log 2` and `N = 5` there.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.C05RadioactiveDecay`
-/

/-- Numeric decay law with `λ = 1/2`, `N0 = 10`. -/
example (t : ℝ) : HasDerivAt (fun t : ℝ => 10 * Real.exp (-(1/2) * t))
    (-(1/2) * (10 * Real.exp (-(1/2) * t))) t :=
  EarthScience.decay_hasDerivAt (1/2) 10 t

/-- Numeric half-life value: at `log 2 / (1/2)`, half of `10` remains. -/
example : (10 : ℝ) * Real.exp (-(1/2) * (Real.log 2 / (1/2))) = 10 / 2 :=
  EarthScience.decay_halfLife_value (1/2) 10 (by norm_num) (by norm_num)

/-- Numeric half-life uniqueness: `t ≥ 0` with `N(t) = 5` is the half-life. -/
example (t : ℝ) (ht : 0 ≤ t)
    (h : (10 : ℝ) * Real.exp (-(1/2) * t) = 10 / 2) :
    t = Real.log 2 / (1/2) :=
  EarthScience.decay_halfLife_unique (1/2) 10 t (by norm_num) (by norm_num) ht h

/-- Boundary case `t = 0`: the inventory is the initial inventory. -/
example : (10 : ℝ) * Real.exp (-(1/2) * 0) = 10 := by
  simp
