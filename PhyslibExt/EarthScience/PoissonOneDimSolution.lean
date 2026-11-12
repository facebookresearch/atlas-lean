/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
/-!
# One-dimensional Poisson boundary problem: explicit solution

For the problem `-u'' = 1` on `(0, 1)` with `u(0) = u(1) = 0`, the
explicit solution is `u(x) = x * (1 - x) / 2`, with `u'(x) = (1 - 2*x)/2`
and `u''(x) = -1`.

## i. Overview

The three theorems below check the boundary data and the first two
derivatives of the explicit solution. No claim is made about uniqueness,
higher dimensions, or variable coefficients.

## ii. Key results

- `EarthScience.poisson_oneDim_solution_boundary`: `u(0) = u(1) = 0`.
- `EarthScience.poisson_oneDim_solution_hasDerivAt`: `u'(x) = (1 - 2*x)/2`.
- `EarthScience.poisson_oneDim_solution_second_hasDerivAt`: `u''(x) = -1`,
  i.e. `-u'' = 1`.

## iii. References

- `hasDerivAt_id'`, `HasDerivAt.const_sub`, `HasDerivAt.mul`,
  `HasDerivAt.div_const`, `HasDerivAt.const_mul` in Mathlib
  (`Mathlib/Analysis/Calculus/Deriv/`).
-/

@[expose] public section

namespace EarthScience

/-- One-dimensional Poisson problem `-u'' = 1` on `(0, 1)` with `u(0) = u(1) = 0`:
the explicit solution `u(x) = x * (1 - x) / 2` satisfies the boundary data. -/
theorem poisson_oneDim_solution_boundary :
    (fun x : ℝ => x * (1 - x) / 2) 0 = 0 ∧ (fun x : ℝ => x * (1 - x) / 2) 1 = 0 := by
  constructor <;> norm_num

/-- First derivative of the Poisson solution: `u'(x) = (1 - 2 * x) / 2`. -/
theorem poisson_oneDim_solution_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x : ℝ => x * (1 - x) / 2) ((1 - 2 * x) / 2) x := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have h2 : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1) x := HasDerivAt.const_sub 1 h1
  have hmul := h1.mul h2
  have hdiv := hmul.div_const (2 : ℝ)
  convert hdiv using 1
  ring

/-- Second derivative of the Poisson solution: `u''(x) = -1`, i.e. `-u'' = 1`. -/
theorem poisson_oneDim_solution_second_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x : ℝ => (1 - 2 * x) / 2) (-1) x := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) (2 * 1) x := HasDerivAt.const_mul 2 h1
  have hsub : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-(2 * 1)) x := HasDerivAt.const_sub 1 h2
  have hdiv := hsub.div_const (2 : ℝ)
  convert hdiv using 1
  norm_num

end EarthScience
