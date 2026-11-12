/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.PoissonOneDimSolution

/-!
# One-dimensional Poisson solution checks

Concrete consumers of `PhyslibExt.EarthScience.PoissonOneDimSolution`:
the boundary data, the derivative at the midpoint `x = 1/2` (where
`u' = 0` and `u = 1/8`), and the constant second derivative.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.PoissonOneDimSolution`
-/

/-- Boundary data: `u(0) = u(1) = 0`. -/
example : (fun x : ℝ => x * (1 - x) / 2) 0 = 0 ∧ (fun x : ℝ => x * (1 - x) / 2) 1 = 0 :=
  EarthScience.poisson_oneDim_solution_boundary

/-- At the midpoint `x = 1/2`, the solution peaks with derivative `0`. -/
example : HasDerivAt (fun x : ℝ => x * (1 - x) / 2) 0 (1 / 2) := by
  have h := EarthScience.poisson_oneDim_solution_hasDerivAt (1 / 2 : ℝ)
  norm_num at h
  exact h

/-- At `x = 1/4`, the solution is `3/32` with derivative `1/4`. -/
example : HasDerivAt (fun x : ℝ => x * (1 - x) / 2) (1 / 4) (1 / 4) := by
  have h := EarthScience.poisson_oneDim_solution_hasDerivAt (1 / 4 : ℝ)
  norm_num at h
  exact h

/-- Second derivative is the constant `-1`, so `-u'' = 1`. -/
example (x : ℝ) : HasDerivAt (fun x : ℝ => (1 - 2 * x) / 2) (-1) x :=
  EarthScience.poisson_oneDim_solution_second_hasDerivAt x
