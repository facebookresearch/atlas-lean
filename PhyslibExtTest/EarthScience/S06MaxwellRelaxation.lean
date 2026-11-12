/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.S06MaxwellRelaxation

/-!
# Maxwell relaxation checks

Concrete consumers of `PhyslibExt.EarthScience.S06MaxwellRelaxation`:
`μ = 2`, `η = 10`, `σ₀ = 7` (relaxation time `5`, `σ(5) = 7 / e`), plus
the zero-initial-stress boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric relaxation
- B. Zero initial stress

## iv. References

- `PhyslibExt.EarthScience.S06MaxwellRelaxation`
-/

/-- Numeric relaxation: `σ` obeys the Maxwell ODE at `t = 5`. -/
example : HasDerivAt (fun t => (7 : ℝ) * Real.exp (-(2 / 10) * t))
    (-(2 / 10) * ((7 : ℝ) * Real.exp (-(2 / 10) * 5))) 5 :=
  EarthScience.hasDerivAt_maxwell_relaxation (by norm_num) (by norm_num)

/-- Numeric relaxation: initial value and nonnegativity. -/
example : (7 : ℝ) * Real.exp (-(2 / 10) * 0) = 7 ∧
    0 ≤ (7 : ℝ) * Real.exp (-(2 / 10) * 5) :=
  EarthScience.maxwell_relaxation_initial_nonneg (by norm_num)

/-- Numeric relaxation: after one relaxation time `η / μ = 5`, `σ = 7 / e`. -/
example : (7 : ℝ) * Real.exp (-(2 / 10) * (10 / 2)) = 7 / Real.exp 1 :=
  EarthScience.maxwell_relaxation_at_relaxation_time (by norm_num) (by norm_num)

/-- Zero initial stress: the stress stays zero and obeys the ODE. -/
example : HasDerivAt (fun t => (0 : ℝ) * Real.exp (-(2 / 10) * t))
    (-(2 / 10) * ((0 : ℝ) * Real.exp (-(2 / 10) * 5))) 5 :=
  EarthScience.hasDerivAt_maxwell_relaxation (μ := 2) (η := 10) (σ₀ := 0) (t := 5)
    (by norm_num) (by norm_num)
