/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Reliability.WeibullComponent
import Mathlib.Tactic.NormNum

/-!
# Weibull-component checks

Focused checks for `MathlibExt.Probability.Reliability.WeibullComponent`:
survival at time zero is exactly one; the exponential case at
`l = 2`, `t = 1`; an invalid shape gives the zero measure.

These are elaboration and non-vacuity checks, not new results.
-/

open Reliability ProbabilityTheory Set

/-- Survival at time zero is one. -/
example : (weibullMeasure 2 3).real (Ioi 0) = 1 := by
  have h := (weibull_component_survival (k := 2) (l := 3) (t := 0)
    (by norm_num) (by norm_num) (by norm_num)).1
  rw [h]
  norm_num

/-- Exponential case. -/
example : (weibullMeasure 1 2).real (Ioi 1) = Real.exp (-1 / 2) :=
  weibull_component_exponential (by norm_num) (by norm_num)

/-- Invalid shape gives the zero measure. -/
example : weibullMeasure 0 1 = 0 :=
  weibull_invalid_parameters (by simp)
