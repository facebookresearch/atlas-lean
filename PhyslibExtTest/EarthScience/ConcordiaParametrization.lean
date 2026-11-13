/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.ConcordiaParametrization

/-!
# Concordia-parametrization checks

Concrete consumers of `PhyslibExt.EarthScience.ConcordiaParametrization`:
with decay constants `l1 = 1`, `l2 = 2`, the concordia point at `t = 0` is
`(0, 0)`, at `t = 1` it is `(exp 1 - 1, exp 2 - 1)`, distinct times give
distinct points, and the logarithm recovers the time.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The boundary
case is `t = 0`, where both coordinates vanish, and a positive-time case
shows the first coordinate strictly increases and the time recovery works.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.ConcordiaParametrization`
-/

open EarthScience

/-- Boundary case: at `t = 0` the concordia point is `(0, 0)`. -/
example : concordiaPoint 1 2 0 = (0, 0) := by
  simp [concordiaPoint]

/-- At `t = 1` the point is `(exp 1 - 1, exp 2 - 1)`, with positive coordinates. -/
example : 0 < (concordiaPoint 1 2 1).1 ∧ 0 < (concordiaPoint 1 2 1).2 := by
  constructor <;> simp only [concordiaPoint]
  · have h1 : Real.exp (0 : ℝ) < Real.exp (1 * 1) :=
      Real.exp_lt_exp.mpr (by norm_num)
    rw [Real.exp_zero] at h1
    linarith
  · have h2 : Real.exp (0 : ℝ) < Real.exp (2 * 1) :=
      Real.exp_lt_exp.mpr (by norm_num)
    rw [Real.exp_zero] at h2
    linarith

/-- Distinct times give distinct concordia points: injectivity at `0` vs `1`. -/
example : concordiaPoint 1 2 0 ≠ concordiaPoint 1 2 1 := by
  intro h
  have hinj := concordia_injectiveOn (l1 := 1) (l2 := 2) (by norm_num) (by norm_num)
    (by norm_num : (1 : ℝ) ≠ 2)
  have := hinj (by norm_num : (0 : ℝ) ∈ Set.Ici 0) (by norm_num : (1 : ℝ) ∈ Set.Ici 0) h
  norm_num at this

/-- Time recovery: the logarithm of the first coordinate plus one, divided
by `l1 = 1`, returns `t = 1`. -/
example : Real.log ((concordiaPoint 1 2 1).1 + 1) / 1 = 1 := by
  have h := concordia_recover_time (l1 := 1) (l2 := 2) (by norm_num) (1 : ℝ)
  simpa using h

/-- First-coordinate strict monotonicity: `t = 0` gives a smaller first
coordinate than `t = 1`. -/
example : (concordiaPoint 1 2 0).1 < (concordiaPoint 1 2 1).1 :=
  concordia_first_strictMonoOn (l1 := 1) (l2 := 2) (by norm_num)
    (by norm_num : (0 : ℝ) ∈ Set.Ici 0) (by norm_num : (1 : ℝ) ∈ Set.Ici 0) (by norm_num)
