/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import PhyslibExt.EarthScience.HydraulicJump

/-!
# Hydraulic-jump conjugate-depth checks

Concrete consumers of `PhyslibExt.EarthScience.HydraulicJump`: for
`g = 1`, depths `1` and `2` are conjugate exactly when `q ^ 2 = 3`, with
common specific force `7 / 2`. The equal-depth and zero-discharge cases
check that the unequal-depth hypothesis of the theorem cannot be dropped.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. The `g = 1`, depths `1, 2` witness
- B. Boundary and negative controls
- C. Public theorem shape

## iv. References

- `PhyslibExt.EarthScience.HydraulicJump`
-/

open EarthScience

/-! ## A. The `g = 1`, depths `1, 2` witness -/

/-- With `q = √3`, `g = 1`, the specific force at depth `1` is `7 / 2`. -/
example : rectangularSpecificForce (Real.sqrt 3) 1 1 = 7 / 2 := by
  unfold rectangularSpecificForce
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-- With `q = √3`, `g = 1`, the specific force at depth `2` is also `7 / 2`. -/
example : rectangularSpecificForce (Real.sqrt 3) 1 2 = 7 / 2 := by
  unfold rectangularSpecificForce
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-- The theorem applied to the witness: depths `1` and `2` at `g = 1` are
conjugate for unit discharge `√3`, i.e. `(√3) ^ 2 = 1 * 1 * 2 * (1 + 2) / 2`. -/
example : (Real.sqrt 3) ^ 2 = (1:ℝ) * 1 * 2 * (1 + 2) / 2 := by
  have hM : rectangularSpecificForce (Real.sqrt 3) 1 1
      = rectangularSpecificForce (Real.sqrt 3) 1 2 := by
    unfold rectangularSpecificForce
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  exact specific_force_conjugate_depths (q := Real.sqrt 3) (g := (1:ℝ))
    (h1 := (1:ℝ)) (h2 := (2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hM

/-! ## B. Boundary and negative controls -/

/-- At zero discharge the specific force is the hydrostatic term `h ^ 2 / 2`. -/
example (g h : ℝ) : rectangularSpecificForce 0 g h = h ^ 2 / 2 := by
  simp [rectangularSpecificForce]

/-- Equal depths give equal specific force for every discharge, but the
conjugate-depth conclusion at `q = 0`, `g = 1`, `h = 1` would read `0 = 1`:
the unequal-depth hypothesis is necessary. -/
example : rectangularSpecificForce 0 1 1 = rectangularSpecificForce 0 1 1
    ∧ ¬ ((0:ℝ) ^ 2 = (1:ℝ) * 1 * 1 * (1 + 1) / 2) := by
  constructor
  · rfl
  · norm_num

/-! ## C. Public theorem shape -/

/-- The public statement, restated through the definition. -/
example {q g h1 h2 : ℝ} (hg : 0 < g) (hh1 : 0 < h1) (hh2 : 0 < h2)
    (hne : h1 ≠ h2) (hM : h1 ^ 2 / 2 + q ^ 2 / (g * h1)
      = h2 ^ 2 / 2 + q ^ 2 / (g * h2)) :
    q ^ 2 = g * h1 * h2 * (h1 + h2) / 2 :=
  specific_force_conjugate_depths hg hh1 hh2 hne hM
