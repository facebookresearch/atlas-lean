/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ideal monoprotic acid: the positive hydrogen concentration is unique

## i. Overview

For an ideal monoprotic acid with fixed total `C > 0` and `K > 0`,
a hydrogen concentration `h > 0` satisfying `h ^ 2 + K * h - K * C = 0`
is uniquely `(-K + sqrt (K ^ 2 + 4 * K * C)) / 2`, and that candidate is
positive and satisfies the equation. Water autoionization is omitted;
this is one chosen ideal model, not general carbonate uniqueness.
`K` and `C` share a concentration scale; pH logs dimensionless activity.

## ii. Key results

- `EarthScience.monoprotic_acid_h_unique`: uniqueness of the positive root.
- `EarthScience.monoprotic_acid_h_exists`: the candidate root is positive
  and satisfies the equation.

## iii. Table of contents

- A. Uniqueness
- B. Existence of the positive root

## iv. References

- `Real.sq_sqrt`, `Real.lt_sqrt`, `Real.sqrt_sq` in Mathlib.
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Uniqueness: for ideal monoprotic acid with total `C > 0` and
`K > 0`, a hydrogen concentration `h > 0` satisfying
`h ^ 2 + K * h - K * C = 0` is uniquely
`(-K + sqrt (K ^ 2 + 4 * K * C)) / 2`. -/
theorem monoprotic_acid_h_unique {K C h : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hh : 0 < h) (heq : h ^ 2 + K * h - K * C = 0) :
    h = (-K + Real.sqrt (K ^ 2 + 4 * K * C)) / 2 := by
  have hsq : (2 * h + K) ^ 2 = K ^ 2 + 4 * K * C := by linear_combination 4 * heq
  have hpos : 0 < 2 * h + K := by linarith
  have hsqrt : 2 * h + K = Real.sqrt (K ^ 2 + 4 * K * C) := by
    rw [← Real.sqrt_sq (le_of_lt hpos), hsq]
  linarith

/-- The candidate root is positive and satisfies the equilibrium equation. -/
theorem monoprotic_acid_h_exists {K C : ℝ} (hK : 0 < K) (hC : 0 < C) :
    0 < (-K + Real.sqrt (K ^ 2 + 4 * K * C)) / 2 ∧
      ((-K + Real.sqrt (K ^ 2 + 4 * K * C)) / 2) ^ 2
        + K * ((-K + Real.sqrt (K ^ 2 + 4 * K * C)) / 2) - K * C = 0 := by
  have hD : 0 ≤ K ^ 2 + 4 * K * C := by positivity
  have hsq : (Real.sqrt (K ^ 2 + 4 * K * C)) ^ 2 = K ^ 2 + 4 * K * C :=
    Real.sq_sqrt hD
  have hlt : K < Real.sqrt (K ^ 2 + 4 * K * C) := by
    rw [Real.lt_sqrt (le_of_lt hK)]
    have h4KC : 0 < 4 * K * C := by positivity
    linarith
  refine ⟨by linarith, by linear_combination hsq / 4⟩

end EarthScience
