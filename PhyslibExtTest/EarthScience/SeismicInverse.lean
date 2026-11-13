/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.SeismicInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Seismic-inverse capstone checks

Concrete consumers of `PhyslibExt.EarthScience.SeismicInverse`:
travel times `[3 / 4, 1]`, inversion recovering `[1 / 2, 1 / 4]`,
the null direction, the algebraic single-row ambiguity at `t = 2` (where
`s + 2 * [1, -1] = [5 / 2, -7 / 4]` still gives row dot `3 / 4`, but has
a negative component), the positive-slowness ambiguity at `t = 1 / 8`
(where `s + (1 / 8) * [1, -1] = [5 / 8, 1 / 8]`), and the
missing-receiver analogue (row `[1, 0]` alone cannot distinguish `s`
from `s + [0, 1]`).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Travel times, inversion, ambiguity

## iv. References

- `PhyslibExt.EarthScience.SeismicInverse`
-/

/-- Travel times `[3 / 4, 1]`. -/
example : Matrix.mulVec (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ)
      (![1 / 2, 1 / 4] : Fin 2 → ℚ) = ![3 / 4, 1] :=
  EarthScience.travel_times_value

/-- Inversion recovers `[1 / 2, 1 / 4]`. -/
example : ∀ x : Fin 2 → ℚ,
    Matrix.mulVec (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ) x = ![3 / 4, 1] →
      x = ![1 / 2, 1 / 4] :=
  fun _ h => EarthScience.inversion_recovers_slowness h

/-- Null direction. -/
example : (![1, 1] : Fin 2 → ℚ) ⬝ᵥ (![1, -1] : Fin 2 → ℚ) = (0 : ℚ) ∧
    (![1, -1] : Fin 2 → ℚ) ≠ 0 :=
  EarthScience.single_row_null_direction

/-- Single-row ambiguity at `t = 2`: `s + 2 * [1, -1]` still gives row dot `3 / 4`. -/
example : (![1, 1] : Fin 2 → ℚ) ⬝ᵥ
      ((![1 / 2, 1 / 4] : Fin 2 → ℚ) + (2 : ℚ) • (![1, -1] : Fin 2 → ℚ))
    = (![1, 1] : Fin 2 → ℚ) ⬝ᵥ (![1 / 2, 1 / 4] : Fin 2 → ℚ) :=
  EarthScience.single_row_ambiguity (t := 2)

/-- Positive-slowness ambiguity at `t = 1 / 8`: the distinct model
`[5 / 8, 1 / 8]` has positive slowness and the same single-row travel
time `3 / 4` as `s`. -/
example :
    (∀ i, 0 < ((![1 / 2, 1 / 4] : Fin 2 → ℚ) + (1 / 8 : ℚ) • (![1, -1] : Fin 2 → ℚ)) i) ∧
      (![1 / 2, 1 / 4] : Fin 2 → ℚ) + (1 / 8 : ℚ) • (![1, -1] : Fin 2 → ℚ)
        ≠ (![1 / 2, 1 / 4] : Fin 2 → ℚ) ∧
      (![1, 1] : Fin 2 → ℚ) ⬝ᵥ
          ((![1 / 2, 1 / 4] : Fin 2 → ℚ) + (1 / 8 : ℚ) • (![1, -1] : Fin 2 → ℚ))
        = (![1, 1] : Fin 2 → ℚ) ⬝ᵥ (![1 / 2, 1 / 4] : Fin 2 → ℚ) :=
  EarthScience.single_row_positive_ambiguity (by norm_num) (by norm_num) (by norm_num)

/-- The `t = 1 / 8` perturbation is the explicit model `[5 / 8, 1 / 8]`. -/
example : (![1 / 2, 1 / 4] : Fin 2 → ℚ) + (1 / 8 : ℚ) • (![1, -1] : Fin 2 → ℚ)
    = ![5 / 8, 1 / 8] := by
  ext i
  fin_cases i <;> simp <;> norm_num

/-- Missing-receiver analogue: row `[1, 0]` alone cannot distinguish
`s` from `s + [0, 1]`: both give `1 / 2`. -/
example : (![1, 0] : Fin 2 → ℚ) ⬝ᵥ (![1 / 2, 1 / 4] : Fin 2 → ℚ)
    = (![1, 0] : Fin 2 → ℚ) ⬝ᵥ (![1 / 2, 5 / 4] : Fin 2 → ℚ) := by
  simp [dotProduct]
