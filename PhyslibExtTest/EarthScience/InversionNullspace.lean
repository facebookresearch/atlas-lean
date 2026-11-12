/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.InversionNullspace

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-!
# Inversion nullspace checks

Concrete consumers of `PhyslibExt.EarthScience.InversionNullspace`:
`A = [[1, 2], [2, 4]]`, `s = [1, 1]`, `v = [2, -1]` (so `A *ᵥ v = 0` and
`A *ᵥ (s + v) = A *ᵥ s = [3, 6]`), rank deficiency, and the missing-ray
cell.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Rank-deficient matrix
- B. Missing-ray cell
- C. Full-rank recovery

## iv. References

- `PhyslibExt.EarthScience.InversionNullspace`
-/

/-- Rank deficiency: `[[1, 2], [2, 4]] *ᵥ [2, -1] = 0`. -/
example : Matrix.mulVec (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ) ![2, -1] = 0 := by
  ext i <;> fin_cases i <;>
    simp [Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons] <;> norm_num

/-- Rank deficiency: `s` and `s + v` give the same travel times. -/
example : Matrix.mulVec (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ) ![3, 0]
    = Matrix.mulVec (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] := by
  have h := EarthScience.travel_time_same_iff_nullspace
    (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] ![2, -1]
  have hv : Matrix.mulVec (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ) ![2, -1] = 0 := by
    ext i <;> fin_cases i <;>
      simp [Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons] <;> norm_num
  have h2 := h.mpr hv
  have hsum : (![1, 1] + ![2, -1] : Fin 2 → ℝ) = ![3, 0] := by
    ext i <;> fin_cases i <;> simp <;> norm_num
  rwa [hsum] at h2

/-- Missing-ray cell via the proved theorem. -/
example : Matrix.mulVec (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] = 0 :=
  EarthScience.missing_ray_nullspace.1

/-- Full-rank recovery: identity nullspace is trivial. -/
example (v : Fin 2 → ℝ)
    (hv : Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) v = 0) :
    v = 0 :=
  EarthScience.identity_nullspace_trivial v hv
