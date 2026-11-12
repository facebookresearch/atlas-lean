/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import PhyslibExt.EarthScience.Interpolation

/-!
# Spatial interpolation and gridded data

Concrete consumers of `PhyslibExt.EarthScience.Interpolation`.

## i. Overview

Three-point weights `0.2, 0.3, 0.5` preserving a constant and staying in
range.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.Interpolation`
-/

/-- Three-point constant field: weights `0.2, 0.3, 0.5`, value `7`. -/
example : ∑ i : Fin 3, (![0.2, 0.3, 0.5] : Fin 3 → ℝ) i * (7 : ℝ) = 7 := by
  have hw : ∑ i : Fin 3, (![0.2, 0.3, 0.5] : Fin 3 → ℝ) i = 1 := by
    rw [Fin.sum_univ_three]
    norm_num
  exact EarthScience.interpolation_preserves_constant Finset.univ _ 7 hw

/-- Three-point range: samples `1, 4, 6` combine to `4.4 ∈ [1, 6]`. -/
example : 1 ≤ ∑ i : Fin 3, (![0.2, 0.3, 0.5] : Fin 3 → ℝ) i *
      (![1, 4, 6] : Fin 3 → ℝ) i ∧
    ∑ i : Fin 3, (![0.2, 0.3, 0.5] : Fin 3 → ℝ) i *
      (![1, 4, 6] : Fin 3 → ℝ) i ≤ 6 := by
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ (![0.2, 0.3, 0.5] : Fin 3 → ℝ) i := by
    intro i _
    fin_cases i <;> norm_num
  have hw : ∑ i : Fin 3, (![0.2, 0.3, 0.5] : Fin 3 → ℝ) i = 1 := by
    rw [Fin.sum_univ_three]
    norm_num
  have hy : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      1 ≤ (![1, 4, 6] : Fin 3 → ℝ) i ∧ (![1, 4, 6] : Fin 3 → ℝ) i ≤ 6 := by
    intro i _
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact EarthScience.interpolation_mem_range Finset.univ _ _ 1 6 hw0 hw hy
