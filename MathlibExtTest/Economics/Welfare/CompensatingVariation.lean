/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Welfare.CompensatingVariation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for compensating variation

For the perfect-complements utility `min x₀ x₁` at wealth `4` and baseline prices `(1, 1)`
(baseline utility `2`): a price rise to `(1, 3)` has `CV = -4`; a price fall to `(1/2, 1/2)` has
`CV = 2`, consistent with `compensatingVariation_nonneg_of_le`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Welfare.CompensatingVariation

open Matrix

example : MathlibExt.Economics.Consumer.compensatingVariation
    (fun x => min (x 0) (x 1))
    MathlibExt.Economics.Consumer.twoGoodSet ![1, 1] ![1, 3] 4 = -4 := by
  have hp0 : ∀ i, (0:ℝ) < (![1, 1] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hp1 : ∀ i, (0:ℝ) < (![1, 3] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hw : (0:ℝ) ≤ 4 := by norm_num
  rw [MathlibExt.Economics.Consumer.compensatingVariation_min hp0 hp1 hw]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

example : MathlibExt.Economics.Consumer.compensatingVariation
    (fun x => min (x 0) (x 1))
    MathlibExt.Economics.Consumer.twoGoodSet ![1, 1] ![1/2, 1/2] 4 = 2 := by
  have hp0 : ∀ i, (0:ℝ) < (![1, 1] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hp1 : ∀ i, (0:ℝ) < (![1/2, 1/2] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hw : (0:ℝ) ≤ 4 := by norm_num
  rw [MathlibExt.Economics.Consumer.compensatingVariation_min hp0 hp1 hw]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

example : 0 ≤ MathlibExt.Economics.Consumer.compensatingVariation
    (fun x => min (x 0) (x 1))
    MathlibExt.Economics.Consumer.twoGoodSet ![1, 1] ![1/2, 1/2] 4 := by
  apply MathlibExt.Economics.Consumer.compensatingVariation_nonneg_of_le
  · intro x hx i
    exact hx i
  · intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

example : MathlibExt.Economics.Consumer.indirectUtility
    (fun x => min (x 0) (x 1)) MathlibExt.Economics.Consumer.twoGoodSet ![1, 1] 4 = 2 := by
  have hp0 : ∀ i, (0:ℝ) < (![1, 1] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hw : (0:ℝ) ≤ 4 := by norm_num
  rw [MathlibExt.Economics.Consumer.indirectUtility_min hp0 hw]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

example : MathlibExt.Economics.Consumer.expenditure
    (fun x => min (x 0) (x 1)) MathlibExt.Economics.Consumer.twoGoodSet ![1, 3] 2 = 8 := by
  have hp1 : ∀ i, (0:ℝ) < (![1, 3] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hu : (0:ℝ) ≤ 2 := by norm_num
  rw [MathlibExt.Economics.Consumer.expenditure_min hp1 hu]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

end MathlibExtTest.Economics.Welfare.CompensatingVariation
