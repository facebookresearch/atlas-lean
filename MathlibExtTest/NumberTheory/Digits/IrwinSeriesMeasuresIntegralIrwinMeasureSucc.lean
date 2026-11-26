/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresIntegralIrwinMeasureSucc

/-!
# Tests for digit decomposition of the Irwin measures, positive index
-/

namespace MathlibExtTest.NumberTheory.Digits.IrwinSeriesMeasuresIntegralIrwinMeasureSucc

open scoped BigOperators
open MeasureTheory
open MetaMathlibExt

private theorem isBounded_id_image_Ico (b : ℕ) :
    Bornology.IsBounded ((id : ℝ → ℝ) '' Set.Ico (0 : ℝ) (b : ℝ)) := by
  rw [Set.image_id]
  exact Metric.isBounded_Ico _ _

-- The digit decomposition applies to the identity function in base 10.
example : (∫ x in Set.Ico (0 : ℝ) 1, (10 : ℝ) * x
      ∂irwinMeasure 10 3 1 (by decide))
    = (1 / (10 : ℝ)) *
        (∑ a ∈ Finset.range 10,
          if a = 3 then 0 else
            ∫ x in Set.Ico (0 : ℝ) 1, ((a : ℝ) + x) ∂irwinMeasure 10 3 1 (by decide)) +
      (1 / (10 : ℝ)) *
        ∫ x in Set.Ico (0 : ℝ) 1, ((3 : ℝ) + x) ∂irwinMeasure 10 3 0 (by decide) := by
  have h := MetaMathlibExt.integral_irwinMeasure_succ 10 3 (by decide) (by decide) id
    measurable_id (isBounded_id_image_Ico 10) 1 le_rfl
  simpa using h

-- In base 2 the decomposition splits off the digit `0` at index 2.
example : (∫ x in Set.Ico (0 : ℝ) 1, (2 : ℝ) * x
      ∂irwinMeasure 2 0 2 (by decide))
    = (1 / (2 : ℝ)) *
        (∑ a ∈ Finset.range 2,
          if a = 0 then 0 else
            ∫ x in Set.Ico (0 : ℝ) 1, ((a : ℝ) + x) ∂irwinMeasure 2 0 2 (by decide)) +
      (1 / (2 : ℝ)) *
        ∫ x in Set.Ico (0 : ℝ) 1, ((0 : ℝ) + x) ∂irwinMeasure 2 0 1 (by decide) := by
  have h := MetaMathlibExt.integral_irwinMeasure_succ 2 0 (by decide) (by decide) id
    measurable_id (isBounded_id_image_Ico 2) 2 (by decide)
  simpa using h

end MathlibExtTest.NumberTheory.Digits.IrwinSeriesMeasuresIntegralIrwinMeasureSucc
