/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.CobbDouglas

/-!
# Tests for Cobb–Douglas demand

With `α = 1/3`, prices `(1, 2)` and wealth `6`, the demand is `(2, 2)` with utility `2`; the
affordable corner `(6, 0)` has utility `0`; the main theorem is instantiated, including at
zero wealth, where the demand is `(0, 0)`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Consumer.CobbDouglas

open Matrix MathlibExt.Economics.Consumer

example : cobbDouglasDemand (1 / 3) ![1, 2] 6 = ![2, 2] := by
  funext i
  fin_cases i <;> simp [cobbDouglasDemand] <;> norm_num

example : cobbDouglas (1 / 3) ![2, 2] = 2 := by
  have h23 : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  simp only [cobbDouglas, Matrix.cons_val_zero, Matrix.cons_val_one, h23]
  rw [← Real.rpow_add (show (0 : ℝ) < 2 by norm_num) (1 / 3) (2 / 3),
    show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]

example : cobbDouglas (1 / 3) ![6, 0] = 0 := by
  simp only [cobbDouglas, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
    Real.zero_rpow (show (2 / 3 : ℝ) ≠ 0 by norm_num), mul_zero]

example : IsMarshallianDemand (cobbDouglas (1 / 3)) twoGoodSet ![1, 2] 6 ![2, 2] := by
  have hdemand : cobbDouglasDemand (1 / 3) ![1, 2] 6 = ![2, 2] := by
    funext i
    fin_cases i <;> simp [cobbDouglasDemand] <;> norm_num
  rw [← hdemand]
  exact isMarshallianDemand_cobbDouglas (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp) (by norm_num)

example : cobbDouglasDemand (1 / 3) ![1, 2] 0 = ![0, 0] := by
  funext i
  fin_cases i <;> simp [cobbDouglasDemand]

example : IsMarshallianDemand (cobbDouglas (1 / 3)) twoGoodSet ![1, 2] 0 ![0, 0] := by
  have hdemand : cobbDouglasDemand (1 / 3) ![1, 2] 0 = ![0, 0] := by
    funext i
    fin_cases i <;> simp [cobbDouglasDemand]
  rw [← hdemand]
  exact isMarshallianDemand_cobbDouglas (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> simp) (by norm_num)

end MathlibExtTest.Economics.Consumer.CobbDouglas
