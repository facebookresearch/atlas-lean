/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.ZhangZagier

@[expose] public section

namespace MathlibExt.NumberTheory.Height

open Polynomial

/-- The reused Mathlib height has the source's primitive-polynomial normalization. -/
example (α : AlgebraicClosure ℚ) :
    NumberField.absLogHeight₁ α =
      (Real.log
        ‖((NumberField.primitiveIntMinpoly α).map (Int.castRingHom ℂ)).leadingCoeff‖ +
        (((NumberField.primitiveIntMinpoly α).map (Int.castRingHom ℂ)).roots.map
          (fun z => Real.log (max 1 ‖z‖))).sum) /
        ((minpoly ℚ α).natDegree : ℝ) := by
  rw [AbsoluteWanted.absLogHeight₁_eq_log_leadingCoeff_add_sum_log_roots]
  simp_rw [Real.posLog_eq_log_max_one (norm_nonneg _)]

example :
    zhangZagierHeight (0 : AlgebraicClosure ℚ) =
      NumberField.absLogHeight₁ (0 : AlgebraicClosure ℚ) +
        NumberField.absLogHeight₁ (1 - (0 : AlgebraicClosure ℚ)) :=
  rfl

example :
    zhangZagierHeight (1 : AlgebraicClosure ℚ) =
      NumberField.absLogHeight₁ (1 : AlgebraicClosure ℚ) +
        NumberField.absLogHeight₁ (1 - (1 : AlgebraicClosure ℚ)) :=
  rfl

example (α : AlgebraicClosure ℚ) :
    α ∈ zhangZagierSublevelSet (zhangZagierHeight α) := by
  simp [zhangZagierSublevelSet]

example : IsZhangZagierFiniteThreshold (-1) :=
  isZhangZagierFiniteThreshold_of_neg (by norm_num)

example : 0 ≤ zhangZagierEssentialMinimum :=
  zero_le_zhangZagierEssentialMinimum

example : (0.39679 : ℝ) = 39679 / 100000 := by norm_num
example : (0.25594 : ℝ) = 25594 / 100000 := by norm_num
example : (0.25444 : ℝ) = 25444 / 100000 := by norm_num
example : (0.2536331090204145 : ℝ) = 2536331090204145 / 10000000000000000 := by norm_num
example : (0.24824 : ℝ) = 24824 / 100000 := by norm_num
example : (0.24874 : ℝ) = 24874 / 100000 := by norm_num

end MathlibExt.NumberTheory.Height
