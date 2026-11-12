/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.InputOutput.Leontief
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

namespace MathlibExtTest.Economics.InputOutput.Leontief

open MathlibExt.Economics.InputOutput
open Matrix

noncomputable def A2 : Matrix (Fin 2) (Fin 2) ℝ := ![![(1/2 : ℝ), 0], ![1/4, 1/2]]

noncomputable def A1 : Matrix (Fin 1) (Fin 1) ℝ := ![![(1 : ℝ)]]

example : IsGrossOutput A2 ![1, 1] ![2, 3] := by
  unfold IsGrossOutput A2
  funext i
  fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_two]

example : (1 - A2) *ᵥ ![2, 3] = ![1, 1] := by
  have h : IsGrossOutput A2 ![1, 1] ![2, 3] := by
    unfold IsGrossOutput A2
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_two]
  exact (isGrossOutput_iff.mp h)

theorem singular_all_gross (x : Fin 1 → ℝ) : IsGrossOutput A1 0 x := by
  apply isGrossOutput_iff.mpr
  have h : (1 : Matrix (Fin 1) (Fin 1) ℝ) - A1 = 0 := by
    ext i j
    rw [Matrix.sub_apply, Matrix.zero_apply]
    fin_cases i; fin_cases j
    simp [A1, Matrix.one_apply_eq]
  rw [h, Matrix.zero_mulVec]

end MathlibExtTest.Economics.InputOutput.Leontief