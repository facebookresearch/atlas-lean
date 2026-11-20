/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Inequality.ProgressiveTransfer
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Tactic

@[expose] public section

namespace MathlibExtTest.Economics.Inequality.ProgressiveTransfer

open MathlibExt.Economics.Inequality
open scoped Matrix

theorem convex_sq : ConvexOn ℝ Set.univ fun y : ℝ => y ^ 2 :=
  Even.convexOn_pow (by decide : Even (2 : ℕ))

theorem transfer_one : transfer (![1, 5] : Fin 2 → ℝ) 0 1 1 = ![2, 4] := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  refine funext (Fin.forall_fin_two.mpr ?_)
  constructor
  · simp only [transfer, Function.update_apply, h01, Matrix.cons_val_one,
      Matrix.cons_val_zero, ite_true, ite_false]
    norm_num
  · simp only [transfer, Function.update_apply, h10, Matrix.cons_val_one,
      Matrix.cons_val_zero, ite_true, ite_false]
    norm_num

theorem index_before : separableIndex (fun y : ℝ => y ^ 2) (![1, 5] : Fin 2 → ℝ) = 13 := by
  simp [separableIndex, Fin.sum_univ_two, Matrix.cons_val_one, Fintype.card_fin]
  norm_num

theorem index_after :
    separableIndex (fun y : ℝ => y ^ 2) (transfer (![1, 5] : Fin 2 → ℝ) 0 1 1) = 10 := by
  rw [transfer_one]
  simp [separableIndex, Fin.sum_univ_two, Matrix.cons_val_one, Fintype.card_fin]
  norm_num

theorem pigou_dalton_ex :
    separableIndex (fun y : ℝ => y ^ 2) (transfer (![1, 5] : Fin 2 → ℝ) 0 1 1)
      ≤ separableIndex (fun y : ℝ => y ^ 2) (![1, 5] : Fin 2 → ℝ) := by
  have hδ : (1 : ℝ) ≤ (![1, 5] : Fin 2 → ℝ) 1 - (![1, 5] : Fin 2 → ℝ) 0 := by
    simp [Matrix.cons_val_one]
    norm_num
  exact separableIndex_transfer_le convex_sq _ (by decide : (0 : Fin 2) ≠ 1)
    (Set.mem_univ _) (Set.mem_univ _) zero_le_one hδ

theorem pigou_dalton_nums : (10 : ℝ) ≤ 13 := by
  have h := pigou_dalton_ex
  rw [index_after, index_before] at h
  exact h

theorem sum_transfer_ex : ∑ k, transfer (![1, 5] : Fin 2 → ℝ) 0 1 1 k
    = ∑ k, (![1, 5] : Fin 2 → ℝ) k :=
  sum_transfer _ (by decide : (0 : Fin 2) ≠ 1) _

theorem transfer_bad : transfer (![1, 5] : Fin 2 → ℝ) 0 1 5 = ![6, 0] := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  refine funext (Fin.forall_fin_two.mpr ?_)
  constructor
  · simp only [transfer, Function.update_apply, h01, Matrix.cons_val_one,
      Matrix.cons_val_zero, ite_true, ite_false]
    norm_num
  · simp only [transfer, Function.update_apply, h10, Matrix.cons_val_one,
      Matrix.cons_val_zero, ite_true, ite_false]
    norm_num

theorem index_bad :
    separableIndex (fun y : ℝ => y ^ 2) (transfer (![1, 5] : Fin 2 → ℝ) 0 1 5) = 18 := by
  rw [transfer_bad]
  simp [separableIndex, Fin.sum_univ_two, Matrix.cons_val_one, Fintype.card_fin]
  norm_num

theorem regressive_worse :
    separableIndex (fun y : ℝ => y ^ 2) (![1, 5] : Fin 2 → ℝ)
      < separableIndex (fun y : ℝ => y ^ 2) (transfer (![1, 5] : Fin 2 → ℝ) 0 1 5) := by
  rw [index_before, index_bad]
  norm_num

end MathlibExtTest.Economics.Inequality.ProgressiveTransfer