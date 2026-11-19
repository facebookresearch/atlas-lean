/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Labor.OaxacaBlinder
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExtTest.Economics.Labor.OaxacaBlinder

open MathlibExt.Economics.OaxacaBlinder MathlibExt.Probability.FiniteProbability Matrix

/-- Identity test: the mean gap `17 - 9` splits via `meanGap_eq`. -/
example : (17 : ℝ) - 9 =
    (((![1, 3] - ![1, 2] : Fin 2 → ℝ)) ⬝ᵥ ![1, 4]) +
    (((![1, 3] : Fin 2 → ℝ)) ⬝ᵥ ((![2, 5] - ![1, 4] : Fin 2 → ℝ))) := by
  have hA : (17 : ℝ) = ((![1, 3] : Fin 2 → ℝ) ⬝ᵥ ![2, 5]) := by
    simp [dotProduct, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hB : (9 : ℝ) = ((![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 4]) := by
    simp [dotProduct, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact meanGap_eq hA hB

/-- Identity test: the gap `8` is explained part `4` plus coefficient part `4`. -/
example : (17 : ℝ) - 9 = 4 + 4 := by
  have hA : (17 : ℝ) = ((![1, 3] : Fin 2 → ℝ) ⬝ᵥ ![2, 5]) := by
    simp [dotProduct, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hB : (9 : ℝ) = ((![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 4]) := by
    simp [dotProduct, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hdecomp := meanGap_eq (xA := (![1, 3] : Fin 2 → ℝ)) (xB := ![1, 2])
    (βA := ![2, 5]) (βB := ![1, 4]) (yA := 17) (yB := 9) hA hB
  have he : (((![1, 3] - ![1, 2] : Fin 2 → ℝ)) ⬝ᵥ ![1, 4]) = 4 := by
    simp [dotProduct, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    all_goals norm_num
  have hcf : (((![1, 3] : Fin 2 → ℝ)) ⬝ᵥ ((![2, 5] - ![1, 4] : Fin 2 → ℝ))) = 4 := by
    simp [dotProduct, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    all_goals norm_num
  rw [hdecomp, he, hcf]

/-- Bridge test: exact OLS fit, so `sampleMean y = 5` via the bridge theorem. -/
example : sampleMean (![3, 7] : Fin 2 → ℝ) = 5 := by
  have hfit : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 4] = ![3, 7] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    all_goals norm_num
  have hnormal : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ
      ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 4]) =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ ![3, 7] := by
    rw [hfit]
  have hc : ∀ i : Fin 2, (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) i 0 = 1 := by
    intro i
    fin_cases i <;> rfl
  have hbridge := sampleMean_eq_regressorMean_dotProduct
    (X := (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)) (y := ![3, 7]) (β := ![3, 4])
    0 hc hnormal
  have hreg : regressorMean (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) =
      ![1, 1 / 2] := by
    ext j
    fin_cases j <;> simp [regressorMean, sampleMean_eq_sum_div, Fin.sum_univ_two,
      Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hbridge, hreg]
  simp [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals norm_num

/-- End-to-end test: `sampleMean_sub_eq` on two concrete groups shows the gap `7/2`
is the explained part `1/2` plus the coefficient part `3`. -/
example : (7 : ℝ) / 2 = 1 / 2 + 3 := by
  have hfitA : (!![1, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 2] = ![5, 9] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    all_goals norm_num
  have hfitB : (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![2, 1] = ![3, 4] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    all_goals norm_num
  have hnormalA : (!![1, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ
      ((!![1, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 2]) =
      (!![1, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ ![5, 9] := by
    rw [hfitA]
  have hnormalB : (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ
      ((!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![2, 1]) =
      (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ ![3, 4] := by
    rw [hfitB]
  have hcA : ∀ i : Fin 2, (!![1, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ) i 0 = 1 := by
    intro i
    fin_cases i <;> rfl
  have hcB : ∀ i : Fin 2, (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) i 0 = 1 := by
    intro i
    fin_cases i <;> rfl
  have hmA : sampleMean (![5, 9] : Fin 2 → ℝ) = 7 := by
    simp only [sampleMean_eq_sum_div]
    simp [Fin.sum_univ_two, Fintype.card_fin, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    all_goals norm_num
  have hmB : sampleMean (![3, 4] : Fin 2 → ℝ) = 7 / 2 := by
    simp only [sampleMean_eq_sum_div]
    simp [Fin.sum_univ_two, Fintype.card_fin, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    all_goals norm_num
  have hrA : regressorMean (!![1, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ) =
      ![1, 2] := by
    ext j
    fin_cases j <;> simp [regressorMean, sampleMean_eq_sum_div, Fin.sum_univ_two,
      Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one]
    all_goals norm_num
  have hrB : regressorMean (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) =
      ![1, 3 / 2] := by
    ext j
    fin_cases j <;> simp [regressorMean, sampleMean_eq_sum_div, Fin.sum_univ_two,
      Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one]
    all_goals norm_num
  have hdecomp := sampleMean_sub_eq
    (XA := (!![1, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ))
    (XB := (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ))
    (yA := ![5, 9]) (yB := ![3, 4]) (βA := ![3, 2]) (βB := ![2, 1])
    0 hcA hcB hnormalA hnormalB
  rw [hmA, hmB, hrA, hrB] at hdecomp
  have he : (((![1, 2] - ![1, 3 / 2] : Fin 2 → ℝ)) ⬝ᵥ ![2, 1]) = 1 / 2 := by
    simp [dotProduct, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    all_goals norm_num
  have hcf : (((![1, 2] : Fin 2 → ℝ)) ⬝ᵥ ((![3, 2] - ![2, 1] : Fin 2 → ℝ))) = 3 := by
    simp [dotProduct, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    all_goals norm_num
  rw [he, hcf] at hdecomp
  have hgap : (7 : ℝ) - 7 / 2 = 7 / 2 := by norm_num
  rw [hgap] at hdecomp
  exact hdecomp

end MathlibExtTest.Economics.Labor.OaxacaBlinder