/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.CoefficientT
import Mathlib.LinearAlgebra.Matrix.Notation

namespace MathlibExtTest.LinearModelCoefficientT

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

noncomputable def X₀ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun _ _ => 1

example : coefficientTStatistic X₀ 0 ![0] ![2, 4, 6] = 2 * Real.sqrt 3 := by
  have hM : X₀ᵀ * X₀ = Matrix.of fun _ _ : Fin 1 => (3 : ℝ) := by
    ext i j
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, X₀, Matrix.of_apply, Fin.sum_univ_three]
  have hMinv : (X₀ᵀ * X₀)⁻¹ = Matrix.of fun _ _ : Fin 1 => (1 / 3 : ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [hM]
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    norm_num [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one, Matrix.one_apply, hij]
  have hβ : olsEstimator X₀ ![2, 4, 6] = ![4] := by
    unfold olsEstimator
    rw [olsMatrix_eq, hMinv]
    ext i
    norm_num [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, X₀,
      Matrix.of_apply, Fin.sum_univ_three, Fin.sum_univ_one]
  have hres : (![2, 4, 6] - X₀ *ᵥ olsEstimator X₀ ![2, 4, 6] : Fin 3 → ℝ)
      = ![-2, 0, 2] := by
    rw [hβ]
    ext i
    fin_cases i <;>
      norm_num [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, X₀,
        Matrix.of_apply, Fin.sum_univ_one]
  have hRSS : ((![2, 4, 6] - X₀ *ᵥ olsEstimator X₀ ![2, 4, 6] : Fin 3 → ℝ) ⬝ᵥ
      (![2, 4, 6] - X₀ *ᵥ olsEstimator X₀ ![2, 4, 6])) = 8 := by
    rw [hres]
    norm_num [dotProduct, Fin.sum_univ_three]
  have hdiag : (X₀ᵀ * X₀)⁻¹ 0 0 = 1 / 3 := by
    simp [hMinv]
  have hcast : ((Fintype.card (Fin 3) - Fintype.card (Fin 1) : ℕ) : ℝ) = 2 := by
    norm_num [Fintype.card_fin]
  have hsqrt34 : Real.sqrt 3 * Real.sqrt (4 / 3 : ℝ) = 2 := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)]
    rw [show (3 : ℝ) * (4 / 3) = 4 by norm_num]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)
  have hne : Real.sqrt ((4 / 3 : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < 4 / 3 by norm_num))
  unfold coefficientTStatistic
  rw [hRSS, hβ, hdiag, hcast]
  rw [show (((![4] : Fin 1 → ℝ) 0 - (![0] : Fin 1 → ℝ) 0)) = 4 by norm_num]
  rw [show ((8 : ℝ) / 2) * (1 / 3) = 4 / 3 by norm_num]
  rw [div_eq_iff hne, mul_assoc, hsqrt34]
  norm_num

example : coefficientTStatistic X₀ 0 ![0] ![2, 4, 6]
    = tStatistic X₀ (Pi.single (0 : Fin 1) (1 : ℝ)) ![0] ![2, 4, 6] :=
  coefficientTStatistic_eq_tStatistic X₀ 0 ![0] ![2, 4, 6]

example : (Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ) ≠ 0 := by
  intro h0
  have h1 := congrFun h0 0
  simp at h1

end MathlibExtTest.LinearModelCoefficientT
