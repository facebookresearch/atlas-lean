/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.FiniteSampleExpressivity

namespace CSLibExt.MachineLearning.FiniteSampleExpressivity

-- Lemma 1 on the interleaving `0 < 1 < 2 < 3`.
example : (Matrix.of fun i j => max (![1, 3] i - ![0, 2] j) 0 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 :=
  det_relu_matrix_ne_zero _ _ (fun i => by fin_cases i <;> norm_num)
    (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all)

-- Any labelling of three distinct points of `ℝ`, here the alternating one, is fitted exactly.
example : ∃ (a : ℝ) (b w : Fin 3 → ℝ), ∀ i,
    reluNet a b w (![0, 1, 2] i) = ![1, 0, 1] i :=
  exists_reluNet_eq (fun i j h => by fin_cases i <;> fin_cases j <;> simp_all) _

-- Distinctness is needed: two copies of one point with different labels cannot be fitted.
example : ¬ ∃ (a : ℝ) (b w : Fin 2 → ℝ), ∀ i,
    reluNet a b w (![(0 : ℝ), 0] i) = ![0, 1] i := by
  rintro ⟨a, b, w, h⟩
  have h0 := h 0
  have h1 := h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [h0] at h1
  exact zero_ne_one h1

end CSLibExt.MachineLearning.FiniteSampleExpressivity
