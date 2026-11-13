/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.Sequence.KalmanHistory

/-!
# Tests for sequential Kalman conditioning

Closed checks on the existing filter at `n = p = Fin 1`: the roadmap witness
`F = H0 = H1 = 1`, `P0 = R0 = R1 = 1`, `Q = 0`, `m0 = 0`, `y0 = 1`, `y1 = 2`
gives recursive belief mean `1` and variance `1/3` and equals the batch
conditioning; a known state (`P0 = 0`) is never revised; and the recursive
belief is valid by the existing `update_valid` and `step_valid`.
-/

open Matrix Cslib.MachineLearning.Sequence.KalmanFilter

namespace Cslib.MachineLearning.Sequence.KalmanHistory

/-- Witness: `F = H0 = H1 = 1`, `P0 = R0 = R1 = 1`, `Q = 0`, `m0 = 0`,
`y0 = 1`, `y1 = 2`: recursive belief mean `1`, variance `1/3`. -/
example :
    (step !![1] !![0] !![1] !![1] (!₂[2]) (update !![1] !![1] (!₂[1]) ⟨!₂[0], !![1]⟩)).mean 0 = 1 ∧
      (step !![1] !![0] !![1] !![1] (!₂[2])
        (update !![1] !![1] (!₂[1]) ⟨!₂[0], !![1]⟩)).cov 0 0 = 1 / 3 := by
  simp only [step, update_mean_fin_one, update_cov_fin_one, predict_mean_fin_one,
    predict_cov_fin_one]
  norm_num

/-- Witness: recursive equals batch on the witness parameters. -/
example :
    (step !![1] !![0] !![1] !![1] (!₂[2]) (update !![1] !![1] (!₂[1]) ⟨!₂[0], !![1]⟩)).mean 0 =
        BatchMean 1 1 1 1 1 0 1 0 ![1, 2] ∧
      (step !![1] !![0] !![1] !![1] (!₂[2])
        (update !![1] !![1] (!₂[1]) ⟨!₂[0], !![1]⟩)).cov 0 0 = BatchVar 1 1 1 1 1 0 1 := by
  have h := recursive_eq_batch 1 0 1 1 1 1 ⟨!₂[0], !![1]⟩ (!₂[1]) (!₂[2]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- Known state: with `P0 = 0`, `F = H0 = H1 = 1`, `Q = 0`, and `R0 = R1 = 1`,
the belief stays `(m0, 0)` regardless of the observations. -/
example (m0 : ℝ) (y0 y1 : EuclideanSpace ℝ (Fin 1)) :
    (step !![1] !![0] !![1] !![1] y1 (update !![1] !![1] y0 ⟨!₂[m0], !![0]⟩)).mean 0 = m0 ∧
      (step !![1] !![0] !![1] !![1] y1 (update !![1] !![1] y0 ⟨!₂[m0], !![0]⟩)).cov 0 0 =
        0 := by
  simp [step, update_mean_fin_one, update_cov_fin_one, predict_mean_fin_one,
    predict_cov_fin_one]

/-- The recursive belief is a valid Gaussian belief, by the existing filter lemmas. -/
example (F Q H0 H1 R0 R1 : ℝ) (b0 : Belief (Fin 1)) (y0 y1 : EuclideanSpace ℝ (Fin 1))
    (hb : b0.Valid) (hQ : (!![Q] : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef)
    (hR0 : (!![R0] : Matrix (Fin 1) (Fin 1) ℝ).PosDef)
    (hR1 : (!![R1] : Matrix (Fin 1) (Fin 1) ℝ).PosDef) :
    (step !![F] !![Q] !![H1] !![R1] y1 (update !![H0] !![R0] y0 b0)).Valid :=
  step_valid !![F] !![Q] !![H1] y1 (update_valid !![H0] y0 hb hR0) hQ hR1

#print axioms recursive_eq_batch

end Cslib.MachineLearning.Sequence.KalmanHistory
