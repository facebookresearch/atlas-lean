/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Streaming.AMSFrequencyMoment

@[expose] public section

open MathlibExt.Probability.Streaming.AMS

namespace MathlibExtTest.Probability.Streaming.AMSFrequencyMoment

-- The stream `0, 1, 1`: suffix counts `1, 2, 1`.
example : suffixCount ([0, 1, 1] : List (Fin 3)) ⟨0, by simp⟩ = 1 := by decide
example : suffixCount ([0, 1, 1] : List (Fin 3)) ⟨1, by simp⟩ = 2 := by decide
example : suffixCount ([0, 1, 1] : List (Fin 3)) ⟨2, by simp⟩ = 1 := by decide

-- With `k = 2` the estimator at position `1` is `3 (2² - 1²) = 9`.
example : basicEstimator 2 ([0, 1, 1] : List (Fin 3)) ⟨1, by simp⟩ = 9 := by
  have : suffixCount ([0, 1, 1] : List (Fin 3)) ⟨1, by simp⟩ = 2 := by decide
  rw [basicEstimator, this]
  norm_num

-- The estimator values `3, 9, 3` average to `F₂ = 1 + 4 = 5`.
example : (1 / 3 : ℝ) * ∑ p, basicEstimator 2 ([0, 1, 1] : List (Fin 3)) p = 5 := by
  have h := average_basicEstimator 2 (by norm_num) ([0, 1, 1] : List (Fin 3))
  have h5 : ∑ i : Fin 3, (([0, 1, 1] : List (Fin 3)).count i : ℝ) ^ 2 = 5 := by
    simp [Fin.sum_univ_three, List.count_cons]
    norm_num
  rw [h5] at h
  simpa using h

-- The second-moment bound `E[X²] ≤ k F₁ F_{2k-1}`: `(9 + 81 + 9) / 3 = 33 ≤ 2 · 3 · (1 + 8)`.
example : (1 / 3 : ℝ) * ∑ p, basicEstimator 2 ([0, 1, 1] : List (Fin 3)) p ^ 2 ≤ 54 := by
  have h := average_basicEstimator_sq_le 2 (by norm_num) ([0, 1, 1] : List (Fin 3))
  have h9 : ∑ i : Fin 3, (([0, 1, 1] : List (Fin 3)).count i : ℝ) ^ (2 * 2 - 1) = 9 := by
    simp [Fin.sum_univ_three, List.count_cons]
    norm_num
  rw [h9] at h
  norm_num at h
  simpa using h

-- The moment inequality is an equality for `n = 1`: `x · x³ = 1^{1/2} · (x²)²`.
example (x : ℝ) (hx : 0 ≤ x) :
    (∑ _i : Fin 1, x) * ∑ _i : Fin 1, x ^ (2 * 2 - 1) ≤
      (Fintype.card (Fin 1) : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) * (∑ _i : Fin 1, x ^ 2) ^ 2 :=
  sum_mul_sum_le_rpow (fun _ => x) (fun _ => hx) 2 (by norm_num)

end MathlibExtTest.Probability.Streaming.AMSFrequencyMoment
