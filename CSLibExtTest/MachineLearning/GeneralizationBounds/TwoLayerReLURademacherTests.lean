/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.TwoLayerReLURademacher

open Real
open Cslib.MachineLearning.Rademacher

namespace CSLibExt.MachineLearning.GeneralizationBounds

-- The ball is not trivial: a single ReLU unit `x ↦ max x₀ 0` has path norm `1`.
example {n : ℕ} (x : Fin n → Fin 1 → ℝ) :
    (fun i => max (x i 0) 0) ∈ pathNormBallValues x 1 :=
  ⟨1, fun _ => 1, fun _ _ => 1, by simp [pathNorm], by funext i; simp [twoLayerReLU]⟩

-- Rescaling the outer weight scales the path norm: `3 max(x₀, 0)` lies in the ball of radius 3.
example {n : ℕ} (x : Fin n → Fin 1 → ℝ) :
    (fun i => 3 * max (x i 0) 0) ∈ pathNormBallValues x 3 :=
  ⟨1, fun _ => 3, fun _ _ => 1, by simp [pathNorm], by funext i; simp [twoLayerReLU]⟩

-- A width-two network with a negative outer weight: `max(x₀, 0) - max(-x₀, 0) = x₀`, path
-- norm `2`; so the identity of the line is in the ball of radius `2`.
example {n : ℕ} (x : Fin n → Fin 1 → ℝ) :
    (fun i => x i 0) ∈ pathNormBallValues x 2 := by
  refine ⟨2, ![1, -1], ![fun _ => 1, fun _ => -1], ?_, ?_⟩
  · simp [pathNorm, Fin.sum_univ_two]; norm_num
  · funext i
    simp only [twoLayerReLU, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, neg_mul]
    rcases le_total 0 (x i 0) with h | h
    · simp [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
    · simp [max_eq_right h, max_eq_left (neg_nonneg.2 h)]

-- The bound for three points in `[-1, 1]²` and path norm `5`.
example (x : Fin 3 → Fin 2 → ℝ) (hx : ∀ i j, |x i j| ≤ 1) :
    rademacherComplexity (pathNormBallValues x 5) ≤ 2 * 5 * √(2 * log (2 * 2) / 3) := by
  simpa using rademacherComplexity_pathNormBallValues_le (by norm_num) hx (by norm_num)

-- Path norm `0` forces complexity at most `0`.
example {n d : ℕ} (hd : 0 < d) (x : Fin n → Fin d → ℝ) (hx : ∀ i j, |x i j| ≤ 1) :
    rademacherComplexity (pathNormBallValues x 0) ≤ 0 := by
  simpa using rademacherComplexity_pathNormBallValues_le hd hx le_rfl

-- With a bias: a ReLU unit `x ↦ max(x₀ + 1, 0)` has path norm `|1| (|1| + |1|) = 2`.
example {n : ℕ} (x : Fin n → Fin 1 → ℝ) :
    (fun i => max (x i 0 + 1) 0) ∈ pathNormBallBiasValues x 2 :=
  ⟨1, fun _ => 1, fun _ _ => 1, fun _ => 1, by simp [pathNormBias]; norm_num,
    by funext i; simp [twoLayerReLUBias]⟩

-- The bias bound on the real line (`d = 1`): `log (2 (1 + 1)) = log 4`.
example {n : ℕ} (x : Fin n → Fin 1 → ℝ) (hx : ∀ i j, |x i j| ≤ 1) :
    rademacherComplexity (pathNormBallBiasValues x 1) ≤ 2 * 1 * √(2 * log (2 * (1 + 1)) / n) := by
  simpa using rademacherComplexity_pathNormBallBiasValues_le hx zero_le_one

end CSLibExt.MachineLearning.GeneralizationBounds
