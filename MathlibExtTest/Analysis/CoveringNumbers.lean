/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.CoveringNumbers

/-- Boundary check: in dimension `0` the bound instantiates (the
ball is a single point). -/
example : ∃ C : Finset (EuclideanSpace ℝ (Fin 0)),
    (∀ x ∈ C, ‖x‖ ≤ 1 + 1) ∧
    (∀ x, ‖x‖ ≤ 1 → ∃ c ∈ C, dist x c ≤ 1) ∧
    (C.card : ℝ) ≤ (1 + 2 * 1 / 1) ^ 0 :=
  euclidean_ball_net (by norm_num) (by norm_num)

/-- The bound instantiates for the unit ball in one dimension at
scale `1 / 2`. -/
example : ∃ C : Finset (EuclideanSpace ℝ (Fin 1)),
    (∀ x ∈ C, ‖x‖ ≤ 1 + 1 / 2) ∧
    (∀ x, ‖x‖ ≤ 1 → ∃ c ∈ C, dist x c ≤ 1 / 2) ∧
    (C.card : ℝ) ≤ (1 + 2 * 1 / (1 / 2)) ^ 1 :=
  euclidean_ball_net (by norm_num) (by norm_num)
