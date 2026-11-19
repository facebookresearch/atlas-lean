/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Optimization.TrustRegion

open MathlibExt.Analysis.Optimization.TrustRegion

-- A nonconvex model: `g = 1`, `B = -I` on `ℝ`, `Δ = 1`, so `q(s) = s - s² / 2`. The boundary
-- point `s = -1` with multiplier `μ = 2` satisfies the optimality conditions, hence is a global
-- minimiser on `[-1, 1]` although `B` is indefinite.
example : ∀ p : ℝ, ‖p‖ ≤ 1 →
    trustRegionModel (1 : ℝ) (-ContinuousLinearMap.id ℝ ℝ) (-1) ≤
      trustRegionModel (1 : ℝ) (-ContinuousLinearMap.id ℝ ℝ) p := by
  refine trustRegionModel_le_of_optimality (Δ := 1) (μ := 2) ?_ (by norm_num) ?_ ?_ ?_
  · intro u v; simp
  · simp; norm_num
  · intro v
    simp only [neg_apply, ContinuousLinearMap.id_apply, RCLike.inner_apply,
      conj_trivial, smul_eq_mul]
    nlinarith [sq_nonneg v]
  · simp

-- The Cauchy decrease with `B = I`, `g = 1`, `Δ = 1`, `M = 1`: predicted reduction at least `1/2`.
example : ∃ t : ℝ, 0 ≤ t ∧ ‖t • (1 : ℝ)‖ ≤ 1 ∧
    1 / 2 * ‖(1 : ℝ)‖ * min 1 (‖(1 : ℝ)‖ / 1) ≤
      -trustRegionModel (1 : ℝ) (ContinuousLinearMap.id ℝ ℝ) (-(t • (1 : ℝ))) :=
  exists_cauchy_step (by norm_num) (by norm_num) fun v => by simp
