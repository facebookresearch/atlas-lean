/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Optimization.TrustRegion

open scoped RealInnerProductSpace
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

-- The boundary minimizer of the concave quadratic has a nonzero multiplier.
example : ∃ μ : ℝ, 0 ≤ μ ∧ μ = 2 := by
  let B : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  have hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫ := by
    intro u v
    simp [B]
  have hmin : ∀ p : ℝ, ‖p‖ ≤ 1 → trustRegionModel (1 : ℝ) B (-1) ≤ trustRegionModel 1 B p := by
    intro p hp
    simp only [trustRegionModel, B, neg_apply, ContinuousLinearMap.id_apply, RCLike.inner_apply,
      conj_trivial]
    have habs : |p| ≤ 1 := by simpa only [Real.norm_eq_abs] using hp
    have hl := (abs_le.mp habs).1
    have hu := (abs_le.mp habs).2
    nlinarith [mul_nonneg (show 0 ≤ 1 + p by linarith) (show 0 ≤ 3 - p by linarith)]
  obtain ⟨μ, hμ, heq, -, -⟩ := exists_optimality_of_isMinOn (Δ := 1)
    (by norm_num) hsymm (by norm_num) hmin
  change B (-1) + μ • (-1 : ℝ) = -1 at heq
  simp only [B, neg_apply, ContinuousLinearMap.id_apply, neg_neg, smul_eq_mul] at heq
  exact ⟨μ, hμ, by linarith⟩
