/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.MirrorDescent

open Finset

namespace MathlibExt.Analysis.Convex.MirrorDescent

/-- The Euclidean distance-generating function `ω x = x² / 2` on `ℝ`, with derivative
`ω' x = x • id`. -/
noncomputable def ωR : ℝ → ℝ := fun x => x ^ 2 / 2

/-- The derivative selection of `ωR`. -/
noncomputable def ωR' : ℝ → ℝ →L[ℝ] ℝ := fun x => x • ContinuousLinearMap.id ℝ ℝ

-- In the Euclidean setup the Bregman divergence is half the squared distance.
example (x u : ℝ) : bregman ωR ωR' x u = (u - x) ^ 2 / 2 := by
  simp [bregman, ωR, ωR']; ring

-- The Euclidean setup is `1`-strongly convex in the Bregman form (with equality).
example (x u : ℝ) : 1 / 2 * ‖u - x‖ ^ 2 ≤ bregman ωR ωR' x u := by
  simp [bregman, ωR, ωR', Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (u - x)]

-- The three-point identity on a concrete instance.
example : bregman ωR ωR' 0 3 - bregman ωR ωR' 1 3 - bregman ωR ωR' 0 1 = (ωR' 1 - ωR' 0) (3 - 1) :=
  bregman_three_point _ _ _ _ _

-- Mirror descent in the Euclidean setup on `ℝ` is the gradient step `x_{t+1} = x_t - γ_t g_t`,
-- whose prox optimality condition holds with equality; `mirror_descent_sum_le` then gives the
-- classical regret bound `∑ γ_t g_t (x_t - u) ≤ (u - x_0)² / 2 + ∑ γ_t² g_t² / 2`.
example (x : ℕ → ℝ) (c : ℕ → ℝ) (γ : ℕ → ℝ) (hx : ∀ t, x (t + 1) = x t - γ t * c t) (u : ℝ)
    (N : ℕ) :
    ∑ t ∈ range N, γ t * (c t • ContinuousLinearMap.id ℝ ℝ) (x t - u) ≤
      bregman ωR ωR' (x 0) u +
        (∑ t ∈ range N, γ t ^ 2 * ‖c t • ContinuousLinearMap.id ℝ ℝ‖ ^ 2) / (2 * 1) := by
  refine mirror_descent_sum_le ωR ωR' one_pos (X := Set.univ) (Xo := Set.univ) subset_rfl
    (fun x _ u _ => ?_) (fun _ => Set.mem_univ _) (fun t u _ => ?_) (Set.mem_univ u) N
  · simp [bregman, ωR, ωR', Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (u - x)]
  · simp [ωR', hx t]; ring_nf; rfl

-- The pathwise stochastic bound applies with zero noise and reduces to the deterministic bound.
example (x : ℕ → ℝ) (c : ℕ → ℝ) (γ : ℕ → ℝ) (hγ : ∀ t, 0 < γ t)
    (hx : ∀ t, x (t + 1) = x t - γ t * c t) (hsub : ∀ t y, |x t| + c t * (y - x t) ≤ |y|) :
    |(∑ t ∈ range 3, γ t)⁻¹ • ∑ t ∈ range 3, γ t • x t| - |0| ≤
      (bregman ωR ωR' (x 0) 0 +
        (∑ t ∈ range 3, γ t ^ 2 * ‖c t • ContinuousLinearMap.id ℝ ℝ + 0‖ ^ 2) / (2 * 1) -
          ∑ t ∈ range 3, γ t * (0 : ℝ →L[ℝ] ℝ) (x t - 0)) / ∑ t ∈ range 3, γ t := by
  refine stochastic_mirror_descent_average_le ωR ωR' one_pos (X := Set.univ) (Xo := Set.univ)
    subset_rfl (fun x _ u _ => ?_) convexOn_univ_norm
    (g := fun t => c t • ContinuousLinearMap.id ℝ ℝ)
    (Δ := fun _ => 0) (fun _ => Set.mem_univ _) (fun t u _ => ?_) (fun t y _ => ?_) hγ
    (Set.mem_univ _) (by norm_num)
  · simp [bregman, ωR, ωR', Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (u - x)]
  · simp [ωR', hx t]; ring_nf; rfl
  · simpa [Real.norm_eq_abs] using hsub t y

end MathlibExt.Analysis.Convex.MirrorDescent
