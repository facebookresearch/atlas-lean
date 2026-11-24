/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.FirstOrderLowerBound

namespace MathlibExt.Analysis.Convex.FirstOrderLowerBound

open scoped ContDiff

/-! Non-vacuity tests for the lower complexity bound and the worst function. -/

-- The worst function `f_3` on `ℝ³` with `L = 1` attains `-(1 / 8) (3 / 4) = -3 / 32` at `x̄`.
example : worstFunction 3 3 1 (worstMinimizer 3 3) = -3 / 32 := by
  rw [worstFunction_worstMinimizer (by norm_num) le_rfl]
  norm_num

-- It is smooth, convex and `1`-smooth, and `x̄` minimises it.
example : ContDiff ℝ ∞ (worstFunction 3 3 1) ∧ ∀ z, worstFunction 3 3 1 (worstMinimizer 3 3) ≤
    worstFunction 3 3 1 z := by
  refine ⟨(worstFunction_mem_class 3 zero_le_one).1, fun z => ?_⟩
  rw [worstFunction_worstMinimizer (by norm_num) le_rfl]
  exact worstFunction_ge_of_support (by norm_num) le_rfl zero_le_one fun j hj => by
    simp [coordVec, show ¬ (j ≤ 3) by omega]

-- The span hypothesis is satisfiable: the method that never moves has its iterates in every
-- span, and the bound applies to it on `ℝ³` with `k = 1`. The minimiser is not the starting
-- point, so the bound is positive and the starting point is strictly suboptimal: the trivial
-- witness `x⋆ = x₀` (for instance with `f ≡ 0`) is excluded.
example (x₀ : EuclideanSpace ℝ (Fin 3)) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, ∃ xstar, xstar ≠ x₀ ∧ (∀ z, f xstar ≤ f z) ∧
      0 < 3 * 1 * ‖x₀ - xstar‖ ^ 2 / (32 * ((1 : ℕ) + 1 : ℝ) ^ 2) ∧
      3 * 1 * ‖x₀ - xstar‖ ^ 2 / (32 * ((1 : ℕ) + 1 : ℝ) ^ 2) ≤ f x₀ - f xstar := by
  obtain ⟨f, -, -, -, xstar, hne, hmin, hlow⟩ :=
    exists_lower_bound_smooth_convex (n := 3) (k := 1) le_rfl le_rfl one_pos x₀
  have hpos : 0 < ‖x₀ - xstar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  exact ⟨f, xstar, hne, hmin, by positivity, (hlow (fun _ => x₀) rfl (fun j => by simp)).1⟩

-- The same holds in every admissible dimension and for every `k`: no first-order method that
-- starts at `x₀` has reached the minimum after `k` steps.
example {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k + 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ∃ xstar, (∀ z, f xstar ≤ f z) ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x₀ →
        (∀ j, x j - x₀ ∈ Submodule.span ℝ ((fun i => gradient f (x i)) '' Set.Iio j)) →
        f xstar < f (x k) := by
  obtain ⟨f, -, -, -, xstar, hne, hmin, hlow⟩ := exists_lower_bound_smooth_convex hk hkn hL x₀
  refine ⟨f, xstar, hmin, fun x hx0 hspan => ?_⟩
  have hpos : 0 < ‖x₀ - xstar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have := (hlow x hx0 hspan).1
  have : 0 < 3 * L * ‖x₀ - xstar‖ ^ 2 / (32 * ((k : ℝ) + 1) ^ 2) := by positivity
  linarith

-- The coordinates beyond `m` of the minimiser vanish and the first one is `m / (m + 1)`.
example :
    worstMinimizer 5 3 ⟨0, by norm_num⟩ = 3 / 4 ∧ worstMinimizer 5 3 ⟨4, by norm_num⟩ = 0 := by
  simp [worstMinimizer]
  norm_num

end MathlibExt.Analysis.Convex.FirstOrderLowerBound
