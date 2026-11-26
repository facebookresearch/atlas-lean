/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.StronglyConvexLowerBound

open WantedExt.Analysis.Convex.FirstOrderLowerBoundWanted

local notation "H" => lp (fun _ : ℕ => ℝ) 2

-- For μ = 2 and Q = 9, every first gradient step retains at least a quarter of the
-- initial squared distance, both in squared distance and in objective error.
example (x₀ : H) : ∃ (f : H → ℝ) (c : H), c ≠ x₀ ∧ ∀ t : ℝ,
    ‖x₀ - c‖ ^ 2 / 4 ≤ ‖x₀ + t • gradient f x₀ - c‖ ^ 2 ∧
    ‖x₀ - c‖ ^ 2 / 4 ≤ f (x₀ + t • gradient f x₀) - f c := by
  obtain ⟨f, -, -, -, c, hne, -, hbound⟩ :=
    exists_lower_bound_strongly_convex (μ := 2) (Q := 9) (by norm_num) (by norm_num) x₀
  refine ⟨f, c, hne, fun t => ?_⟩
  let x : ℕ → H
    | 0 => x₀
    | _ + 1 => x₀ + t • gradient f x₀
  have hspan (j : ℕ) : x j - x₀ ∈ Submodule.span ℝ ((fun i => gradient f (x i)) '' Set.Iio j) := by
    cases j with
    | zero => simp [x]
    | succ j =>
      rw [show x (j + 1) - x₀ = t • gradient f (x 0) by simp [x]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, Nat.zero_lt_succ _, rfl⟩)
  have h := hbound x rfl hspan 1
  have hs : √(9 : ℝ) = 3 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [x, hs, div_eq_inv_mul] at h ⊢
  exact h
