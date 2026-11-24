/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatMaximumPrinciple

/-!
# Tests for the weak maximum principle for the heat equation

The function `u(t, x) = -t` on `[0, 1] × [-1, 1] ⊆ ℝ × ℝ` is a strict subsolution
(`uₜ - Δ u = -1`) that is not constant in time; every hypothesis of the weak maximum principle
holds, and the principle gives a maximum on the parabolic boundary.
-/

open InnerProductSpace Laplacian Set Metric
open MathlibExt.Analysis.PDE.HeatMaximumPrinciple

example : ∃ p ∈ parabolicBoundary (ball (0 : ℝ) 1) 1,
    IsMaxOn (fun p : ℝ × ℝ => -p.1) (Icc 0 1 ×ˢ closure (ball (0 : ℝ) 1)) p :=
  exists_mem_parabolicBoundary_isMaxOn (u := fun t _ => -t) (ut := fun _ _ => -1)
    zero_le_one isBounded_ball isOpen_ball ⟨0, mem_ball_self one_pos⟩
    (by fun_prop) (fun _ _ _ _ => contDiffAt_const)
    (fun t _ _ _ => (hasDerivAt_neg t).hasDerivWithinAt)
    (fun t _ x _ => by
      show (-1 : ℝ) - Δ (fun _ : ℝ => -t) x ≤ 0
      rw [laplacian_const]
      norm_num)
