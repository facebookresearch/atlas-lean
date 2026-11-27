/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/
module

import MathlibExt.Analysis.Convex.PolarCone

open scoped InnerProductSpace

-- A negative vector is polar to the nonnegative ray; its negation is in the dual cone.
example : -(-2 : ℝ) ∈ PointedCone.dual (innerₗ ℝ) (Set.Ici (0 : ℝ)) := by
  apply PointedCone.neg_mem_dual_inner_iff.mpr
  intro x hx
  rw [Real.inner_apply]
  exact mul_nonpos_of_nonneg_of_nonpos hx (by norm_num)

-- The positive test vector 1 detects the opposite sign's failure.
example : -(2 : ℝ) ∉ PointedCone.dual (innerₗ ℝ) (Set.Ici (0 : ℝ)) := by
  intro h
  have hbad : inner ℝ (1 : ℝ) (2 : ℝ) ≤ 0 :=
    (PointedCone.neg_mem_dual_inner_iff.mp h) 1 (by norm_num)
  norm_num [Real.inner_apply] at hbad
