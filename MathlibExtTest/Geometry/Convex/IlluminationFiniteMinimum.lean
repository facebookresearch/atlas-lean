/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Convex.IlluminationFiniteMinimum
import MathlibExtTest.Geometry.Convex.HadwigerCovering
import Mathlib.Analysis.Normed.Module.Convex

open ConvexCovering ConvexCoveringTest

-- The closed unit interval has a finite illumination number, and its endpoint rules out zero.
example : 0 < directionalIlluminationNumber K ∧ directionalIlluminationNumber K < ⊤ := by
  have hK : IsConvexBody K :=
    ⟨isCompact_closedBall _ _, convex_closedBall _ _,
      0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self zero_lt_one)⟩
  obtain ⟨q, hq⟩ := illuminationFiniteMinimum 1 Nat.zero_lt_one K hK
  have hvalue : directionalIlluminationNumber K = (q : WithTop ℕ) :=
    (WithTop.coe_mono.map_isLeast hq).csInf_eq
  obtain ⟨_, _, hcover⟩ := hq.1
  obtain ⟨i, _⟩ := hcover tip tip_frontier
  rw [hvalue]
  exact ⟨WithTop.coe_lt_coe.mpr (Nat.zero_lt_of_lt i.isLt), WithTop.coe_lt_top _⟩
