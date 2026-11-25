/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.MidpointConvexContinuousConvex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MathlibExt.Analysis.Calculus.MidpointConvexContinuousConvexWanted

-- A non-affine example on an interval containing points of both signs.
example : ConvexOn ℝ (Set.Ioo (-2 : ℝ) 2) (fun x : ℝ ↦ x ^ 2) := by
  refine convexOn_Ioo_of_continuousOn_of_midpoint_le (by norm_num) _ (by fun_prop) ?_
  intro x _ y _
  nlinarith [sq_nonneg (x - y)]
