/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.NesterovSmoothing
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.Basic

namespace MathlibExt.Analysis.Convex.NesterovSmoothing

/-! Non-vacuity test: `f₀(x) = max_{|u| ≤ 1} x u = |x|` smoothed with `d(u) = u² / 2` (the Huber
function); the hypotheses of the uniform approximation hold. -/

example (μ : ℝ) (hμ : 0 ≤ μ) (x : ℝ) :
    smoothedMax (ContinuousLinearMap.id ℝ ℝ) (fun _ => 0) (fun u => u ^ 2 / 2) (Set.Icc (-1) 1)
        μ x ≤
      smoothedMax (ContinuousLinearMap.id ℝ ℝ) (fun _ => 0) (fun u => u ^ 2 / 2)
        (Set.Icc (-1) 1) 0 x :=
  (smoothedMax_le_and_le (ContinuousLinearMap.id ℝ ℝ) isCompact_Icc
    ⟨0, by norm_num⟩ continuousOn_const (by fun_prop) (fun u _ => by positivity) hμ x).1

end MathlibExt.Analysis.Convex.NesterovSmoothing
