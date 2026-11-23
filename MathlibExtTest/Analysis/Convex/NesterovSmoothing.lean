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

-- On the same interval, the Huber smoothing has a global gradient Lipschitz bound of `1 / μ`.
example (μ : ℝ) (hμ : 0 < μ) :
    let f := smoothedMax (ContinuousLinearMap.id ℝ ℝ) (fun _ => 0)
      (fun u => u ^ 2 / 2) (Set.Icc (-1) 1) μ
    ConvexOn ℝ Set.univ f ∧ Differentiable ℝ f ∧
      LipschitzWith ⟨1 / μ, div_nonneg zero_le_one hμ.le⟩ (gradient f) := by
  intro f
  have hQc : Convex ℝ (Set.Icc (-1 : ℝ) 1) := convex_Icc _ _
  have hd : StrongConvexOn (Set.Icc (-1 : ℝ) 1) 1 (fun u => u ^ 2 / 2) := by
    rw [strongConvexOn_iff_convex]
    convert convexOn_const (0 : ℝ) hQc using 1
    ext u
    rw [Real.norm_eq_abs, sq_abs]
    ring
  have h := smoothedMax_convex_differentiable_lipschitz (ContinuousLinearMap.id ℝ ℝ)
    (φ := fun _ => 0) isCompact_Icc ⟨0, by norm_num⟩ hQc continuousOn_const
    (convexOn_const _ hQc) (by fun_prop) zero_lt_one hd hμ
  simpa only [ContinuousLinearMap.norm_id, one_pow, mul_one] using h

end MathlibExt.Analysis.Convex.NesterovSmoothing
