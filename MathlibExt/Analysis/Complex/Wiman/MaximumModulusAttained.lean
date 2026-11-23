/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact

@[expose] public section

namespace Complex

noncomputable section

open Set

/-- **The maximum modulus is attained.** Let $f$ be an entire function and let $r \ge 0$. Then
there is a point $z$ with $|z| = r$ such that $|f(w)| \le |f(z)|$ for every $w$ with $|w| = r$,
and the maximum modulus $M(r) = \sup_{|w| = r} |f(w)|$ equals $|f(z)|$. -/
theorem exists_mem_sphere_eq_wimanMaximumModulus
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ z ∈ Metric.sphere (0 : ℂ) r,
      wimanMaximumModulus f r = ‖f z‖ ∧
      ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖f w‖ ≤ ‖f z‖ := by
  obtain ⟨z, hz, hsup, hmax⟩ :=
    (isCompact_sphere (0 : ℂ) r).exists_sSup_image_eq_and_ge
      (NormedSpace.sphere_nonempty.mpr hr) hf.continuous.norm.continuousOn
  exact ⟨z, hz, by simpa [wimanMaximumModulus, abs_of_nonneg hr] using hsup, hmax⟩

end

end Complex
