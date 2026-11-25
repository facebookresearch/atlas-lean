/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ScottishBook144

/-! # The interval constraint in Scottish Book Problem 144 -/

open MathlibExt.Analysis.ScottishBook144Wanted

example : ¬ ScottishBookProblem144Claim.{1} := mazurUlam144_refuted

-- The real unit sphere does admit an injection into the interval. The entire image is null.
example : ∃ f : Metric.sphere (0 : ℝ) 1 → ℝ, Function.Injective f ∧
    (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧ MeasureTheory.volume (Set.range f) = 0 := by
  let f (x : Metric.sphere (0 : ℝ) 1) := (x.val + 1) / 2
  refine ⟨f, fun x y h ↦ Subtype.ext (by simpa [f] using h), ?_, ?_⟩
  · intro x
    have hx : |x.val| = 1 := by
      simpa only [Metric.mem_sphere, Real.dist_eq, sub_zero] using x.property
    obtain ⟨hl, hu⟩ := abs_le.mp hx.le
    constructor <;> dsimp [f] <;> linarith
  · have : Finite (Metric.sphere (0 : ℝ) 1) := by
      rw [Real.sphere_eq_pair _ zero_le_one]
      infer_instance
    exact (Set.finite_range f).measure_zero _
