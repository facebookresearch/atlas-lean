/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.ScottishBook83

/-! # Distinct witnesses to the failure of the Hölder bound -/

open MathlibExt.Analysis.Calculus.ScottishBook83Wanted

-- The same function meets a common local bound and violates every global bound at distinct points.
example : ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ M > 0, ∃ f : ℝ → ℝ, Continuous f ∧
    (∀ x : ℝ, ∃ δ > 0, ∀ h : ℝ, 0 < |h| → |h| < δ →
      |f (x + h) - f x| ≤ M * |h| ^ a) ∧
    ∀ C : ℝ, ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1,
      x ≠ y ∧ C * |x - y| ^ a < |f x - f y| := by
  have h := auerbach83_refuted
  unfold ScottishBookProblem83Claim at h
  push Not at h
  obtain ⟨a, M, ha, ha', hM, f, hf, hlocal, hglobal⟩ := h
  refine ⟨a, ⟨ha, ha'⟩, M, hM, f, hf, ?_, ?_⟩
  · intro x
    obtain ⟨m, hm, δ, hδ, hb⟩ := hlocal x
    refine ⟨δ, hδ, fun h hh hs ↦ ?_⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hh a)).mp ((hb h hh hs).trans hm.le)
  · intro C
    obtain ⟨x, hx, y, hy, hxy⟩ := hglobal C
    refine ⟨x, hx, y, hy, ?_, hxy⟩
    rintro rfl
    simp [Real.zero_rpow ha.ne'] at hxy
