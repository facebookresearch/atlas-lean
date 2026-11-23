/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.LinearStabilization

@[expose] public section

open Matrix MathlibExt.Analysis.Control

namespace MathlibExtTest.Analysis.Control.LinearStabilization

/-- Non-vacuity: the unstable scalar system `ẋ = x + u` (`A = [1]`, `B = [1]`) satisfies the
Kalman rank condition, so some feedback makes it exponentially stable. -/
example : ∃ K : Matrix (Fin 1) (Fin 1) ℝ, ((1 : Matrix (Fin 1) (Fin 1) ℝ) + 1 * K).IsHurwitz := by
  obtain ⟨K, -, hK⟩ := exists_isHurwitz_add_mul (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (by
    rw [eq_top_iff]
    intro x _
    exact Submodule.subset_span ⟨0, by norm_num, x, by simp⟩)
  exact ⟨K, hK⟩

end MathlibExtTest.Analysis.Control.LinearStabilization
