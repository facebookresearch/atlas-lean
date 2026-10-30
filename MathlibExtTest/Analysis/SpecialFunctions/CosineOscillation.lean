/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.CosineOscillation
import Mathlib.Tactic

namespace MetaMathlibExt

/-- At `θ = 0`, the oscillation lemma supplies a phase shift in `(π, 3 * π)`
with `|cos 0 - cos φ| ≥ 1`. -/
example : ∃ φ : ℝ, Real.pi < φ ∧ φ < 3 * Real.pi ∧
    1 ≤ |Real.cos 0 - Real.cos φ| := by
  simpa using Real.exists_cos_sub_cos_ge_one 0

/-- At `c = 0, K = 1`, the scaled oscillation lemma supplies
`y ∈ (π, 3 * π)` with `|cos 0 - cos y| ≥ 1`. -/
example : ∃ y : ℝ, Real.pi < y ∧ y < 3 * Real.pi ∧
    1 ≤ |Real.cos 0 - Real.cos y| := by
  simpa using Real.exists_cos_oscillation 0 1 one_pos

/-- The concrete witness `φ = 3 * π / 2` at `θ = 0`: `cos (3 * π / 2) = 0`
while `cos 0 = 1`, so the oscillation is exactly `1`. -/
example : 1 ≤ |Real.cos 0 - Real.cos (3 * Real.pi / 2)| := by
  have h : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
      Real.cos_add_pi_div_two, Real.sin_pi, neg_zero]
  rw [h, Real.cos_zero]
  norm_num

end MetaMathlibExt
