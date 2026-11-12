/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.Negligible

/-- Boundary check: the zero function is negligible (directly from
the definition), and the closure lemmas instantiate on it. -/
example : Negligible (fun _ : ℕ => (0 : ℝ)) ∧
    Negligible (fun n : ℕ => (3 : ℝ) * 0) := by
  have hz : Negligible (fun _ : ℕ => (0 : ℝ)) := by
    intro c
    exact ⟨0, fun n _ => by simp⟩
  exact ⟨hz, negligible_const_mul hz 3⟩
