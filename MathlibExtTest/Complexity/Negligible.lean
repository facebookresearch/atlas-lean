/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.Negligible

/-- Boundary check: the zero function and its constant multiple
are negligible. -/
example : Negligible (fun _ : ℕ => (0 : ℝ)) ∧
    Negligible (fun n : ℕ => (3 : ℝ) * 0) := by
  have hz : Negligible (fun _ : ℕ => (0 : ℝ)) := by
    intro c
    exact ⟨0, fun n _ => by simp⟩
  exact ⟨hz, negligible_const_mul hz 3⟩

private def spike (n : ℕ) : ℝ := if n = 0 then 7 else 0

private theorem negligible_spike : Negligible spike := by
  intro c
  refine ⟨1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  simp [spike, hn0]

/-- Addition applies to functions with nonzero initial values. -/
example : Negligible (fun n => spike n + 3 * spike n) :=
  negligible_add negligible_spike (negligible_const_mul negligible_spike 3)

/-- The polynomial bound is needed only eventually: it fails at zero. -/
example : Negligible
    (fun n => (if n = 0 then 37 else (n : ℝ) ^ 3) * spike n) := by
  apply negligible_mul_of_poly_bound negligible_spike (d := 3)
  refine ⟨1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  simp [hn0, abs_of_nonneg hp]
