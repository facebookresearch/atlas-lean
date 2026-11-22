/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.AffineRecurrenceConvergence
import Mathlib.Tactic

/-!
# Tests for the single-cue error-correction update

Concrete boundary values for gains `0`, `1`, `1/2`, `3/2` and `2`,
proved directly from the update equation.
-/

@[expose] public section

namespace MathlibExtTest.Algebra.AffineRecurrenceConvergence

open Filter Topology
open MathlibExt.AffineRecurrence

/-- At unit gain the target is reached in one step. -/
theorem test_alpha_one {lambda : ℝ} {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + 1 * (lambda - v n)) :
    v 1 = lambda := by
  have e : v 1 = v 0 + 1 * (lambda - v 0) := hv 0
  rw [e]
  ring

/-- At gain `2` the iterates alternate around the target:
with target `5` and initial value `1`, the first values are `9, 1, 9`. -/
theorem test_alpha_two_alternates {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + 2 * (5 - v n)) (h0 : v 0 = 1) :
    v 1 = 9 ∧ v 2 = 1 ∧ v 3 = 9 := by
  have e1 : v 1 = v 0 + 2 * (5 - v 0) := hv 0
  have e2 : v 2 = v 1 + 2 * (5 - v 1) := hv 1
  have e3 : v 3 = v 2 + 2 * (5 - v 2) := hv 2
  rw [h0] at e1
  norm_num at e1
  rw [e1] at e2
  norm_num at e2
  rw [e2] at e3
  norm_num at e3
  exact ⟨e1, e2, e3⟩

/-- At gain `1/2`, with target `5` and initial value `1`, the first values
are `3, 4, 9/2`. -/
theorem test_alpha_half_values {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + (1 / 2 : ℝ) * (5 - v n)) (h0 : v 0 = 1) :
    v 1 = 3 ∧ v 2 = 4 ∧ v 3 = 9 / 2 := by
  have e1 : v 1 = v 0 + (1 / 2 : ℝ) * (5 - v 0) := hv 0
  have e2 : v 2 = v 1 + (1 / 2 : ℝ) * (5 - v 1) := hv 1
  have e3 : v 3 = v 2 + (1 / 2 : ℝ) * (5 - v 2) := hv 2
  rw [h0] at e1
  norm_num at e1
  rw [e1] at e2
  norm_num at e2
  rw [e2] at e3
  norm_num at e3
  exact ⟨e1, e2, e3⟩

/-- At gain `3/2` the iterates overshoot and then undershoot the target:
with target `5` and initial value `1`, the first values are `7, 4`. -/
theorem test_alpha_three_halves_oscillates {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + (3 / 2 : ℝ) * (5 - v n)) (h0 : v 0 = 1) :
    v 1 = 7 ∧ v 2 = 4 := by
  have e1 : v 1 = v 0 + (3 / 2 : ℝ) * (5 - v 0) := hv 0
  have e2 : v 2 = v 1 + (3 / 2 : ℝ) * (5 - v 1) := hv 1
  rw [h0] at e1
  norm_num at e1
  rw [e1] at e2
  norm_num at e2
  exact ⟨e1, e2⟩

/-- At zero gain nothing moves: every iterate equals the initial value. -/
theorem test_alpha_zero_fixed {lambda : ℝ} {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + 0 * (lambda - v n)) (n : ℕ) :
    v n = v 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [hv n, ih]; ring

/-- API client check: the closed form gives the third half-gain value. -/
theorem test_api_eq_half {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + (1 / 2 : ℝ) * (5 - v n)) (h0 : v 0 = 1) :
    v 3 = 9 / 2 := by
  have h := errorCorrection_eq (1 / 2 : ℝ) 5 hv 3
  rw [h0] at h
  norm_num at h
  exact h

/-- API client check: half gain converges to the target. -/
theorem test_api_tendsto_half {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + (1 / 2 : ℝ) * (5 - v n)) :
    Tendsto v atTop (𝓝 5) := by
  exact errorCorrection_tendsto (1 / 2 : ℝ) 5 hv (by norm_num) (by norm_num)

/-- API client check: at gain `2`, a sequence starting away from the target
does not converge to it. -/
theorem test_api_not_tendsto_two {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + 2 * (5 - v n)) (h0 : v 0 = 1) :
    ¬ Tendsto v atTop (𝓝 5) := by
  intro ht
  have hne : v 0 ≠ 5 := by rw [h0]; norm_num
  have h := (errorCorrection_tendsto_iff_of_ne 2 5 hv hne).mp ht
  norm_num at h

/-- API client check: at half gain, the sign theorem applies at `n = 3`. -/
theorem test_api_sign_half {v : ℕ → ℝ}
    (hv : ∀ n, v (n + 1) = v n + (1 / 2 : ℝ) * (5 - v n)) :
    0 ≤ (v 0 - 5) * (v 3 - 5) := by
  exact errorCorrection_mul_nonneg_of_le_one (1 / 2 : ℝ) 5 hv (by norm_num) 3

end MathlibExtTest.Algebra.AffineRecurrenceConvergence
