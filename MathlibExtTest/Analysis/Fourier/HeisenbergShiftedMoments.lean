/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.HeisenbergShiftedMoments

/-! # Tests for the Heisenberg inequality with shifted moments -/

open scoped FourierTransform
open MathlibExt.Analysis.Fourier.HeisenbergShiftedMomentsWanted

-- A single positive lower bound works for every normalized function and both centers.
example : ∃ k : ℝ, 0 < k ∧ ∀ (c d : ℝ) (f : SchwartzMap ℝ ℂ),
    (∫ x : ℝ, ‖f x‖ ^ 2) = 1 →
    k ≤ (∫ x : ℝ, (x - c) ^ 2 * ‖f x‖ ^ 2) *
      (∫ ξ : ℝ, (ξ - d) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
  obtain ⟨C, hC, bound⟩ := exists_const_sq_integral_sq_le_mul_shifted_moments_fourier
  refine ⟨1 / C, by positivity, ?_⟩
  intro c d f hf
  apply (div_le_iff₀ hC).2
  simpa [hf, mul_assoc, mul_comm, mul_left_comm] using bound c d f

-- Vanishing of either shifted moment forces zero mass.
example (c d : ℝ) (f : SchwartzMap ℝ ℂ)
    (h : (∫ x : ℝ, (x - c) ^ 2 * ‖f x‖ ^ 2) = 0 ∨
      (∫ ξ : ℝ, (ξ - d) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) = 0) :
    (∫ x : ℝ, ‖f x‖ ^ 2) = 0 := by
  obtain ⟨C, _, bound⟩ := exists_const_sq_integral_sq_le_mul_shifted_moments_fourier
  have hsq := bound c d f
  rcases h with h | h <;> simpa [h] using hsq
