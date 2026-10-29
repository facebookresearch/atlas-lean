/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.ZeroCounting
import MathlibExt.NumberTheory.LSeries.RiemannXiZeros

/-!
# Tests for zero counting

Instantiations of the zero-density bounds for `ζ` at an actual enumeration of the zeros.
-/

@[expose] public section

open RiemannXi

namespace ZeroCountingTest

/-- The elementary inequality `1 / (1 + (T - γ)²) ≤ 4 Re (1 / (2 + iT - ρ) + 1 / ρ)` at
`ρ = 1/2 + iT`. -/
example (T : ℝ) : 1 / (1 + (T - (1 / 2 + T * Complex.I : ℂ).im) ^ 2) ≤
    4 * (1 / ((2 : ℂ) + T * Complex.I - (1 / 2 + T * Complex.I)) +
      1 / (1 / 2 + T * Complex.I)).re :=
  one_div_one_add_sq_sub_im_le_re (by simp) (by norm_num) T

/-- The weighted zero count near height `T` is `O(log T)`, at an actual enumeration. -/
example : ∃ C : ℝ, ∃ (ι : Type) (z : ι → ℂ), ∀ T : ℝ, 2 ≤ T →
    ∑' n, 1 / (1 + (T - (z n).im) ^ 2) ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := exists_tsum_one_div_one_add_sq_sub_im_le_log.{0}
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  exact ⟨C, ι, z, fun T hT => (hC z hz T hT).2⟩

/-- `∑_{|γ| < R} 1/|ρ| = O(log² R)`, at an actual enumeration. -/
example : ∃ C : ℝ, ∃ (ι : Type) (z : ι → ℂ), ∀ R : ℝ, 2 ≤ R →
    ∑' n, (if |(z n).im| < R then 1 / ‖z n‖ else 0) ≤ C * Real.log R ^ 2 := by
  obtain ⟨C, hC⟩ := exists_tsum_one_div_norm_le_log_sq.{0}
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  exact ⟨C, ι, z, hC z hz⟩

/-- `ζ'/ζ` is bounded on `Re s ≥ 2`. -/
example : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ K := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_logDeriv_riemannZeta_le (δ := 1) one_pos
  exact ⟨K, hK0, fun s hs => hK s (by linarith)⟩

end ZeroCountingTest
