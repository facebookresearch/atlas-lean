/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.RiemannZetaBounds

/-!
# Tests for bounds on `ζ` near the line `Re s = 1`

The sawtooth bound at concrete points, the Euler–Maclaurin formula at `n = 1`, and the
`3`-`4`-`1` inequality on the real axis.
-/

@[expose] public section

namespace RiemannZetaBoundsTest

example : |(5 / 2 : ℝ) - (⌊(5 / 2 : ℝ)⌋ : ℝ) - 1 / 2| ≤ 1 / 2 := abs_sub_floor_sub_half_le _

/-- The sawtooth vanishes at half-integers. -/
example : (5 / 2 : ℝ) - (⌊(5 / 2 : ℝ)⌋ : ℝ) - 1 / 2 = 0 := by
  rw [show ⌊(5 / 2 : ℝ)⌋ = 2 by norm_num [Int.floor_eq_iff]]
  norm_num

/-- Euler–Maclaurin at `n = 1`:
`ζ(s) = 1/2 + 1/(s - 1) - s ∫_1^∞ (x - ⌊x⌋ - 1/2) x^{-s-1} dx`. -/
example {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / 2 + 1 / (s - 1) - s * ∫ x in Set.Ioi (1 : ℝ),
      ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1) := by
  have h := riemannZeta_eq_sum_add_integral_sawtooth hs hs1 (n := 1) le_rfl
  simpa using h

/-- The `3`-`4`-`1` inequality at `t = 0`: `|ζ(σ)|⁸ ≥ 1`. -/
example : 1 ≤ ‖riemannZeta ((2 : ℝ) : ℂ) ^ 3 * riemannZeta (((2 : ℝ) : ℂ) + (0 : ℝ) * Complex.I) ^ 4 *
    riemannZeta (((2 : ℝ) : ℂ) + 2 * (0 : ℝ) * Complex.I)‖ :=
  one_le_norm_riemannZeta_pow_three_mul (by norm_num)

/-- The convexity-type bound `ζ(s) ≪ |t|^{1/2}` on `Re s ≥ 1/2`. -/
example : ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ C * |t| ^ (1 / 2 : ℝ) := by
  obtain ⟨C, T₀, hC, hT₀, h⟩ := exists_pos_norm_riemannZeta_le_mul_abs_im_rpow_half
  refine ⟨C, T₀, hC, hT₀, fun t ht => ?_⟩
  have := h (1 / 2 + t * Complex.I) (by simp) (by simpa using ht)
  simpa using this

end RiemannZetaBoundsTest
