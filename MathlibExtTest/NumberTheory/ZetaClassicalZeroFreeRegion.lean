/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZetaClassicalZeroFreeRegion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Tests for `MathlibExt.NumberTheory.ZetaClassicalZeroFreeRegion` -/

namespace MathlibExtTest.ZetaClassicalZeroFreeRegion

open Complex MathlibExt.NumberTheory.ZetaClassicalZeroFreeRegionWanted

-- The logarithm in the bound is positive for every imaginary part, so the region is never empty.
example (t : ℝ) : 0 < Real.log (2 + |t|) := Real.log_pos (by linarith [abs_nonneg t])

-- The theorem recovers the non-vanishing of `ζ` on the line `Re s = 1`, away from the pole.
example (s : ℂ) (hs : s.re = 1) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  obtain ⟨c, hc, h⟩ := riemannZeta_ne_zero_of_classical_zero_free_region
  refine h s hs1 ?_
  have : 0 < c / Real.log (2 + |s.im|) :=
    div_pos hc (Real.log_pos (by linarith [abs_nonneg s.im]))
  linarith

-- Halfway into the region: `ζ` does not vanish at `1 - c / (2 log (2 + |t|)) + i t`, a point
-- strictly to the left of the line `Re s = 1`.
example : ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
    riemannZeta (((1 - c / (2 * Real.log (2 + |t|)) : ℝ) : ℂ) + t * I) ≠ 0 := by
  obtain ⟨c, hc, h⟩ := riemannZeta_ne_zero_of_classical_zero_free_region
  refine ⟨c, hc, fun t => ?_⟩
  have hL : 0 < Real.log (2 + |t|) := Real.log_pos (by linarith [abs_nonneg t])
  have hre : (((1 - c / (2 * Real.log (2 + |t|)) : ℝ) : ℂ) + t * I).re =
      1 - c / (2 * Real.log (2 + |t|)) := by
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_zero,
      add_zero]
  have him : (((1 - c / (2 * Real.log (2 + |t|)) : ℝ) : ℂ) + t * I).im = t := by
    simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_one, mul_zero, zero_add,
      add_zero]
  have hhalf : c / (2 * Real.log (2 + |t|)) = c / Real.log (2 + |t|) / 2 := by
    rw [div_div, mul_comm]
  have hpos : 0 < c / Real.log (2 + |t|) := div_pos hc hL
  refine h _ ?_ ?_
  · intro h1
    have := congrArg Complex.re h1
    rw [hre, one_re, hhalf] at this
    linarith
  · rw [hre, him, hhalf]
    linarith

-- On every horizontal line there is an interval `(σ₀, 1)` free of zeros of `ζ`, of length at
-- least a fixed multiple of `1 / log (2 + |t|)`.
example : ∃ c : ℝ, 0 < c ∧ ∀ t σ : ℝ, 1 - c / Real.log (2 + |t|) < σ → σ < 1 →
    riemannZeta ((σ : ℂ) + t * I) ≠ 0 := by
  obtain ⟨c, hc, h⟩ := riemannZeta_ne_zero_of_classical_zero_free_region
  refine ⟨c, hc, fun t σ hσ hσ1 => h _ ?_ ?_⟩
  · intro h1
    have := congrArg Complex.re h1
    simp at this
    linarith
  · simpa using hσ

end MathlibExtTest.ZetaClassicalZeroFreeRegion
