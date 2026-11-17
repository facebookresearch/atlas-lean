/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.MeanValue

import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Tests for mean values of Dirichlet series

The orthogonality integral at the degenerate base `u = 1` (where it is `2T`), the `sinc` bound,
and the coefficient-recovery and mean-square theorems for `∑ n⁻ˢ` at `σ = 2`.
-/

@[expose] public section

open Complex Filter Topology

namespace MeanValueTest

/-- `∫_{-T}^{T} 1^{it} dt = 2T`. -/
example {T : ℝ} (hT : 0 < T) : (∫ t in (-T)..T, ((1 : ℝ) : ℂ) ^ ((t : ℂ) * I)) = 2 * T := by
  rw [integral_ofReal_cpow_mul_I one_pos hT]
  simp

example : |Real.sinc 2| ≤ |(2 : ℝ)|⁻¹ := Real.abs_sinc_le_inv_abs two_ne_zero

/-- Coefficient recovery: `(1/2T) ∫ ζ(2 + it) m^{2+it} dt → 1`. -/
example {m : ℕ} (hm : m ≠ 0) : Tendsto (fun T : ℝ => (1 / (2 * (T : ℂ))) *
    ∫ t in (-T)..T, LSeries 1 ((2 : ℝ) + t * I) * (m : ℂ) ^ (((2 : ℝ) : ℂ) + t * I))
      atTop (𝓝 1) := by
  have hs : LSeriesSummable 1 (2 : ℝ) := LSeriesSummable_one_iff.mpr (by norm_num)
  simpa [hm] using hs.tendsto_integral_LSeries_mul_cpow_atTop hm

/-- The mean square of `ζ` on `Re s = 2` is `∑ n⁻⁴ = ζ(4)`, as a `tsum`. -/
example : Tendsto (fun T : ℝ => (1 / (2 * T)) * ∫ t in (-T)..T, ‖LSeries 1 ((2 : ℝ) + t * I)‖ ^ 2)
    atTop (𝓝 (∑' n : ℕ, ‖LSeries.term 1 (2 : ℝ) n‖ ^ 2)) :=
  (LSeriesSummable_one_iff.mpr (by norm_num)).tendsto_integral_norm_LSeries_sq_atTop

end MeanValueTest
