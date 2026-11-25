/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Approximation.ChebyshevAnalytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Tests for the Chebyshev coefficient bound for analytic functions -/

namespace MathlibExtTest.Analysis.Approximation.ChebyshevAnalytic

open MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted
open Filter Topology

/-- A constant bounds the coefficient in degree zero by its norm. -/
example (c : ℂ) {ρ : ℝ} (hρ : 1 < ρ) : ‖chebCoeff (fun _ => c) 0‖ ≤ ‖c‖ :=
  (norm_chebCoeff_le_of_analytic hρ (f := fun _ => c) (differentiableOn_const c)
    fun _ _ => le_rfl).1

/-- Letting `ρ → ∞`, the higher Chebyshev coefficients of a constant vanish. -/
example (c : ℂ) {k : ℕ} (hk : 1 ≤ k) : chebCoeff (fun _ => c) k = 0 := by
  have hlim : Tendsto (fun ρ : ℝ => 2 * ‖c‖ * (ρ ^ k)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega))).const_mul
      (2 * ‖c‖)
  refine norm_le_zero_iff.mp (ge_of_tendsto hlim ?_)
  filter_upwards [eventually_gt_atTop 1] with ρ hρ
  exact (norm_chebCoeff_le_of_analytic hρ (f := fun _ => c) (differentiableOn_const c)
    fun _ _ => le_rfl).2 k hk

/-- Points of the Bernstein ellipse `E_ρ` have norm less than its semi-major axis. -/
private theorem norm_lt_of_mem {ρ : ℝ} {z : ℂ} (hz : z ∈ bernsteinEllipse ρ) :
    ‖z‖ < (ρ + ρ⁻¹) / 2 := by
  have h : ‖(z - 1) + (z + 1)‖ ≤ ‖z - 1‖ + ‖z + 1‖ := norm_add_le _ _
  rw [show (z - 1) + (z + 1) = 2 * z by ring, norm_mul, Complex.norm_two] at h
  have hz' : ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹ := hz
  linarith

/-- The exponential is bounded by `exp ((ρ + ρ⁻¹) / 2)` on `E_ρ`, so its Chebyshev coefficients
decay like `ρ^{-k}` for every `ρ > 1`. -/
example {ρ : ℝ} (hρ : 1 < ρ) {k : ℕ} (hk : 1 ≤ k) :
    ‖chebCoeff (fun x => Complex.exp x) k‖ ≤ 2 * Real.exp ((ρ + ρ⁻¹) / 2) * (ρ ^ k)⁻¹ := by
  refine (norm_chebCoeff_le_of_analytic hρ (f := Complex.exp)
    Complex.differentiable_exp.differentiableOn fun z hz => ?_).2 k hk
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans (norm_lt_of_mem hz).le)

end MathlibExtTest.Analysis.Approximation.ChebyshevAnalytic
