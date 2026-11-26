/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringGeOne
import QuantumInfo.ForMathlib.Matrix

/-! # Tests for the Araki–Lieb–Thirring inequality at exponents at least one -/

namespace MathlibExtTest.LinearAlgebra.Matrix.ArakiLiebThirringGeOne

open MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted
open scoped ComplexOrder

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

private def P : Mat := Matrix.diagonal fun i => ((![(1 : ℝ), 0] i : ℝ) : ℂ)

/-- Compressing to one coordinate with a singular outer matrix allows an arbitrary positive
inner matrix, including matrices that do not commute with the projection. -/
example {B : Mat} (hB : B.PosSemidef) :
    RCLike.re (P * B * P).trace ≤ RCLike.re (cfc (· ^ (2 / 3 : ℝ) : ℝ → ℝ)
      (P * cfc (· ^ (3 / 2 : ℝ) : ℝ → ℝ) B * P)).trace := by
  have hP : P.PosSemidef := Matrix.PosSemidef.diagonal (by
    intro i
    fin_cases i <;> norm_num)
  have hpow (s : ℝ) (hs : s ≠ 0) : cfc (· ^ s : ℝ → ℝ) P = P := by
    unfold P
    refine (Matrix.cfc_diagonal (𝕜 := ℂ) ![(1 : ℝ), 0] (· ^ s)).trans ?_
    congr 1
    funext i
    fin_cases i <;> simp [Function.comp_def, Real.zero_rpow hs]
  have h := araki_lieb_thirring hP hB (q := 2 / 3) (r := 3 / 2) (by norm_num) (by norm_num)
  rw [hpow _ (by norm_num), hpow _ (by norm_num),
    show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num] at h
  have hHerm : (P * B * P).IsHermitian := by
    simpa only [hP.isHermitian.eq] using Matrix.isHermitian_conjTranspose_mul_mul P hB.isHermitian
  have hid : cfc (fun x : ℝ => x) (P * B * P) = P * B * P := cfc_id' ℝ _ (ha := hHerm)
  simpa only [Real.rpow_one, hid] using h

/-- At zero trace exponent, even zero matrices give the full dimension on both sides. -/
example {n : Type*} [Fintype n] [DecidableEq n] (r : ℝ) (hr : 1 ≤ r) :
    RCLike.re (cfc (· ^ (r * 0) : ℝ → ℝ)
      (cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) (0 : Matrix n n ℂ) * 0 *
        cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) (0 : Matrix n n ℂ))).trace = Fintype.card n ∧
    RCLike.re (cfc (· ^ (0 : ℝ) : ℝ → ℝ)
      (cfc (· ^ (r / 2) : ℝ → ℝ) (0 : Matrix n n ℂ) * cfc (· ^ r : ℝ → ℝ) (0 : Matrix n n ℂ) *
        cfc (· ^ (r / 2) : ℝ → ℝ) (0 : Matrix n n ℂ))).trace = Fintype.card n := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  simp [cfc_apply_zero, Real.zero_rpow hr₀.ne', Matrix.trace_one]

end MathlibExtTest.LinearAlgebra.Matrix.ArakiLiebThirringGeOne
