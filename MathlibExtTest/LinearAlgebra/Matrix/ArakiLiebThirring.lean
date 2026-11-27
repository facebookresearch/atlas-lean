/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirring
import QuantumInfo.ForMathlib.Matrix

/-! # Tests for the reversed Araki–Lieb–Thirring inequality -/

namespace MathlibExtTest.LinearAlgebra.Matrix.ArakiLiebThirring

open MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted
open scoped ComplexOrder

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

private def P : Mat := Matrix.diagonal fun i => ((![(1 : ℝ), 0] i : ℝ) : ℂ)

private lemma P_pow {s : ℝ} (hs : s ≠ 0) : cfc (· ^ s : ℝ → ℝ) P = P := by
  unfold P
  refine (Matrix.cfc_diagonal (𝕜 := ℂ) ![(1 : ℝ), 0] (· ^ s)).trans ?_
  congr 1
  funext i
  fin_cases i <;> simp [Function.comp_def, Real.zero_rpow hs]

private def B : Mat := !![1, 1; 1, 1]

/-- Two singular, noncommuting matrices at fractional exponents. Since `P B P = P`,
the bound on the trace is one. -/
example : RCLike.re (cfc (· ^ (3 / 2 : ℝ) : ℝ → ℝ)
    (P * cfc (· ^ (1 / 2 : ℝ) : ℝ → ℝ) B * P)).trace ≤ 1 := by
  have hP : P.PosSemidef := Matrix.PosSemidef.diagonal (by
    intro i
    fin_cases i <;> norm_num)
  let X : Mat := !![1, 1; 0, 0]
  have hB : B.PosSemidef := by
    have h : X.conjTranspose * X = B := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [X, B, Matrix.mul_apply, Fin.sum_univ_two]
    exact h ▸ Matrix.posSemidef_conjTranspose_mul_self X
  have hPBP : P * B * P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, B]
  have h := araki_lieb_thirring_of_le_one hP hB (q := 3 / 2) (r := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  rw [P_pow (by norm_num), P_pow (by norm_num), hPBP, P_pow (by norm_num)] at h
  simpa [P, Matrix.trace, Fin.sum_univ_two] using h

/-- At `r = 0`, even zero input matrices give the dimension on each side. -/
example (q : ℝ) :
    RCLike.re (cfc (· ^ q : ℝ → ℝ)
      (cfc (· ^ ((0 : ℝ) / 2) : ℝ → ℝ) (0 : Mat) * cfc (· ^ (0 : ℝ) : ℝ → ℝ) (0 : Mat) *
        cfc (· ^ ((0 : ℝ) / 2) : ℝ → ℝ) (0 : Mat))).trace = 2 ∧
    RCLike.re (cfc (· ^ (0 * q) : ℝ → ℝ)
      (cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) (0 : Mat) * 0 * cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ)
        (0 : Mat))).trace = 2 := by
  norm_num [cfc_apply_zero, cfc_apply_one, Matrix.trace, Fin.sum_univ_two]

end MathlibExtTest.LinearAlgebra.Matrix.ArakiLiebThirring
