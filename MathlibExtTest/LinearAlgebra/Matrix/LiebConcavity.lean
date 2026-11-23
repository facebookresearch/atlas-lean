/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.LiebConcavity
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Tests for `MathlibExt.LinearAlgebra.Matrix.LiebConcavity`

Lieb's theorem is used in its two-point form at a midpoint, and evaluated in a commuting case:
for the diagonal `H = diag(1, -1)` and scalar matrices `A = r • 1`,
`tr exp(H + log A) = r (e + e⁻¹)` is linear in `r`, so the concavity inequality holds with
equality.
-/

@[expose] public section

open MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted
open scoped ComplexOrder

namespace MathlibExtTest.LinearAlgebra.Matrix.LiebConcavity

/-- The two-point form of Lieb's theorem at the midpoint. -/
example {n : Type*} [Fintype n] [DecidableEq n] {H A₁ A₂ : Matrix n n ℂ} (hH : H.IsHermitian)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) :
    (RCLike.re (NormedSpace.exp (H + cfc Real.log A₁)).trace +
        RCLike.re (NormedSpace.exp (H + cfc Real.log A₂)).trace) / 2 ≤
      RCLike.re
        (NormedSpace.exp (H + cfc Real.log ((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂))).trace := by
  have h := (lieb_concavity hH).2 hA₁ hA₂ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  linarith

/-- The diagonal matrix `diag(1, -1)`. -/
noncomputable abbrev H₀ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]

lemma isHermitian_H₀ : H₀.IsHermitian := by
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  fin_cases i <;> simp [IsSelfAdjoint]

/-- The scalar matrix `r • 1` of size two. -/
noncomputable abbrev sc (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := algebraMap ℝ _ r

lemma posDef_sc {r : ℝ} (hr : 0 < r) : (sc r).PosDef := by
  rw [sc, Matrix.algebraMap_eq_diagonal]
  exact Matrix.PosDef.diagonal fun _ => by simpa using hr

/-- In the commuting case `H = diag(1, -1)`, `A = r • 1`, `tr exp(H + log A) = r (e + e⁻¹)`. -/
lemma re_trace_exp_H₀_sc {r : ℝ} (hr : 0 < r) :
    RCLike.re (NormedSpace.exp (H₀ + cfc Real.log (sc r))).trace =
      r * (Real.exp 1 + Real.exp (-1)) := by
  rw [cfc_algebraMap r Real.log, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_add,
    Matrix.exp_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two, Pi.exp_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← Complex.exp_eq_exp_ℂ,
    Pi.algebraMap_apply, Complex.coe_algebraMap, map_add, Complex.exp_add]
  rw [← Complex.ofReal_exp, Real.exp_log hr, ← Complex.ofReal_one, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  simp only [RCLike.re_to_complex, Complex.ofReal_re, ← Complex.ofReal_mul]
  ring

/-- In this commuting case the concavity inequality of Lieb's theorem is an equality:
`(f(1) + f(3)) / 2 = f(2)` for `f(A) = tr exp(H₀ + log A)`. -/
example :
    (1 / 2 : ℝ) * RCLike.re (NormedSpace.exp (H₀ + cfc Real.log (sc 1))).trace +
        (1 / 2 : ℝ) * RCLike.re (NormedSpace.exp (H₀ + cfc Real.log (sc 3))).trace =
      RCLike.re (NormedSpace.exp (H₀ + cfc Real.log
        ((1 / 2 : ℝ) • sc 1 + (1 / 2 : ℝ) • sc 3))).trace ∧
    (1 / 2 : ℝ) * RCLike.re (NormedSpace.exp (H₀ + cfc Real.log (sc 1))).trace +
        (1 / 2 : ℝ) * RCLike.re (NormedSpace.exp (H₀ + cfc Real.log (sc 3))).trace ≤
      RCLike.re (NormedSpace.exp (H₀ + cfc Real.log
        ((1 / 2 : ℝ) • sc 1 + (1 / 2 : ℝ) • sc 3))).trace := by
  have hmid : (1 / 2 : ℝ) • sc 1 + (1 / 2 : ℝ) • sc 3 = sc 2 := by
    rw [Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul, ← map_add]
    norm_num
  refine ⟨?_, by
    simpa only [smul_eq_mul] using (lieb_concavity isHermitian_H₀).2 (posDef_sc one_pos)
      (posDef_sc (by norm_num : (0 : ℝ) < 3)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)⟩
  rw [hmid, re_trace_exp_H₀_sc one_pos, re_trace_exp_H₀_sc (by norm_num),
    re_trace_exp_H₀_sc two_pos]
  ring

end MathlibExtTest.LinearAlgebra.Matrix.LiebConcavity
