/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.ComplexNorm

/-!
# Bounds for the complex cotangent away from the real axis

We bound `|cos z|` by `|sin z|`, so that the cotangent is bounded, away from the zeros of `sin`.

## Main statements

* `Complex.norm_cos_le_two_mul_norm_sin_of_one_le_abs_im`, `Complex.sin_ne_zero_of_one_le_abs_im`:
  if `|Im z| ≥ 1`, then `sin z ≠ 0` and `|cos z| ≤ 2 |sin z|`.
* `Complex.norm_cos_le_norm_sin_of_cos_re_eq_zero`, `Complex.sin_ne_zero_of_cos_re_eq_zero`: on the
  lines `Re z = π/2 + kπ`, `sin z ≠ 0` and `|cos z| ≤ |sin z|`.
-/

@[expose] public section

namespace Complex

private lemma sin_ne_zero_and_norm_cos_le_of_one_le_abs_im {z : ℂ} (hz : 1 ≤ |z.im|) :
    sin z ≠ 0 ∧ ‖cos z‖ ≤ 2 * ‖sin z‖ := by
  have h1 : ‖exp (z * I)‖ = Real.exp (-z.im) := by rw [norm_exp]; simp
  have h2 : ‖exp (-z * I)‖ = Real.exp z.im := by rw [norm_exp]; simp
  have hs : ‖sin z‖ * 2 = ‖exp (-z * I) - exp (z * I)‖ := by rw [sin]; simp
  have hc : ‖cos z‖ * 2 = ‖exp (z * I) + exp (-z * I)‖ := by rw [cos]; simp
  have hs' : |Real.exp z.im - Real.exp (-z.im)| ≤ ‖sin z‖ * 2 := by
    rw [hs, ← h1, ← h2]; exact abs_norm_sub_norm_le _ _
  have hc' : ‖cos z‖ * 2 ≤ Real.exp z.im + Real.exp (-z.im) := by
    rw [hc, ← h1, ← h2, add_comm (‖_‖)]; exact norm_add_le _ _
  have key : Real.exp z.im + Real.exp (-z.im) ≤ 2 * |Real.exp z.im - Real.exp (-z.im)| := by
    have e1 : Real.exp (-z.im) * Real.exp z.im = 1 := by rw [← Real.exp_add]; simp
    have hp := Real.exp_pos z.im
    have hq := Real.exp_pos (-z.im)
    rcases le_or_gt 0 z.im with hy | hy
    · rw [abs_of_nonneg hy] at hz
      have e2 : 1 + 2 * z.im ≤ Real.exp (2 * z.im) := by
        have := Real.add_one_le_exp (2 * z.im); linarith
      have e3 : Real.exp (2 * z.im) = Real.exp z.im * Real.exp z.im := by
        rw [← Real.exp_add]; ring_nf
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    · rw [abs_of_neg hy] at hz
      have e2 : 1 + 2 * (-z.im) ≤ Real.exp (2 * (-z.im)) := by
        have := Real.add_one_le_exp (2 * (-z.im)); linarith
      have e3 : Real.exp (2 * (-z.im)) = Real.exp (-z.im) * Real.exp (-z.im) := by
        rw [← Real.exp_add]; ring_nf
      rw [abs_of_nonpos (by nlinarith)]
      nlinarith
  have hpos : 0 < Real.exp z.im + Real.exp (-z.im) := by positivity
  constructor
  · intro h0
    rw [h0, norm_zero] at hs'
    nlinarith [abs_nonneg (Real.exp z.im - Real.exp (-z.im))]
  · nlinarith

/-- Away from the real axis, `|Im z| ≥ 1`, the cotangent is bounded: `|cos z| ≤ 2 |sin z|`. -/
theorem norm_cos_le_two_mul_norm_sin_of_one_le_abs_im {z : ℂ} (hz : 1 ≤ |z.im|) :
    ‖cos z‖ ≤ 2 * ‖sin z‖ :=
  (sin_ne_zero_and_norm_cos_le_of_one_le_abs_im hz).2

/-- `sin z ≠ 0` when `|Im z| ≥ 1`. -/
theorem sin_ne_zero_of_one_le_abs_im {z : ℂ} (hz : 1 ≤ |z.im|) : sin z ≠ 0 :=
  (sin_ne_zero_and_norm_cos_le_of_one_le_abs_im hz).1

/-- On the lines `Re z = π/2 + kπ` (where `cos (Re z) = 0`), `|cos z| ≤ |sin z|`. -/
theorem norm_cos_le_norm_sin_of_cos_re_eq_zero {z : ℂ} (hz : Real.cos z.re = 0) :
    ‖cos z‖ ≤ ‖sin z‖ := by
  have hs := sq_norm_sin z
  have hc := sq_norm_cos z
  have h1 := Real.sin_sq_add_cos_sq z.re
  rw [hz] at hc h1
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith)

/-- On the lines `Re z = π/2 + kπ` (where `cos (Re z) = 0`), `sin z ≠ 0`. -/
theorem sin_ne_zero_of_cos_re_eq_zero {z : ℂ} (hz : Real.cos z.re = 0) : sin z ≠ 0 := by
  intro h
  have hs := sq_norm_sin z
  have h1 := Real.sin_sq_add_cos_sq z.re
  rw [hz, h, norm_zero] at *
  nlinarith [sq_nonneg (Real.sinh z.im)]

end Complex
