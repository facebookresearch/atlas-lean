/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArcSlSubstSl

open MetaMathlibExt PowerSeries

variable (S C : PowerSeries ℚ)
    (hS : derivative S = C ^ 2) (hC : derivative C = -(S ^ 2))
    (hS0 : constantCoeff S = 0) (hC0 : constantCoeff C = 1)

-- Substituting Sl into ArcSl gives the variable.
example : (PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S =
    PowerSeries.X :=
  arcSl_subst_sl S C hS hC hS0 hC0

-- Hence the linear coefficient of the composition is one.
example : coeff 1
    ((PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S) = 1 := by
  rw [arcSl_subst_sl S C hS hC hS0 hC0]
  simp

-- And the coefficient of degree four of the composition vanishes.
example : coeff 4
    ((PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S) = 0 := by
  rw [arcSl_subst_sl S C hS hC hS0 hC0, coeff_X]
  norm_num

-- Differentiating the identity gives the derivative of the composition.
example : derivative ((PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S) = 1 := by
  rw [arcSl_subst_sl S C hS hC hS0 hC0]
  simp

-- The first nonlinear coefficient of ArcSl itself is `1 / 6`.
example : coeff 4 (PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0) = 1 / 6 := by
  rw [coeff_mk]
  norm_num [Ring.choose_one_right]

/-! The hypotheses of `arcSl_subst_sl` can be met: the coefficient recursion below defines power
series `sl` and `cl` with `sl' = cl ^ 2`, `cl' = -sl ^ 2`, `sl(0) = 0` and `cl(0) = 1`, the Taylor
series at `0` of `Sl` and `Cl`. -/

namespace MetaMathlibExtTest.ArcSlSubstSl

/-- The Taylor coefficients `(sₙ, cₙ)` of `Sl` and `Cl`, determined by `s₀ = 0`, `c₀ = 1`,
`(n + 1) sₙ₊₁ = ∑ᵢ cᵢ cₙ₋ᵢ` and `(n + 1) cₙ₊₁ = -∑ᵢ sᵢ sₙ₋ᵢ`. -/
private def slClCoeff : ℕ → ℚ × ℚ
  | 0 => (0, 1)
  | n + 1 =>
    ((∑ i : Fin (n + 1), (slClCoeff i).2 * (slClCoeff (n - i)).2) / (n + 1),
      -(∑ i : Fin (n + 1), (slClCoeff i).1 * (slClCoeff (n - i)).1) / (n + 1))
decreasing_by all_goals omega

private theorem slClCoeff_zero : slClCoeff 0 = (0, 1) := by
  rw [slClCoeff]

private theorem slClCoeff_succ (n : ℕ) :
    slClCoeff (n + 1) =
      ((∑ p ∈ Finset.antidiagonal n, (slClCoeff p.1).2 * (slClCoeff p.2).2) / (n + 1),
        -(∑ p ∈ Finset.antidiagonal n, (slClCoeff p.1).1 * (slClCoeff p.2).1) / (n + 1)) := by
  rw [slClCoeff, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (slClCoeff i).2 * (slClCoeff j).2),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (slClCoeff i).1 * (slClCoeff j).1),
    ← Fin.sum_univ_eq_sum_range (fun i => (slClCoeff i).2 * (slClCoeff (n - i)).2),
    ← Fin.sum_univ_eq_sum_range (fun i => (slClCoeff i).1 * (slClCoeff (n - i)).1)]

/-- The Taylor series of `Sl` at `0`. -/
private noncomputable def sl : PowerSeries ℚ := PowerSeries.mk fun n => (slClCoeff n).1

/-- The Taylor series of `Cl` at `0`. -/
private noncomputable def cl : PowerSeries ℚ := PowerSeries.mk fun n => (slClCoeff n).2

private theorem derivative_sl : derivative sl = cl ^ 2 := by
  ext n
  rw [coeff_derivative, pow_two, coeff_mul]
  simp only [sl, cl, coeff_mk, slClCoeff_succ]
  field_simp

private theorem derivative_cl : derivative cl = -(sl ^ 2) := by
  ext n
  rw [coeff_derivative, map_neg, pow_two, coeff_mul]
  simp only [sl, cl, coeff_mk, slClCoeff_succ]
  field_simp

private theorem constantCoeff_sl : constantCoeff sl = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, sl, coeff_mk, slClCoeff_zero]

private theorem constantCoeff_cl : constantCoeff cl = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, cl, coeff_mk, slClCoeff_zero]

-- With this witness, substituting the series of `Sl` into `ArcSl` gives the variable.
example : (PowerSeries.mk fun k => if k % 3 = 1 then
      (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst sl =
    PowerSeries.X :=
  arcSl_subst_sl sl cl derivative_sl derivative_cl constantCoeff_sl constantCoeff_cl

-- The witness starts as `Sl(u) = u - u ^ 4 / 6 + ⋯`.
example : coeff 1 sl = 1 ∧ coeff 2 sl = 0 ∧ coeff 3 sl = 0 ∧ coeff 4 sl = -1 / 6 := by
  simp only [sl, coeff_mk, slClCoeff_succ, slClCoeff_zero, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  norm_num

end MetaMathlibExtTest.ArcSlSubstSl
