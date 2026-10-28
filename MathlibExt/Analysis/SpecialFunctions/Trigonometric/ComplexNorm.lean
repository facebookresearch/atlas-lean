/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Norms of the complex sine and cosine

## Main statements

* `Complex.normSq_sin`, `Complex.normSq_cos`: `|sin z|² = sin² x + sinh² y` and
  `|cos z|² = cos² x + sinh² y` for `z = x + iy`.
* `Real.abs_le_abs_sin_pi_mul_div_two`: Jordan's inequality `|d| ≤ |sin (πd/2)|` for `|d| ≤ 1`.
* `Complex.sq_le_sq_norm_sin_pi_mul_div_two`: if `s` is at distance at least `ρ ≥ 0` from every
  even integer, then `ρ² ≤ |sin (πs/2)|²`.
* `Complex.norm_cos_div_sin_pi_mul_div_two_le`: if `s` is at distance at least `ρ > 0` from every
  even integer, then `sin (πs/2) ≠ 0` and `|cot (πs/2)| ≤ 1/ρ + 1`.
-/

@[expose] public section

namespace Complex

/-- `|sin z|² = sin² (Re z) + sinh² (Im z)`. -/
theorem normSq_sin (z : ℂ) :
    normSq (sin z) = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [sin_eq z, ← ofReal_sin, ← ofReal_cos, ← ofReal_sinh, ← ofReal_cosh, ← ofReal_mul,
    ← ofReal_mul]
  simp only [normSq_apply, add_re, ofReal_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_zero,
    add_im, ofReal_im, mul_im, add_zero]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq z.im]

/-- `|cos z|² = cos² (Re z) + sinh² (Im z)`. -/
theorem normSq_cos (z : ℂ) :
    normSq (cos z) = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [cos_eq z, ← ofReal_sin, ← ofReal_cos, ← ofReal_sinh, ← ofReal_cosh, ← ofReal_mul,
    ← ofReal_mul]
  simp only [normSq_apply, sub_re, ofReal_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_zero,
    sub_im, ofReal_im, mul_im, add_zero, zero_sub, mul_neg, neg_mul, neg_neg]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq z.im]

/-- `‖sin z‖² = sin² (Re z) + sinh² (Im z)`. -/
theorem sq_norm_sin (z : ℂ) : ‖sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, normSq_sin]

/-- `‖cos z‖² = cos² (Re z) + sinh² (Im z)`. -/
theorem sq_norm_cos (z : ℂ) : ‖cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, normSq_cos]

end Complex

/-- **Jordan's inequality** in the form `|d| ≤ |sin (πd/2)|` for `|d| ≤ 1`. -/
theorem Real.abs_le_abs_sin_pi_mul_div_two {d : ℝ} (hd : |d| ≤ 1) :
    |d| ≤ |Real.sin (Real.pi * d / 2)| := by
  have hpi := Real.pi_pos
  rcases le_total 0 d with h | h
  · have := Real.mul_le_sin (x := Real.pi * d / 2) (by positivity)
      (by rw [abs_of_nonneg h] at hd; nlinarith)
    rw [abs_of_nonneg h]
    refine le_trans ?_ (le_trans this (le_abs_self _))
    field_simp; rfl
  · have := Real.mul_le_sin (x := Real.pi * (-d) / 2) (by nlinarith)
      (by rw [abs_of_nonpos h] at hd; nlinarith)
    rw [abs_of_nonpos h]
    rw [show Real.pi * (-d) / 2 = -(Real.pi * d / 2) by ring, Real.sin_neg] at this
    refine le_trans ?_ (le_trans this (neg_le_abs _))
    field_simp; rfl

namespace Complex

/-- If `s` is at distance at least `ρ ≥ 0` from every even integer, then
`ρ² ≤ ‖sin (πs/2)‖²`. -/
theorem sq_le_sq_norm_sin_pi_mul_div_two {ρ : ℝ} (hρ0 : 0 ≤ ρ) (s : ℂ)
    (h : ∀ k : ℤ, ρ ≤ ‖s - 2 * (k : ℂ)‖) :
    ρ ^ 2 ≤ ‖sin (Real.pi * s / 2)‖ ^ 2 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.two_le_pi
  set k : ℤ := ⌊(s.re + 1) / 2⌋ with hk
  have hk1 := Int.floor_le ((s.re + 1) / 2)
  have hk2 := Int.lt_floor_add_one ((s.re + 1) / 2)
  rw [← hk] at hk1 hk2
  set d : ℝ := s.re - 2 * k with hd
  have hdabs : |d| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hre : (Real.pi * s / 2 : ℂ).re = Real.pi * d / 2 + k * Real.pi := by
    simp [hd]; ring
  have him : (Real.pi * s / 2 : ℂ).im = Real.pi * s.im / 2 := by simp
  rw [sq_norm_sin, hre, him]
  have hsin : Real.sin (Real.pi * d / 2 + k * Real.pi) ^ 2 = Real.sin (Real.pi * d / 2) ^ 2 := by
    rw [Real.sin_add_int_mul_pi (Real.pi * d / 2) k, mul_pow]
    rcases Int.even_or_odd k with he | ho
    · simp [he.neg_one_zpow]
    · simp [ho.neg_one_zpow]
  rw [hsin]
  have h1 : d ^ 2 ≤ Real.sin (Real.pi * d / 2) ^ 2 := by
    have := Real.abs_le_abs_sin_pi_mul_div_two hdabs
    nlinarith [abs_nonneg d, sq_abs d, sq_abs (Real.sin (Real.pi * d / 2))]
  set v : ℝ := Real.pi * s.im / 2 with hv
  have h2 : v ^ 2 ≤ Real.sinh v ^ 2 := by
    rcases le_total 0 v with hv0 | hv0
    · have := Real.self_le_sinh_iff.mpr hv0; nlinarith
    · have := (Real.self_le_sinh_iff (x := -v)).mpr (by linarith)
      rw [Real.sinh_neg] at this; nlinarith
  have h3 : s.im ^ 2 ≤ v ^ 2 := by
    have hp : 1 ≤ (Real.pi / 2) ^ 2 := by nlinarith
    calc s.im ^ 2 = 1 * s.im ^ 2 := by ring
      _ ≤ (Real.pi / 2) ^ 2 * s.im ^ 2 := by gcongr
      _ = v ^ 2 := by rw [hv]; ring
  have hn : ‖s - 2 * (k : ℂ)‖ ^ 2 = d ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; simp [hd]; ring
  have hρ := h k
  nlinarith [norm_nonneg (s - 2 * (k : ℂ))]

/-- If `s` is at distance at least `ρ > 0` from every even integer, then `sin (πs/2) ≠ 0`
and `‖cot (πs/2)‖ ≤ 1/ρ + 1`. -/
theorem norm_cos_div_sin_pi_mul_div_two_le {ρ : ℝ} (hρ0 : 0 < ρ) (s : ℂ)
    (h : ∀ k : ℤ, ρ ≤ ‖s - 2 * (k : ℂ)‖) :
    sin (Real.pi * s / 2) ≠ 0 ∧
      ‖cos (Real.pi * s / 2) / sin (Real.pi * s / 2)‖ ≤ 1 / ρ + 1 := by
  have hsinlb := sq_le_sq_norm_sin_pi_mul_div_two hρ0.le s h
  have hsin0 : sin (Real.pi * s / 2) ≠ 0 := by
    intro h; rw [h, norm_zero] at hsinlb; nlinarith
  refine ⟨hsin0, ?_⟩
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hsin0)]
  have hc2 := sq_norm_cos (Real.pi * s / 2)
  have hs2 := sq_norm_sin (Real.pi * s / 2)
  have hcosle : Real.cos (Real.pi * s / 2 : ℂ).re ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact Real.abs_cos_le_one _
  have hsinnn := sq_nonneg (Real.sin (Real.pi * s / 2 : ℂ).re)
  set S := ‖sin (Real.pi * s / 2)‖ with hS
  set Cn := ‖cos (Real.pi * s / 2)‖ with hCn
  have hq : 1 / ρ * ρ = 1 := by field_simp
  have hq0 : 0 < 1 / ρ := by positivity
  have hSn : 0 ≤ S := norm_nonneg _
  have hCnn : 0 ≤ Cn := norm_nonneg _
  have h1 : 1 ≤ (1 / ρ) ^ 2 * S ^ 2 := by
    calc (1 : ℝ) = (1 / ρ) ^ 2 * ρ ^ 2 := by rw [← mul_pow, hq]; norm_num
      _ ≤ _ := by gcongr
  have hsq : Cn ^ 2 ≤ ((1 / ρ + 1) * S) ^ 2 := by
    nlinarith [mul_nonneg hq0.le (sq_nonneg S)]
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 1 / ρ + 1) hSn]

end Complex
