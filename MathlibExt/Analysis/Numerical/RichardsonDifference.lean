/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Richardson extrapolation of the centered difference quotient

The first extrapolation cancels the term of degree two in the step size, and the second
also cancels the term of degree four. The Lagrange remainder gives uniform bounds on a
fixed closed interval without assuming an infinite Taylor expansion.

## References

* D. Levy, *Introduction to Numerical Analysis*, University of Maryland lecture notes,
  4 January 2021, §5.4, (5.18)–(5.23) and the unnumbered sixth-order formula immediately
  after (5.23), pp. 97–98. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
-/

public section

open Set

namespace MetaMathlibExt

/-- The centered difference quotient at `x` with step `h` is
`(f (x + h) - f (x - h)) / (2 * h)`. At `h = 0` it is zero by totalized division. -/
@[expose] noncomputable def centeredDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f (x - h)) / (2 * h)

/-- The first Richardson extrapolation `S(h) = (4 D(h) - D(2h)) / 3`, where
`D(t) = (f (x + t) - f (x - t)) / (2 * t)` is the centered difference quotient at `x`. -/
@[expose] noncomputable def richardsonDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (4 * centeredDifference f x h - centeredDifference f x (2 * h)) / 3

/-- The first Richardson extrapolation of the centered quotient is the four-point formula
`(-f (x + 2*h) + 8*f (x + h) - 8*f (x - h) + f (x - 2*h)) / (12*h)`.
The identity also holds at `h = 0`: both sides are zero by totalized division. -/
theorem richardsonDifference_eq_fourPoint (f : ℝ → ℝ) (x h : ℝ) :
    richardsonDifference f x h =
      (-f (x + 2 * h) + 8 * f (x + h) - 8 * f (x - h) + f (x - 2 * h)) / (12 * h) := by
  by_cases hh : h = 0
  · simp [hh, richardsonDifference, centeredDifference]
  · unfold richardsonDifference centeredDifference
    field_simp
    ring

-- Use the same closed interval to bound every remainder and to take the Taylor coefficients.
private theorem exists_uniform_taylor_bound {f : ℝ → ℝ} {a b x : ℝ} {n : ℕ}
    (hab : a < b) (hx : x ∈ Icc a b) (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    ∃ C ≥ 0, ∀ y ∈ Icc a b,
      |f y - taylorWithinEval f n (Icc a b) x y| ≤ C * |y - x| ^ (n + 1) := by
  have hu := uniqueDiffOn_Icc hab
  have hcont : ContinuousOn (fun z ↦
      |iteratedDerivWithin (n + 1) f (Icc a b) z / (Nat.factorial (n + 1) : ℝ)|) (Icc a b) :=
    ((hf.continuousOn_iteratedDerivWithin (by simp) hu).div_const _).abs
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨C, (abs_nonneg _).trans (hC (mem_image_of_mem _ hx)), ?_⟩
  intro y hy
  by_cases hxy : x = y
  · subst y
    simp
  have hsub := uIcc_subset_Icc hx hy
  have huv := uniqueDiffOn_uIcc hxy
  have hseg := hf.mono hsub
  have hcoeff (k : ℕ) (hk : k ≤ n + 1) {z : ℝ} (hz : z ∈ uIcc x y) :
      iteratedDerivWithin k f (uIcc x y) z = iteratedDerivWithin k f (Icc a b) z := by
    simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
    rw [iteratedFDerivWithin_subset hsub huv hu (hf.of_le (by exact_mod_cast hk)) hz]
  have hpoly : taylorWithinEval f n (uIcc x y) x y = taylorWithinEval f n (Icc a b) x y := by
    simp only [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [hcoeff k (Finset.mem_range.mp hk).le left_mem_uIcc]
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange hxy hseg.of_succ
    ((hseg.differentiableOn_iteratedDerivWithin (by exact_mod_cast n.lt_succ_self) huv).mono
      uIoo_subset_uIcc_self)
  have hz' := uIoo_subset_uIcc_self hz
  rw [hpoly, hcoeff _ le_rfl hz', mul_div_right_comm] at he
  rw [he, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_right (hC (mem_image_of_mem _ (hsub hz')))
    (pow_nonneg (abs_nonneg _) _)

-- Subtract the two Taylor residuals before dividing by the positive step.
private theorem exists_centeredDifference_taylor_bound {f : ℝ → ℝ} {x r : ℝ} {n : ℕ}
    (hr : 0 < r) (hf : ContDiffOn ℝ (n + 1) f (Icc (x - r) (x + r))) :
    ∃ C ≥ 0, ∀ t, 0 < t → t ≤ r →
      |centeredDifference f x t -
        centeredDifference (taylorWithinEval f n (Icc (x - r) (x + r)) x) x t| ≤ C * t ^ n := by
  have hx : x ∈ Icc (x - r) (x + r) := ⟨by linarith, by linarith⟩
  let p := taylorWithinEval f n (Icc (x - r) (x + r)) x
  obtain ⟨C, hC, hT⟩ := exists_uniform_taylor_bound (by linarith) hx hf
  refine ⟨C, hC, ?_⟩
  intro t ht htr
  have hplus : |f (x + t) - p (x + t)| ≤ C * t ^ (n + 1) := by
    simpa only [add_sub_cancel_left, abs_of_pos ht] using
      hT (x + t) ⟨by linarith, by linarith⟩
  have hminus : |f (x - t) - p (x - t)| ≤ C * t ^ (n + 1) := by
    simpa only [sub_sub_cancel_left, abs_neg, abs_of_pos ht] using
      hT (x - t) ⟨by linarith, by linarith⟩
  have hden : 0 < 2 * t := by positivity
  rw [centeredDifference, centeredDifference, ← sub_div, abs_div, abs_of_pos hden,
    div_le_iff₀ hden]
  calc
    _ = |(f (x + t) - p (x + t)) - (f (x - t) - p (x - t))| := by
      congr 1
      ring
    _ ≤ |f (x + t) - p (x + t)| + |f (x - t) - p (x - t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f (x + t) - p (x + t))
        (-(f (x - t) - p (x - t)))
    _ ≤ C * t ^ (n + 1) + C * t ^ (n + 1) := add_le_add hplus hminus
    _ = _ := by rw [pow_succ]; ring

private theorem centeredDifference_taylor_four (f : ℝ → ℝ) (s : Set ℝ) (x t : ℝ)
    (ht : t ≠ 0) :
    centeredDifference (taylorWithinEval f 4 s x) x t =
      derivWithin f s x + (iteratedDerivWithin 3 f s x / 6) * t ^ 2 := by
  rw [centeredDifference, div_eq_iff (mul_ne_zero (by norm_num) ht)]
  norm_num [taylor_within_apply, Finset.sum_range_succ, Nat.factorial, smul_eq_mul]
  ring

private theorem centeredDifference_taylor_six (f : ℝ → ℝ) (s : Set ℝ) (x t : ℝ)
    (ht : t ≠ 0) :
    centeredDifference (taylorWithinEval f 6 s x) x t =
      derivWithin f s x + (iteratedDerivWithin 3 f s x / 6) * t ^ 2 +
        (iteratedDerivWithin 5 f s x / 120) * t ^ 4 := by
  rw [centeredDifference, div_eq_iff (mul_ne_zero (by norm_num) ht)]
  norm_num [taylor_within_apply, Finset.sum_range_succ, Nat.factorial, smul_eq_mul]
  ring

private theorem abs_extrapolation_le {r e₁ e₂ C h : ℝ} {n : ℕ} (hr : 1 < r)
    (h₁ : |e₁| ≤ C * h ^ n) (h₂ : |e₂| ≤ C * (2 * h) ^ n) :
    |(r * e₁ - e₂) / (r - 1)| ≤ ((r + 2 ^ n) * C / (r - 1)) * h ^ n := by
  have hr₀ : 0 ≤ r := by linarith
  have hden := sub_nonneg.mpr hr.le
  calc
    |(r * e₁ - e₂) / (r - 1)| = |r * e₁ - e₂| / (r - 1) := by rw [abs_div, abs_of_nonneg hden]
    _ ≤ (r * |e₁| + |e₂|) / (r - 1) := by
      apply div_le_div_of_nonneg_right _ hden
      simpa only [sub_eq_add_neg, abs_neg, abs_mul, abs_of_nonneg hr₀] using
        abs_add_le (r * e₁) (-e₂)
    _ ≤ (r * (C * h ^ n) + C * (2 * h) ^ n) / (r - 1) :=
      div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left h₁ hr₀) h₂) hden
    _ = _ := by rw [mul_pow]; ring

/-- Fourth-order error of the first Richardson extrapolation. If `h₀ > 0` and `f` is `C⁵` on
`[x - 2*h₀, x + 2*h₀]`, one constant `C ≥ 0` bounds
`|f'(x) - (4 D(h) - D(2h)) / 3|` by `C*h^4` for every `0 < h ≤ h₀`, where
`D(t) = (f (x + t) - f (x - t)) / (2 * t)`. The derivative at the interior point `x`
is the ordinary derivative. -/
theorem exists_abs_deriv_sub_richardsonDifference_le {f : ℝ → ℝ} {x h₀ : ℝ} (hh₀ : 0 < h₀)
    (hf : ContDiffOn ℝ 5 f (Icc (x - 2 * h₀) (x + 2 * h₀))) :
    ∃ C ≥ 0, ∀ h, 0 < h → h ≤ h₀ → |deriv f x - richardsonDifference f x h| ≤ C * h ^ 4 := by
  let s := Icc (x - 2 * h₀) (x + 2 * h₀)
  let a := iteratedDerivWithin 3 f s x / 6
  have hderiv : derivWithin f s x = deriv f x :=
    derivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨C, hC, hT⟩ := exists_centeredDifference_taylor_bound (n := 4) (by positivity) hf
  have hD (t : ℝ) (ht : 0 < t) (htr : t ≤ 2 * h₀) :
      |centeredDifference f x t - (deriv f x + a * t ^ 2)| ≤ C * t ^ 4 := by
    specialize hT t ht htr
    change |centeredDifference f x t - centeredDifference (taylorWithinEval f 4 s x) x t| ≤ _ at hT
    rwa [centeredDifference_taylor_four f s x t ht.ne', hderiv] at hT
  refine ⟨20 * C / 3, by positivity, fun h hh hh' ↦ ?_⟩
  rw [abs_sub_comm (deriv f x)]
  rw [show richardsonDifference f x h - deriv f x =
    (4 * (centeredDifference f x h - (deriv f x + a * h ^ 2)) -
      (centeredDifference f x (2 * h) - (deriv f x + a * (2 * h) ^ 2))) / (4 - 1) by
    unfold richardsonDifference
    ring]
  have hR := abs_extrapolation_le (r := 4) (by norm_num) (hD h hh (by linarith))
    (hD (2 * h) (by positivity) (by linarith))
  norm_num at hR ⊢
  exact hR

/-- Sixth-order error after repeating Richardson extrapolation. If `h₀ > 0` and `f` is `C⁷` on
`[x - 2*h₀, x + 2*h₀]`, one constant `C ≥ 0` bounds
`|f'(x) - (16 S(h) - S(2h)) / 15|` by `C*h^6` for every `0 < h ≤ h₀/2`, where
`S(t) = (4 D(t) - D(2t)) / 3` and `D(t) = (f (x + t) - f (x - t)) / (2 * t)`.
The derivative is the ordinary derivative at `x`, and the outermost samples `x ± 4*h`
are in the closed interval, including at `h = h₀/2`. -/
theorem exists_abs_deriv_sub_richardsonDifference_twice_le {f : ℝ → ℝ} {x h₀ : ℝ} (hh₀ : 0 < h₀)
    (hf : ContDiffOn ℝ 7 f (Icc (x - 2 * h₀) (x + 2 * h₀))) :
    ∃ C ≥ 0, ∀ h, 0 < h → h ≤ h₀ / 2 →
      |deriv f x - (16 * richardsonDifference f x h - richardsonDifference f x (2 * h)) / 15| ≤
        C * h ^ 6 := by
  let s := Icc (x - 2 * h₀) (x + 2 * h₀)
  let a := iteratedDerivWithin 3 f s x / 6
  let b := iteratedDerivWithin 5 f s x / 120
  have hderiv : derivWithin f s x = deriv f x :=
    derivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨C, hC, hT⟩ := exists_centeredDifference_taylor_bound (n := 6) (by positivity) hf
  have hD (t : ℝ) (ht : 0 < t) (htr : t ≤ 2 * h₀) :
      |centeredDifference f x t - (deriv f x + a * t ^ 2 + b * t ^ 4)| ≤ C * t ^ 6 := by
    specialize hT t ht htr
    change |centeredDifference f x t - centeredDifference (taylorWithinEval f 6 s x) x t| ≤ _ at hT
    rwa [centeredDifference_taylor_six f s x t ht.ne', hderiv] at hT
  let K := 68 * C / 3
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS (t : ℝ) (ht : 0 < t) (htr : t ≤ h₀) :
      |richardsonDifference f x t - (deriv f x - 4 * b * t ^ 4)| ≤ K * t ^ 6 := by
    rw [show richardsonDifference f x t - (deriv f x - 4 * b * t ^ 4) =
      (4 * (centeredDifference f x t - (deriv f x + a * t ^ 2 + b * t ^ 4)) -
        (centeredDifference f x (2 * t) - (deriv f x + a * (2 * t) ^ 2 + b * (2 * t) ^ 4))) /
        (4 - 1) by
      unfold richardsonDifference
      ring]
    have hR := abs_extrapolation_le (r := 4) (by norm_num) (hD t ht (by linarith))
      (hD (2 * t) (by positivity) (by linarith))
    norm_num [K] at hR ⊢
    exact hR
  refine ⟨80 * K / 15, by positivity, fun h hh hh' ↦ ?_⟩
  rw [abs_sub_comm (deriv f x)]
  rw [show (16 * richardsonDifference f x h - richardsonDifference f x (2 * h)) / 15 - deriv f x =
    (16 * (richardsonDifference f x h - (deriv f x - 4 * b * h ^ 4)) -
      (richardsonDifference f x (2 * h) - (deriv f x - 4 * b * (2 * h) ^ 4))) / (16 - 1) by ring]
  have hR := abs_extrapolation_le (r := 16) (by norm_num) (hS h hh (by linarith))
    (hS (2 * h) (by positivity) (by linarith))
  norm_num at hR ⊢
  exact hR

end MetaMathlibExt
