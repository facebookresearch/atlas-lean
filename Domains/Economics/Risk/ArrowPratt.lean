/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

@[expose] public section

/-!
# Arrow–Pratt risk aversion of CARA and CRRA utility

The Arrow–Pratt coefficient of absolute risk aversion of a Bernoulli utility `u` is
`A(x) = -u''(x) / u'(x)` and the coefficient of relative risk aversion is `R(x) = x A(x)`
(computed with `deriv`). Exponential (CARA) utility `-exp(-a x)` has constant absolute risk
aversion `a` at every wealth level for `a > 0` (the increasing, strictly concave case), and
isoelastic (CRRA) utility `x^(1-γ) / (1-γ)` (`log x` when `γ = 1`) has constant relative risk
aversion `γ` at every positive wealth level.

## Main results

* `absoluteRiskAversion_caraUtility`: CARA utility with `a > 0` has absolute risk aversion `a`.
* `relativeRiskAversion_crraUtility`: CRRA utility has relative risk aversion `γ` on `x > 0`.

## References

* J. W. Pratt, "Risk aversion in the small and in the large", Econometrica 32 (1964), 122--136.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), Section 6.C (Arrow–Pratt coefficients).
-/

namespace MathlibExt.Economics.Risk

open Real

/-- Arrow–Pratt coefficient of absolute risk aversion `A(x) = -u''(x) / u'(x)`. -/
noncomputable def absoluteRiskAversion (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv u) x / deriv u x

/-- Arrow–Pratt coefficient of relative risk aversion `R(x) = -x u''(x) / u'(x) = x A(x)`. -/
noncomputable def relativeRiskAversion (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * absoluteRiskAversion u x

/-- Constant absolute risk aversion (CARA, exponential) utility `u(x) = -exp(-a x)`. -/
noncomputable def caraUtility (a : ℝ) (x : ℝ) : ℝ :=
  -exp (-(a * x))

/-- Constant relative risk aversion (CRRA, isoelastic) utility on wealth `x > 0`:
`u(x) = x^(1-γ) / (1-γ)` for `γ ≠ 1` and `u(x) = log x` for `γ = 1`. -/
noncomputable def crraUtility (γ : ℝ) (x : ℝ) : ℝ :=
  if γ = 1 then log x else x ^ (1 - γ) / (1 - γ)

/-- CARA utility with `a > 0` (increasing and strictly concave) has constant absolute risk
aversion `a` at every wealth level. -/
theorem absoluteRiskAversion_caraUtility {a : ℝ} (ha : 0 < a) (x : ℝ) :
    absoluteRiskAversion (caraUtility a) x = a := by
  have hlin : ∀ y : ℝ, HasDerivAt (fun y : ℝ => a * y) a y := by
    intro y
    have h := (hasDerivAt_id' y).const_mul a
    rwa [mul_one] at h
  have h1 : ∀ y : ℝ, HasDerivAt (caraUtility a) (a * exp (-(a * y))) y := by
    intro y
    have h := (hlin y).neg.exp.neg
    have hval : a * exp (-(a * y)) = -(exp (-(a * y)) * -a) := by ring
    rw [hval]
    exact h
  have hderiv : deriv (caraUtility a) = fun y => a * exp (-(a * y)) := by
    funext y
    exact (h1 y).deriv
  have h2 : HasDerivAt (fun y : ℝ => a * exp (-(a * y)))
      (-(a ^ 2) * exp (-(a * x))) x := by
    have h := ((hlin x).neg.exp).const_mul a
    have hval : -(a ^ 2) * exp (-(a * x)) = a * (exp (-(a * x)) * -a) := by ring
    rw [hval]
    exact h
  have hDx : deriv (caraUtility a) x = a * exp (-(a * x)) := (h1 x).deriv
  have hD2x : deriv (deriv (caraUtility a)) x = -(a ^ 2) * exp (-(a * x)) := by
    rw [hderiv]
    exact h2.deriv
  unfold absoluteRiskAversion
  rw [hD2x, hDx]
  by_cases ha : a = 0
  · subst ha
    simp
  · have hE : exp (-(a * x)) ≠ 0 := ne_of_gt (exp_pos _)
    have hmul : a * exp (-(a * x)) ≠ 0 := mul_ne_zero ha hE
    field_simp

/-- CRRA utility has constant relative risk aversion `γ` at every positive wealth level. -/
theorem relativeRiskAversion_crraUtility (γ : ℝ) {x : ℝ} (hx : 0 < x) :
    relativeRiskAversion (crraUtility γ) x = γ := by
  unfold relativeRiskAversion absoluteRiskAversion
  by_cases hγ : γ = 1
  · subst hγ
    have hlog : crraUtility 1 = Real.log := by
      funext y
      simp [crraUtility]
    rw [hlog]
    have hD1 : ∀ y : ℝ, 0 < y → deriv Real.log y = y⁻¹ := by
      intro y hy
      exact (Real.hasDerivAt_log (ne_of_gt hy)).deriv
    have hD1x : deriv Real.log x = x⁻¹ := hD1 x hx
    have heq : deriv Real.log =ᶠ[nhds x] fun y => y⁻¹ := by
      have hmem : Set.Ioi (0:ℝ) ∈ nhds x := Ioi_mem_nhds hx
      filter_upwards [hmem] with y hy
      exact hD1 y (Set.mem_Ioi.mp hy)
    have hD2x : deriv (deriv Real.log) x = -((x ^ 2)⁻¹) := by
      rw [heq.deriv_eq]
      exact (hasDerivAt_inv (ne_of_gt hx)).deriv
    rw [hD1x, hD2x, neg_neg]
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hi0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
    have hcancel : (x ^ 2)⁻¹ / x⁻¹ = x⁻¹ := by
      rw [← inv_pow, pow_two]
      exact mul_div_cancel_right₀ _ hi0
    rw [hcancel, mul_inv_cancel₀ hx0]
  · have h1γ : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
    have hcrra : crraUtility γ = fun y : ℝ => y ^ (1 - γ) / (1 - γ) := by
      funext y
      simp [crraUtility, hγ]
    rw [hcrra]
    have hD1 : ∀ y : ℝ, 0 < y →
        deriv (fun y : ℝ => y ^ (1 - γ) / (1 - γ)) y = y ^ (-γ) := by
      intro y hy
      have hpow : HasDerivAt (fun y : ℝ => y ^ (1 - γ))
          ((1 - γ) * y ^ ((1 - γ) - 1)) y :=
        Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hy))
      have hdiv := hpow.div_const (1 - γ)
      have hval : ((1 - γ) * y ^ ((1 - γ) - 1)) / (1 - γ) = y ^ (-γ) := by
        have hpow2 : (1 - γ : ℝ) - 1 = -γ := by ring
        rw [hpow2]
        exact mul_div_cancel_left₀ _ h1γ
      have hder := hdiv.deriv
      rwa [hval] at hder
    have hD1x : deriv (fun y : ℝ => y ^ (1 - γ) / (1 - γ)) x = x ^ (-γ) :=
      hD1 x hx
    have heq : deriv (fun y : ℝ => y ^ (1 - γ) / (1 - γ)) =ᶠ[nhds x]
        fun y => y ^ (-γ) := by
      have hmem : Set.Ioi (0:ℝ) ∈ nhds x := Ioi_mem_nhds hx
      filter_upwards [hmem] with y hy
      exact hD1 y (Set.mem_Ioi.mp hy)
    have hD2x : deriv (deriv (fun y : ℝ => y ^ (1 - γ) / (1 - γ))) x
        = -γ * x ^ ((-γ) - 1) := by
      rw [heq.deriv_eq]
      exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).deriv
    rw [hD1x, hD2x]
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hE : x ^ (-γ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
    have hsplit : x ^ ((-γ) - 1 : ℝ) = x ^ (-γ) * x ^ (-1 : ℝ) := by
      have harg : ((-γ) - 1 : ℝ) = (-γ) + (-1) := by ring
      rw [harg, Real.rpow_add hx]
    have hrw : x ^ (-1 : ℝ) = x⁻¹ := Real.rpow_neg_one x
    rw [hsplit, hrw]
    have hcancel : -(-γ * (x ^ (-γ) * x⁻¹)) / x ^ (-γ) = γ * x⁻¹ := by
      have hring : -(-γ * (x ^ (-γ) * x⁻¹)) = γ * x⁻¹ * x ^ (-γ) := by ring
      rw [hring]
      exact mul_div_cancel_right₀ _ hE
    rw [hcancel]
    calc x * (γ * x⁻¹) = γ * (x * x⁻¹) := by ring
      _ = γ * 1 := by rw [mul_inv_cancel₀ hx0]
      _ = γ := mul_one γ

end MathlibExt.Economics.Risk
