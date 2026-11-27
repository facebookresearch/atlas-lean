/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.GradientDescent
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Mul

namespace MetaMathlibExt

-- For the half-squared norm, the bound at Lipschitz constant `1` is attained.
example (x : ℝ) :
    ‖gradient (fun y : ℝ => (2 : ℝ)⁻¹ * y ^ 2) x‖ ^ 2 =
      2 * 1 * ((2 : ℝ)⁻¹ * x ^ 2 - 0) := by
  let f : ℝ → ℝ := fun y => (2 : ℝ)⁻¹ * y ^ 2
  change ‖gradient f x‖ ^ 2 = 2 * 1 * (f x - 0)
  have hdiff : Differentiable ℝ f := by
    intro y
    simp [f]
  have hgradient (y : ℝ) : gradient f y = y := by
    rw [gradient_eq_deriv']
    simp [f]
  have hsmooth : LipschitzWith (1 : NNReal) (gradient f) := by
    rw [show gradient f = id by ext y; exact hgradient y]
    exact LipschitzWith.id
  apply le_antisymm
  · exact gradientDescent_norm_gradient_sq_le (L := 1) (by norm_num) hdiff hsmooth
      (fun y => by dsimp [f]; positivity) x
  · rw [hgradient, Real.norm_eq_abs, sq_abs]
    dsimp [f]
    ring_nf
    exact le_rfl

-- At `L = 0` the bound forces a zero gradient, even with a strictly lower bound.
example {f : ℝ → ℝ} (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith 0 (gradient f)) (hLower : ∀ y, 0 < f y) (x : ℝ) :
    gradient f x = 0 := by
  have hsq : ‖gradient f x‖ ^ 2 ≤ 0 := by
    simpa using gradientDescent_norm_gradient_sq_le (L := 0) (by norm_num)
      hdiff hsmooth (fun y => (hLower y).le) x
  by_contra hne
  exact (not_lt_of_ge hsq) (pow_pos (norm_pos_iff.mpr hne) 2)

-- The quadratic objective with a half step satisfies the first-iterate rate.
example (x₀ : ℝ) : (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹ * x₀) ^ 2 ≤ ‖x₀‖ ^ 2 := by
  let f : ℝ → ℝ := fun x => (2 : ℝ)⁻¹ * x ^ 2
  let X : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * x₀
  have hconvex : ConvexOn ℝ Set.univ f := by
    have hsquare : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
      (show Even 2 by norm_num).convexOn_pow
    simpa [f, smul_eq_mul] using hsquare.smul (c := (1 / 2 : ℝ)) (by norm_num)
  have hdiff : Differentiable ℝ f := by
    intro x
    simp [f]
  have hgradient (x : ℝ) : gradient f x = x := by
    rw [gradient_eq_deriv']
    simp [f]
  have hsmooth : LipschitzWith (1 : NNReal) (gradient f) := by
    rw [show gradient f = id by ext x; exact hgradient x]
    exact LipschitzWith.id
  have hX : ∀ k, X (k + 1) = X k - (1 / 2 : ℝ) • gradient f (X k) := by
    intro k
    rw [hgradient]
    simp only [X, pow_succ, smul_eq_mul]
    ring
  have hrate := gradient_descent_convex_sublinear_rate
    (E := ℝ) (f := f) (L := 1) (by norm_num) hconvex hdiff hsmooth
    (xstar := 0) (by
      intro x
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, f]
      positivity) (η := 1 / 2) (by norm_num)
    (X := X) hX 1 (by norm_num)
  simpa [f, X] using hrate

-- The same quadratic objective with two half steps satisfies the second-iterate rate.
example (x₀ : ℝ) :
    (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹ ^ 2 * x₀) ^ 2 ≤ ‖x₀‖ ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => (2 : ℝ)⁻¹ * x ^ 2
  let X : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * x₀
  have hconvex : ConvexOn ℝ Set.univ f := by
    have hsquare : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
      (show Even 2 by norm_num).convexOn_pow
    simpa [f, smul_eq_mul] using hsquare.smul (c := (1 / 2 : ℝ)) (by norm_num)
  have hdiff : Differentiable ℝ f := by
    intro x
    simp [f]
  have hgradient (x : ℝ) : gradient f x = x := by
    rw [gradient_eq_deriv']
    simp [f]
  have hsmooth : LipschitzWith (1 : NNReal) (gradient f) := by
    rw [show gradient f = id by ext x; exact hgradient x]
    exact LipschitzWith.id
  have hX : ∀ k, X (k + 1) = X k - (1 / 2 : ℝ) • gradient f (X k) := by
    intro k
    rw [hgradient]
    simp only [X, pow_succ, smul_eq_mul]
    ring
  have hrate := gradient_descent_convex_sublinear_rate
    (E := ℝ) (f := f) (L := 1) (by norm_num) hconvex hdiff hsmooth
    (xstar := 0) (by
      intro x
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, f]
      positivity) (η := 1 / 2) (by norm_num)
    (X := X) hX 2 (by norm_num)
  simpa [f, X] using hrate

end MetaMathlibExt
