/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.AlexandrovGeometry.FourPointComparison
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Derivatives of model trigonometry

This file proves the differential equations for the model cosine `modelCos`
(`cs`) and model sine `modelSin` (`sn`).

## Main results
* `hasDerivAt_modelSin`: the derivative of `sn` is `cs`.
* `hasDerivAt_modelCos`: the derivative of `cs` is `-κ * sn`.

## References
* S. Alexander, V. Kapovitch, and A. Petrunin, Alexandrov geometry:
  foundations, AMS GSM 236, 2024; `model.tex` l.38-61, where `cs` and `sn`
  are the solutions of `y'' + κ y = 0` with `x(0) = 1`, `x'(0) = 0` and
  `y(0) = 0`, `y'(0) = 1` respectively.
-/

@[expose] public section

namespace AlexandrovGeometry

/-- Derivative of `modelSin` is `modelCos`. -/
theorem hasDerivAt_modelSin (κ t : ℝ) :
    HasDerivAt (modelSin κ) (modelCos κ t) t := by
  by_cases hpos : 0 < κ
  · have hsqrt_pos : (0 : ℝ) < √κ := Real.sqrt_pos.mpr hpos
    have hsqrt_ne : √κ ≠ 0 := ne_of_gt hsqrt_pos
    have h_inner : HasDerivAt (fun y : ℝ => √κ * y) √κ t :=
      hasDerivAt_const_mul √κ
    have h_outer :
        HasDerivAt (fun u : ℝ => Real.sin u / √κ)
          (Real.cos (√κ * t) / √κ) (√κ * t) :=
      (Real.hasDerivAt_sin _).div_const _
    have hcomp :
        HasDerivAt
          ((fun u : ℝ => Real.sin u / √κ) ∘ fun y : ℝ => √κ * y)
          (Real.cos (√κ * t) / √κ * √κ) t :=
      HasDerivAt.comp t h_outer h_inner
    have hfun_eq :
        ((fun u : ℝ => Real.sin u / √κ) ∘ fun y : ℝ => √κ * y) =
          modelSin κ := by
      funext y
      simp only [Function.comp_apply]
      simp only [modelSin_of_pos hpos]
    have hcos_eq : modelCos κ t = Real.cos (√κ * t) := by
      exact modelCos_of_pos hpos t
    have hdiv_self : √κ / √κ = 1 := by field_simp [hsqrt_ne]
    have hderiv_eq :
        Real.cos (√κ * t) / √κ * √κ = modelCos κ t := by
      rw [hcos_eq]
      calc Real.cos (√κ * t) / √κ * √κ =
          Real.cos (√κ * t) * (√κ / √κ) := by ring
        _ = Real.cos (√κ * t) * 1 := by rw [hdiv_self]
        _ = Real.cos (√κ * t) := by ring
    rw [hfun_eq, hderiv_eq] at hcomp
    exact hcomp
  · by_cases h0 : κ = 0
    · subst h0
      clear hpos
      have hsin_eq : modelSin (0 : ℝ) = fun y : ℝ => y := by
        funext y
        exact modelSin_zero_left y
      have hcos_val : modelCos (0 : ℝ) t = 1 := by
        exact modelCos_zero_left t
      rw [hsin_eq, hcos_val]
      exact hasDerivAt_id t
    · have hle : κ ≤ 0 := le_of_not_gt hpos
      have hlt : κ < 0 := lt_of_le_of_ne hle h0
      have hneg_pos : (0 : ℝ) < -κ := neg_pos.mpr hlt
      have hsqrt_pos : (0 : ℝ) < √(-κ) :=
        Real.sqrt_pos.mpr hneg_pos
      have hsqrt_ne : √(-κ) ≠ 0 := ne_of_gt hsqrt_pos
      have h_inner :
          HasDerivAt (fun y : ℝ => √(-κ) * y) √(-κ) t :=
        hasDerivAt_const_mul √(-κ)
      have h_outer :
          HasDerivAt (fun u : ℝ => Real.sinh u / √(-κ))
            (Real.cosh (√(-κ) * t) / √(-κ)) (√(-κ) * t) :=
        (Real.hasDerivAt_sinh _).div_const _
      have hcomp :
          HasDerivAt
            ((fun u : ℝ => Real.sinh u / √(-κ)) ∘
              fun y : ℝ => √(-κ) * y)
            (Real.cosh (√(-κ) * t) / √(-κ) * √(-κ)) t :=
        HasDerivAt.comp t h_outer h_inner
      have hfun_eq :
          ((fun u : ℝ => Real.sinh u / √(-κ)) ∘
            fun y : ℝ => √(-κ) * y) = modelSin κ := by
        funext y
        simp only [Function.comp_apply]
        simp only [modelSin_of_neg hlt]
      have hcos_eq : modelCos κ t = Real.cosh (√(-κ) * t) := by
        exact modelCos_of_neg hlt t
      have hdiv_self : √(-κ) / √(-κ) = 1 := by
        field_simp [hsqrt_ne]
      have hderiv_eq :
          Real.cosh (√(-κ) * t) / √(-κ) * √(-κ) =
            modelCos κ t := by
        rw [hcos_eq]
        calc Real.cosh (√(-κ) * t) / √(-κ) * √(-κ) =
            Real.cosh (√(-κ) * t) * (√(-κ) / √(-κ)) := by ring
          _ = Real.cosh (√(-κ) * t) * 1 := by rw [hdiv_self]
          _ = Real.cosh (√(-κ) * t) := by ring
      rw [hfun_eq, hderiv_eq] at hcomp
      exact hcomp

/-- Derivative of `modelCos` is `-κ * modelSin`. -/
theorem hasDerivAt_modelCos (κ t : ℝ) :
    HasDerivAt (modelCos κ) (-κ * modelSin κ t) t := by
  by_cases hpos : 0 < κ
  · have hsqrt_pos : (0 : ℝ) < √κ := Real.sqrt_pos.mpr hpos
    have hsqrt_ne : √κ ≠ 0 := ne_of_gt hsqrt_pos
    have hsqrt_sq : √κ * √κ = κ :=
      Real.mul_self_sqrt (le_of_lt hpos)
    have h_inner : HasDerivAt (fun y : ℝ => √κ * y) √κ t :=
      hasDerivAt_const_mul √κ
    have h_outer :
        HasDerivAt (fun u : ℝ => Real.cos u)
          (-Real.sin (√κ * t)) (√κ * t) :=
      Real.hasDerivAt_cos _
    have hcomp :
        HasDerivAt
          ((fun u : ℝ => Real.cos u) ∘ fun y : ℝ => √κ * y)
          (-Real.sin (√κ * t) * √κ) t :=
      HasDerivAt.comp t h_outer h_inner
    have hfun_eq :
        ((fun u : ℝ => Real.cos u) ∘ fun y : ℝ => √κ * y) =
          modelCos κ := by
      funext y
      simp only [Function.comp_apply]
      simp only [modelCos_of_pos hpos]
    have hsin_eq : modelSin κ t = Real.sin (√κ * t) / √κ := by
      exact modelSin_of_pos hpos t
    have hderiv_eq :
        -Real.sin (√κ * t) * √κ = -κ * modelSin κ t := by
      rw [hsin_eq, ← mul_div_assoc, eq_div_iff hsqrt_ne]
      have hring :
          (-Real.sin (√κ * t) * √κ) * √κ =
            -Real.sin (√κ * t) * (√κ * √κ) := by ring
      rw [hring, hsqrt_sq]
      ring
    rw [hfun_eq, hderiv_eq] at hcomp
    exact hcomp
  · by_cases h0 : κ = 0
    · subst h0
      clear hpos
      have hcos_eq : modelCos (0 : ℝ) = fun _ : ℝ => 1 := by
        funext y
        exact modelCos_zero_left y
      have hderiv_eq : (-(0 : ℝ)) * modelSin 0 t = 0 := by simp
      rw [hcos_eq, hderiv_eq]
      exact hasDerivAt_const t 1
    · have hle : κ ≤ 0 := le_of_not_gt hpos
      have hlt : κ < 0 := lt_of_le_of_ne hle h0
      have hneg_pos : (0 : ℝ) < -κ := neg_pos.mpr hlt
      have hsqrt_pos : (0 : ℝ) < √(-κ) :=
        Real.sqrt_pos.mpr hneg_pos
      have hsqrt_ne : √(-κ) ≠ 0 := ne_of_gt hsqrt_pos
      have hsqrt_sq : √(-κ) * √(-κ) = -κ :=
        Real.mul_self_sqrt (le_of_lt hneg_pos)
      have h_inner :
          HasDerivAt (fun y : ℝ => √(-κ) * y) √(-κ) t :=
        hasDerivAt_const_mul √(-κ)
      have h_outer :
          HasDerivAt (fun u : ℝ => Real.cosh u)
            (Real.sinh (√(-κ) * t)) (√(-κ) * t) :=
        Real.hasDerivAt_cosh _
      have hcomp :
          HasDerivAt
            ((fun u : ℝ => Real.cosh u) ∘ fun y : ℝ => √(-κ) * y)
            (Real.sinh (√(-κ) * t) * √(-κ)) t :=
        HasDerivAt.comp t h_outer h_inner
      have hfun_eq :
          ((fun u : ℝ => Real.cosh u) ∘ fun y : ℝ => √(-κ) * y) =
            modelCos κ := by
        funext y
        simp only [Function.comp_apply]
        simp only [modelCos_of_neg hlt]
      have hsin_eq :
          modelSin κ t = Real.sinh (√(-κ) * t) / √(-κ) := by
        exact modelSin_of_neg hlt t
      have hderiv_eq :
          Real.sinh (√(-κ) * t) * √(-κ) =
            -κ * modelSin κ t := by
        rw [hsin_eq, ← mul_div_assoc, eq_div_iff hsqrt_ne]
        have hring :
            (Real.sinh (√(-κ) * t) * √(-κ)) * √(-κ) =
              Real.sinh (√(-κ) * t) * (√(-κ) * √(-κ)) := by ring
        rw [hring, hsqrt_sq]
        ring
      rw [hfun_eq, hderiv_eq] at hcomp
      exact hcomp

end AlexandrovGeometry
