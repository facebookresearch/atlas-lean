/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.LandauKolmogorov

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the Landau–Kolmogorov inequality

Concrete checks: `sin` (main inequality and absolute form at `0`, where
`(sin' 0)² = 1`), `cos` (at `π / 2`, where `(cos' (π/2))² = 1`), a constant
function (the degenerate `M₂ = 0` branch), the zero function (the degenerate
`M₀ = 0` branch), the one-sided constant-`4` form, and the complex-valued
form (a constant function, and `x ↦ (sin x : ℂ)` at `0`).
-/

@[expose] public section

namespace MetaMathlibExt.LandauKolmogorovTests

open MetaMathlibExt

private theorem sin_bounds_M₀ : ∀ x : ℝ, |Real.sin x| ≤ 1 :=
  fun x => Real.abs_sin_le_one x

private theorem sin_bounds_M₂ : ∀ x : ℝ, |deriv (deriv Real.sin) x| ≤ 1 := by
  intro x
  have h1 : deriv Real.sin = Real.cos := Real.deriv_sin
  have h2 : deriv Real.cos x = -Real.sin x := (Real.hasDerivAt_cos x).deriv
  rw [h1]
  rw [h2]
  rw [abs_neg]
  exact Real.abs_sin_le_one x

private theorem cos_bounds_M₀ : ∀ x : ℝ, |Real.cos x| ≤ 1 :=
  fun x => Real.abs_cos_le_one x

private theorem cos_bounds_M₂ : ∀ x : ℝ, |deriv (deriv Real.cos) x| ≤ 1 := by
  intro x
  have h1 : deriv Real.cos = fun y => -Real.sin y := funext fun _ => Real.deriv_cos
  have h2 : deriv (fun y => -Real.sin y) x = -Real.cos x :=
    (Real.hasDerivAt_sin x).neg.deriv
  rw [h1, h2]
  rw [abs_neg]
  exact Real.abs_cos_le_one x

/-- `sin` at `0`: `(sin' 0)² = 1 ≤ 2 * 1 * 1`. -/
private theorem landau_sin_zero : (deriv Real.sin 0) ^ 2 ≤ 2 * (1 : ℝ) * 1 := by
  have h := landau_inequality Real.contDiff_sin sin_bounds_M₀ sin_bounds_M₂ (0 : ℝ)
  have hder : deriv Real.sin (0 : ℝ) = 1 := by rw [Real.deriv_sin]; simp
  rw [hder] at h
  norm_num at h ⊢

/-- Absolute form for `sin` at `0`: `|sin' 0| = 1 ≤ √2`. -/
private theorem landau_abs_sin_zero : |deriv Real.sin 0| ≤ Real.sqrt 2 := by
  have h := landau_inequality_abs Real.contDiff_sin sin_bounds_M₀ sin_bounds_M₂ (0 : ℝ)
  have hder : deriv Real.sin (0 : ℝ) = 1 := by rw [Real.deriv_sin]; simp
  rw [hder] at h
  have h2 : (2 : ℝ) * 1 * 1 = 2 := by norm_num
  rw [h2] at h
  simp

/-- `cos` at `π / 2`: `(cos' (π/2))² = 1 ≤ 2 * 1 * 1`. -/
private theorem landau_cos_pi_div_two :
    (deriv Real.cos (Real.pi / 2)) ^ 2 ≤ 2 * (1 : ℝ) * 1 := by
  have h := landau_inequality Real.contDiff_cos cos_bounds_M₀ cos_bounds_M₂ (Real.pi / 2)
  have hder : deriv Real.cos (Real.pi / 2) = -1 := by
    rw [Real.deriv_cos]
    simp [Real.sin_pi_div_two]
  rw [hder] at h
  norm_num at h ⊢

/-- Constant function: the `M₂ = 0` branch gives `0 ≤ 2 * 2 * 0`. -/
private theorem landau_const_two :
    (deriv (fun _ : ℝ => (2 : ℝ)) 3) ^ 2 ≤ 2 * (2 : ℝ) * 0 := by
  have hM₀ : ∀ x : ℝ, |(fun _ : ℝ => (2 : ℝ)) x| ≤ 2 := fun x => by simp
  have hM₂ : ∀ x : ℝ, |deriv (deriv (fun _ : ℝ => (2 : ℝ))) x| ≤ 0 := by
    intro x
    have h1 : deriv (fun _ : ℝ => (2 : ℝ)) = fun _ => 0 :=
      funext fun y => deriv_const y 2
    rw [h1, deriv_const]
    simp
  have h := landau_inequality contDiff_const hM₀ hM₂ (3 : ℝ)
  have hder : deriv (fun _ : ℝ => (2 : ℝ)) 3 = 0 := deriv_const 3 2
  rw [hder] at h
  simp

/-- Zero function: the `M₀ = 0` branch gives `0 ≤ 2 * 0 * 1`. -/
private theorem landau_zero_fun :
    (deriv (fun _ : ℝ => (0 : ℝ)) 3) ^ 2 ≤ 2 * (0 : ℝ) * 1 := by
  have hM₀ : ∀ x : ℝ, |(fun _ : ℝ => (0 : ℝ)) x| ≤ 0 := fun x => by simp
  have hM₂ : ∀ x : ℝ, |deriv (deriv (fun _ : ℝ => (0 : ℝ))) x| ≤ 1 := by
    intro x
    have h1 : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 :=
      funext fun y => deriv_const y 0
    rw [h1, deriv_const]
    simp
  have h := landau_inequality contDiff_const hM₀ hM₂ (3 : ℝ)
  have hder : deriv (fun _ : ℝ => (0 : ℝ)) 3 = 0 := deriv_const 3 0
  rw [hder] at h
  simp

/-- One-sided form for `sin` at `0`: `(sin' 0)² = 1 ≤ 4 * 1 * 1`. -/
private theorem landau_one_sided_sin_zero :
    (deriv Real.sin 0) ^ 2 ≤ 4 * (1 : ℝ) * 1 := by
  have h := landau_inequality_one_sided Real.contDiff_sin sin_bounds_M₀ sin_bounds_M₂ (0 : ℝ)
  have hder : deriv Real.sin (0 : ℝ) = 1 := by rw [Real.deriv_sin]; simp
  rw [hder] at h
  norm_num at h ⊢

/-- Complex constant function: `‖(1 : ℂ)'‖² = 0 ≤ 4 * 1 * 0`. -/
private theorem landau_complex_const_one :
    ‖deriv (fun _ : ℝ => (1 : ℂ)) 3‖ ^ 2 ≤ 4 * (1 : ℝ) * 0 := by
  have hM₀ : ∀ x : ℝ, ‖(fun _ : ℝ => (1 : ℂ)) x‖ ≤ 1 := fun x => by simp
  have hM₂ : ∀ x : ℝ, ‖deriv (deriv (fun _ : ℝ => (1 : ℂ))) x‖ ≤ 0 := by
    intro x
    have h1 : deriv (fun _ : ℝ => (1 : ℂ)) = fun _ => 0 :=
      funext fun y => deriv_const y 1
    rw [h1, deriv_const]
    simp
  have h := landau_inequality_complex contDiff_const hM₀ hM₂ (3 : ℝ)
  have hder : deriv (fun _ : ℝ => (1 : ℂ)) 3 = 0 := deriv_const 3 1
  rw [hder] at h
  simp

/-- Complex `x ↦ (sin x : ℂ)` at `0`: `‖f' 0‖² = 1 ≤ 4 * 1 * 1`. -/
private theorem landau_complex_sin_zero :
    ‖deriv (fun x : ℝ => (Real.sin x : ℂ)) 0‖ ^ 2 ≤ 4 * (1 : ℝ) * 1 := by
  have hfun : (fun x : ℝ => (Real.sin x : ℂ)) = Complex.ofRealCLM ∘ Real.sin :=
    funext fun x => (Complex.ofRealCLM_apply (Real.sin x)).symm
  have hcont : ContDiff ℝ 2 (fun x : ℝ => (Real.sin x : ℂ)) := by
    rw [hfun]
    exact Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
  have hM₀ : ∀ x : ℝ, ‖(fun y : ℝ => (Real.sin y : ℂ)) x‖ ≤ 1 := by
    intro x
    rw [Complex.norm_real]
    exact Real.abs_sin_le_one x
  have hderiv : deriv (fun x : ℝ => (Real.sin x : ℂ)) = fun x => (Real.cos x : ℂ) := by
    funext x
    have h := ((hasDerivAt_const x Complex.ofRealCLM).clm_apply
      (Real.hasDerivAt_sin x)).deriv
    have hfun₂ : (fun y : ℝ => Complex.ofRealCLM (Real.sin y)) =
        fun y => (Real.sin y : ℂ) :=
      funext fun y => Complex.ofRealCLM_apply (Real.sin y)
    rw [hfun₂] at h
    simpa [Complex.ofRealCLM_apply] using h
  have hM₂ : ∀ x : ℝ, ‖deriv (deriv (fun y : ℝ => (Real.sin y : ℂ))) x‖ ≤ 1 := by
    intro x
    rw [hderiv]
    have h2 : deriv (fun y : ℝ => (Real.cos y : ℂ)) x = (-Real.sin x : ℂ) := by
      have h := ((hasDerivAt_const x Complex.ofRealCLM).clm_apply
        (Real.hasDerivAt_cos x)).deriv
      have hfun₂ : (fun y : ℝ => Complex.ofRealCLM (Real.cos y)) =
          fun y => (Real.cos y : ℂ) :=
        funext fun y => Complex.ofRealCLM_apply (Real.cos y)
      rw [hfun₂] at h
      simpa [Complex.ofRealCLM_apply] using h
    rw [h2, norm_neg, Complex.norm_real]
    exact Real.abs_sin_le_one x
  have h := landau_inequality_complex hcont hM₀ hM₂ (0 : ℝ)
  have hder : deriv (fun x : ℝ => (Real.sin x : ℂ)) (0 : ℝ) = (1 : ℂ) := by
    rw [hderiv]
    simp
  rw [hder] at h
  rw [hder]
  exact h

end MetaMathlibExt.LandauKolmogorovTests
