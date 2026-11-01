/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The derivative at `1/2` of a function with a Gamma-factor functional equation

Many L-functions satisfy a functional equation of the shape
`A ^ s Γ(s) f(s) = A ^ (1 - s) Γ(1 - s) f(1 - s)` with `A > 0`. Since the completed function
`s ↦ A ^ s Γ(s) f(s)` is symmetric about `s = 1/2`, its derivative vanishes there, which
determines the logarithmic derivative of `f` at the centre:

`f'(1/2) = -f(1/2) (log A + ψ(1/2)) = f(1/2) (2 log 2 + γ - log A)`,

where `ψ = Γ'/Γ` is the digamma function and `γ` is the Euler–Mascheroni constant.

## Main statements

* `deriv_eq_zero_of_eventuallyEq_one_sub`: a function symmetric under `s ↦ 1 - s` near `1/2`
  has derivative `0` at `1/2`.
* `Complex.deriv_one_half_of_cpow_mul_Gamma_symm`: `f'(1/2) = -f(1/2) (log A + ψ(1/2))`.
* `Complex.deriv_one_half_of_cpow_mul_Gamma_symm'`: `f'(1/2) = f(1/2) (2 log 2 + γ - log A)`.
-/

@[expose] public section

open Filter

open scoped Topology

/-- A function that is symmetric under `s ↦ 1 - s` near `1/2` and differentiable at `1/2` has
derivative `0` there. -/
theorem deriv_eq_zero_of_eventuallyEq_one_sub {F : ℂ → ℂ} (hF : DifferentiableAt ℂ F (1 / 2))
    (hsymm : F =ᶠ[𝓝 (1 / 2)] fun s ↦ F (1 - s)) : deriv F (1 / 2) = 0 := by
  have h1h : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  have hF' : HasDerivAt F (deriv F (1 / 2)) (1 - 1 / 2) := by rw [h1h]; exact hF.hasDerivAt
  have hsub : HasDerivAt (fun s : ℂ ↦ 1 - s) (-1) (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_sub (1 : ℂ)
  have hG : HasDerivAt F (deriv F (1 / 2) * (-1)) (1 / 2) :=
    (hF'.comp (1 / 2 : ℂ) hsub).congr_of_eventuallyEq hsymm
  have := hF.hasDerivAt.unique hG
  linear_combination this / 2

namespace Complex

/-- **The derivative at the centre of a Gamma-factor functional equation.** Let `A > 0` and let
`f` be differentiable at `1/2` and satisfy `A ^ s Γ(s) f(s) = A ^ (1 - s) Γ(1 - s) f(1 - s)` for
`s` near `1/2`. Then `f'(1/2) = -f(1/2) (log A + ψ(1/2))`, where `ψ` is the digamma function. -/
theorem deriv_one_half_of_cpow_mul_Gamma_symm {A : ℝ} (hA : 0 < A) {f : ℂ → ℂ}
    (hf : DifferentiableAt ℂ f (1 / 2))
    (hfe : ∀ᶠ s in 𝓝 (1 / 2 : ℂ),
      (A : ℂ) ^ s * Gamma s * f s = (A : ℂ) ^ (1 - s) * Gamma (1 - s) * f (1 - s)) :
    deriv f (1 / 2) = -f (1 / 2) * (Real.log A + digamma (1 / 2)) := by
  set h : ℂ := 1 / 2
  have hhre : h.re = 1 / 2 := by simp [h]
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hG0 : Gamma h ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [hhre]; norm_num)
  have hGd : DifferentiableAt ℂ Gamma h := by
    apply differentiableAt_Gamma
    intro m hm
    have := congrArg re hm
    rw [hhre] at this
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set F : ℂ → ℂ := fun s ↦ (A : ℂ) ^ s * Gamma s * f s
  set D : ℂ := ((A : ℂ) ^ h * log A * 1) * Gamma h * f h +
      (A : ℂ) ^ h * deriv Gamma h * f h + (A : ℂ) ^ h * Gamma h * deriv f h
  have hFd : HasDerivAt F D h := by
    have h1 : HasDerivAt (fun s : ℂ ↦ (A : ℂ) ^ s) ((A : ℂ) ^ h * log A * 1) h :=
      (hasDerivAt_id h).const_cpow (Or.inl hA0)
    have hP := (h1.mul hGd.hasDerivAt).mul hf.hasDerivAt
    exact hP.congr_deriv (by simp only [D, Pi.mul_apply]; ring)
  have hD0 : D = 0 := by
    rw [← hFd.deriv]
    exact deriv_eq_zero_of_eventuallyEq_one_sub hFd.differentiableAt hfe
  have hAh : (A : ℂ) ^ h ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; tauto
  have key : (A : ℂ) ^ h * (Gamma h * deriv f h +
      f h * (log A * Gamma h + deriv Gamma h)) = 0 := by
    linear_combination hD0
  have key2 := (mul_eq_zero.mp key).resolve_left hAh
  rw [digamma_def, logDeriv_apply, ofReal_log hA.le]
  field_simp
  linear_combination key2

/-- **The derivative at the centre of a Gamma-factor functional equation**, explicit form. Under
the hypotheses of `Complex.deriv_one_half_of_cpow_mul_Gamma_symm`,
`f'(1/2) = f(1/2) (2 log 2 + γ - log A)`, where `γ` is the Euler–Mascheroni constant. -/
theorem deriv_one_half_of_cpow_mul_Gamma_symm' {A : ℝ} (hA : 0 < A) {f : ℂ → ℂ}
    (hf : DifferentiableAt ℂ f (1 / 2))
    (hfe : ∀ᶠ s in 𝓝 (1 / 2 : ℂ),
      (A : ℂ) ^ s * Gamma s * f s = (A : ℂ) ^ (1 - s) * Gamma (1 - s) * f (1 - s)) :
    deriv f (1 / 2) =
      f (1 / 2) * (2 * log 2 + Real.eulerMascheroniConstant - Real.log A) := by
  rw [deriv_one_half_of_cpow_mul_Gamma_symm hA hf hfe, digamma_one_half]
  ring

end Complex
