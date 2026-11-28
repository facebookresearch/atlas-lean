/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.FunctionalEquation

/-!
# Tests for the derivative at the centre of a Gamma-factor functional equation

The hypotheses are met by `f = 1 / Γ` with `A = 1`, for which `A ^ s Γ(s) f(s) = 1` is symmetric.
-/

@[expose] public section

open Complex Filter Topology

/-- `s (1 - s)` is symmetric about `1 / 2`, so its derivative there is `0`. -/
example : deriv (fun s : ℂ => s * (1 - s)) (1 / 2) = 0 :=
  deriv_eq_zero_of_eventuallyEq_one_sub (by fun_prop)
    (Eventually.of_forall fun s => by ring)

/-- Near `1 / 2`, both `s` and `1 - s` lie in the right half-plane. -/
private lemma eventually_re_pos :
    ∀ᶠ s in 𝓝 (1 / 2 : ℂ), 0 < s.re ∧ 0 < (1 - s).re := by
  have h1 : ∀ᶠ s in 𝓝 (1 / 2 : ℂ), 0 < s.re :=
    (continuous_re.tendsto _).eventually (lt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ s in 𝓝 (1 / 2 : ℂ), 0 < (1 - s).re :=
    ((continuous_re.comp (continuous_const.sub continuous_id)).tendsto _).eventually
      (lt_mem_nhds (by norm_num))
  exact h1.and h2

private lemma hfe_inv_Gamma : ∀ᶠ s in 𝓝 (1 / 2 : ℂ),
    ((1 : ℝ) : ℂ) ^ s * Gamma s * (Gamma s)⁻¹ =
      ((1 : ℝ) : ℂ) ^ (1 - s) * Gamma (1 - s) * (Gamma (1 - s))⁻¹ := by
  filter_upwards [eventually_re_pos] with s hs
  rw [ofReal_one, one_cpow, one_cpow, one_mul, one_mul, mul_inv_cancel₀
    (Gamma_ne_zero_of_re_pos hs.1), mul_inv_cancel₀ (Gamma_ne_zero_of_re_pos hs.2)]

/-- **Instantiation at `f = 1 / Γ`, `A = 1`.** -/
example : deriv (fun s => (Gamma s)⁻¹) (1 / 2) =
    -(Gamma (1 / 2))⁻¹ * (Real.log 1 + digamma (1 / 2)) :=
  deriv_one_half_of_cpow_mul_Gamma_symm one_pos (differentiable_one_div_Gamma _) hfe_inv_Gamma

/-- The explicit form at `f = 1 / Γ`, `A = 1`: `(1/Γ)'(1/2) = (2 log 2 + γ) / √π`. -/
example : deriv (fun s => (Gamma s)⁻¹) (1 / 2) =
    (Gamma (1 / 2))⁻¹ * (2 * Complex.log 2 + Real.eulerMascheroniConstant - Real.log 1) :=
  deriv_one_half_of_cpow_mul_Gamma_symm' one_pos (differentiable_one_div_Gamma _) hfe_inv_Gamma

/-- The zero function satisfies every such functional equation. -/
example (A : ℝ) (hA : 0 < A) : deriv (fun _ : ℂ => (0 : ℂ)) (1 / 2) =
    -(0 : ℂ) * (Real.log A + digamma (1 / 2)) :=
  deriv_one_half_of_cpow_mul_Gamma_symm hA (differentiableAt_const _)
    (Eventually.of_forall fun s => by simp)
