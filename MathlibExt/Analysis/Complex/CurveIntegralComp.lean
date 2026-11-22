/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Change of variables in a contour integral

For `φ` holomorphic on an open set `Ω` containing a path `γ` that is differentiable at almost every
time, `∫_{φ ∘ γ} f(w) dw = ∫_γ f(φ(z)) φ′(z) dz` (`Complex.curveIntegral_map'_eq_comp_mul_deriv`).
Almost-everywhere differentiability covers piecewise differentiable curves, which may have corners.
Contour integrals are Mathlib's `curveIntegral` of the 1-form `f z • ContinuousLinearMap.id ℂ ℂ`, as
in `WantedExt/Analysis/Complex/ContourIntegralWanted.lean`, and `φ ∘ γ` is `Path.map'`.

Mathlib's `curveIntegral` has reversal, concatenation, segments and linearity, but no change of
variables. The proof rewrites both sides as interval integrals and applies the chain rule at almost
every time.

Rubric-guided revision of v1 ComplexVariables target 9 (`complex_line_integral_substitution` in
`v1/Atlas/ComplexVariables/code/Lecture8.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 21–40). The archived statement used its own
`complexLineIntegral` and required the curve to be differentiable at every point, which excludes
curves with corners; both are fixed here. The archived formalization and its original
license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped unitInterval

namespace Complex

/-- **Change of variables in a complex line integral.**
Let `φ` be holomorphic on an open set `Ω` and let `γ` be a curve in `Ω`, differentiable at almost
every time (this covers piecewise differentiable curves, which may have corners). Then for every
`f : ℂ → ℂ`,
$$\int_{\varphi(\gamma)} f(w)\,dw = \int_\gamma f(\varphi(z))\,\varphi'(z)\,dz.$$
The image curve `φ(γ)` is the path `γ.map' _`, and the 1-form `f(w) dw` is
`f w • ContinuousLinearMap.id ℂ ℂ`. A region in the source is a connected open set; the formula
does not use connectedness. -/
public theorem curveIntegral_map'_eq_comp_mul_deriv {Ω : Set ℂ} {φ : ℂ → ℂ} {z₀ z₁ : ℂ}
    (f : ℂ → ℂ) (γ : Path z₀ z₁) (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω)
    (hγΩ : range γ ⊆ Ω) (hγ : ∀ᵐ t, t ∈ I → DifferentiableAt ℝ γ.extend t) :
    (∫ᶜ w in γ.map' (hφ.continuousOn.mono hγΩ), f w • ContinuousLinearMap.id ℂ ℂ) =
      ∫ᶜ z in γ, (f (φ z) * deriv φ z) • ContinuousLinearMap.id ℂ ℂ := by
  have hext : ⇑(γ.map' (hφ.continuousOn.mono hγΩ)).extend = φ ∘ γ.extend := rfl
  rw [curveIntegral_eq_intervalIntegral_deriv (E := ℂ) (F := ℂ),
    curveIntegral_eq_intervalIntegral_deriv (E := ℂ) (F := ℂ), hext]
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le zero_le_one]
  filter_upwards [hγ] with t hγt ht
  have hφt : DifferentiableAt ℂ φ (γ.extend t) :=
    hφ.differentiableAt (hΩ.mem_nhds (hγΩ (γ.extend_range.subset (mem_range_self t))))
  -- The chain rule at a time where `γ` is differentiable.
  have hchain : deriv (φ ∘ γ.extend) t = deriv φ (γ.extend t) * deriv γ.extend t :=
    (hφt.hasDerivAt.comp t (hγt (Ioc_subset_Icc_self ht)).hasDerivAt).deriv
  simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, hchain]
  ring

end Complex
