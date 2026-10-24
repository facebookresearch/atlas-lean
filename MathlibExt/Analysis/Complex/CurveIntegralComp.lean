/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Change of variables in a contour integral

For `φ` holomorphic on an open set `Ω` containing a path `γ` that is differentiable on `[0, 1]`,
`∫_{φ ∘ γ} f(w) dw = ∫_γ f(φ(z)) φ′(z) dz` (`Complex.curveIntegral_map'`). Contour integrals are
Mathlib's `curveIntegral` of the 1-form `f z • ContinuousLinearMap.id ℂ ℂ`, as in
`WantedExt/Analysis/Complex/ContourIntegralWanted.lean`, and `φ ∘ γ` is `Path.map'`.

Mathlib's `curveIntegral` has reversal, concatenation, segments and linearity, but no change of
variables.

Restatement on Mathlib's `curveIntegral` of `complex_line_integral_substitution` from
`v1/Atlas/ComplexVariables/code/Lecture8.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 21–40, which used the archived
`complexLineIntegral` (`∫ t in a..b, f (γ t) * deriv γ t`); the chain-rule argument is the same.
The archived formalization and its original license/provenance remain in `v1/` (the original
license text is `v1/LICENSE`). This records equivalence to the archived Lean statement, not
verification against the printed textbook.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace Complex

/-- **Change of variables in a contour integral.** If `φ` is holomorphic on an open set containing
the path `γ`, and `γ` is differentiable on `[0, 1]`, then
`∫_{φ ∘ γ} f(w) dw = ∫_γ f(φ(z)) φ′(z) dz`. -/
public theorem curveIntegral_map' {f φ : ℂ → ℂ} {a b : ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ Ω) (γ : Path a b) (hγΩ : range γ ⊆ Ω)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableWithinAt ℝ γ.extend (Icc 0 1) t) :
    (∫ᶜ w in γ.map' (hφ.continuousOn.mono hγΩ), f w • ContinuousLinearMap.id ℂ ℂ) =
      ∫ᶜ z in γ, (f (φ z) * deriv φ z) • ContinuousLinearMap.id ℂ ℂ := by
  have hext : (γ.map' (hφ.continuousOn.mono hγΩ)).extend = φ ∘ γ.extend := by
    funext t
    rfl
  rw [curveIntegral_def, curveIntegral_def]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [curveIntegralFun_def, hext, Function.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  have hmem : γ.extend t ∈ Ω := hγΩ (by rw [Path.extend_apply γ ht]; exact mem_range_self _)
  have hd := ((hφ.differentiableAt (hΩ.mem_nhds hmem)).hasDerivAt.comp_hasDerivWithinAt t
    (hγ t ht).hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc zero_lt_one t ht)
  rw [hd]
  ring

end Complex

