/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.Path

@[expose] public section

namespace MathlibExt.Analysis.Complex.ContourIntegralWanted

/-!
The contour integral `∫_γ f(z) dz` of `f : ℂ → ℂ` along a path `γ` is written as Mathlib's
curve integral of the complex-linear 1-form `z ↦ f z • id`.
-/

/--
Fundamental theorem of contour integration: if `γ` is `C¹` and `F` has complex
derivative `f` on an open neighborhood of the path, then the contour integral
of `f` along `γ` is `F b - F a`.

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "contour integrals of continuous functions in ℂ";
L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §1.1 to §1.3 (line integrals).
-/
theorem_wanted contourIntegral_of_hasDerivAt
    {F f : ℂ → ℂ} {a b : ℂ} {γ : Path a b} {U : Set ℂ}
    (hU : IsOpen U) (hγU : Set.range γ ⊆ U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1))
    (h_int : CurveIntegrable (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ = F b - F a

/--
ML estimate for contour integrals: if `γ` is `C¹`, `‖f‖ ≤ M` on the path and `‖γ'‖ ≤ L` on the
parameter interval `[0, 1]`, then `‖∫_γ f‖ ≤ M * L` (the parameter interval has length one, so
`L` bounds the length of `γ`).

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "contour integrals of continuous functions in ℂ";
L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §1.1 to §1.3 (line integrals).
-/
theorem_wanted norm_contourIntegral_le
    {f : ℂ → ℂ} {a b : ℂ} {γ : Path a b} {M L : ℝ}
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1))
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f (γ.extend t)‖ ≤ M)
    (hγ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖derivWithin γ.extend (Set.Icc 0 1) t‖ ≤ L)
    (h_int : CurveIntegrable (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ) :
    ‖curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ‖ ≤ M * L

end MathlibExt.Analysis.Complex.ContourIntegralWanted
