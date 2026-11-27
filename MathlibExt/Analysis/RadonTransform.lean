/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/RadonTransform.lean` (leanprover/lean-eval), problem
`radon_transform_inversion`, at commit 38361be884302c7edce1908c4aef8296eb2cb27e
(manifest `manifests/problems/radon_transform_inversion.toml`, rev 1, submitter Kim Morrison):
the definitions `radon`, `fourier1`, and `fourier2` and the statement of
`radon_can_be_diagonalized_and_pseudo_inverted`, with their docstrings from
`WantedExt/Analysis/RadonTransformWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). The theorem was converted to
`theorem_wanted` and then proved. The declarations were put in the
`MathlibExt.Analysis.RadonTransformWanted` namespace and moved from
`WantedExt/Analysis/RadonTransformWanted.lean` to this module with their names, statements,
and current docstrings preserved. The LeanEval and Batteries imports and the umbrella Mathlib
import were replaced with specific Mathlib imports.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.Ring

/-!
# Fourier slice theorem for the planar Radon transform

The Fourier transform in the signed distance variable of the planar Radon transform equals
the restriction of the two-dimensional Fourier transform to the line in the normal direction.
The slice identity gives injectivity of the Radon transform on Schwartz functions and hence
the existence of a left inverse in `radon_can_be_diagonalized_and_pseudo_inverted`.
-/

@[expose] public section

namespace MathlibExt.Analysis.RadonTransformWanted.Analysis.RadonTransform

open MeasureTheory Real Complex

set_option linter.dupNamespace false in
/-- **Radon transform on the plane.** For $f : \mathbb{R}^2 \to \mathbb{C}$ and
$p, \theta \in \mathbb{R}$, the Radon transform of $f$ at $(p, \theta)$ is the integral of $f$
along the line $x \cos\theta + y \sin\theta = p$ with respect to arc length,

$$Rf(p, \theta) = \int_{\mathbb{R}} f(p\cos\theta - t\sin\theta, p\sin\theta + t\cos\theta)\,dt,$$

where the integral is taken to be $0$ when the integrand is not integrable. -/
noncomputable def radon (f : ℝ × ℝ → ℂ) (pθ : ℝ × ℝ) : ℂ :=
  ∫ t : ℝ, f (pθ.1 * Real.cos pθ.2 - t * Real.sin pθ.2,
              pθ.1 * Real.sin pθ.2 + t * Real.cos pθ.2)

set_option linter.dupNamespace false in
/-- **One-dimensional Fourier transform.** For $g : \mathbb{R} \to \mathbb{C}$ and
$k \in \mathbb{R}$, the Fourier transform of $g$ at $k$ is

$$\hat g(k) = \int_{\mathbb{R}} e^{-2\pi i p k} \, g(p) \, dp,$$

where the integral is taken to be $0$ when the integrand is not integrable. -/
noncomputable def fourier1 (g : ℝ → ℂ) (k : ℝ) : ℂ :=
  ∫ p : ℝ, Complex.exp (-(2 * Real.pi * p * k) * Complex.I) * g p

set_option linter.dupNamespace false in
/-- **Two-dimensional Fourier transform.** For $f : \mathbb{R}^2 \to \mathbb{C}$ and
$k = (k_1, k_2) \in \mathbb{R}^2$, the Fourier transform of $f$ at $k$ is

$$\hat f(k) = \int_{\mathbb{R}^2} e^{-2\pi i (x_1 k_1 + x_2 k_2)} \, f(x) \, dx,$$

where $dx$ is Lebesgue measure on $\mathbb{R}^2$ and the integral is taken to be $0$ when the
integrand is not integrable. -/
noncomputable def fourier2 (f : ℝ × ℝ → ℂ) (k : ℝ × ℝ) : ℂ :=
  ∫ x : ℝ × ℝ,
    Complex.exp (-(2 * Real.pi * (x.1 * k.1 + x.2 * k.2)) * Complex.I) * f x

open scoped FourierTransform

private noncomputable def rotateProd (θ : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  measurableEquivRealProd.symm.trans
    ((rotation (Circle.exp θ)).toHomeomorph.toMeasurableEquiv.trans measurableEquivRealProd)

private theorem rotateProd_apply (θ : ℝ) (x : ℝ × ℝ) :
    rotateProd θ x =
      (x.1 * Real.cos θ - x.2 * Real.sin θ, x.1 * Real.sin θ + x.2 * Real.cos θ) := by
  have hre : (Circle.exp θ : ℂ).re = Real.cos θ := by
    simp [Complex.exp_mul_I, Complex.cos_ofReal_re]
  have him : (Circle.exp θ : ℂ).im = Real.sin θ := by
    simp [Complex.exp_mul_I, Complex.sin_ofReal_re]
  change measurableEquivRealProd (rotation (Circle.exp θ)
    (measurableEquivRealProd.symm x)) = _
  simp only [rotation_apply, measurableEquivRealProd_apply, measurableEquivRealProd_symm_apply,
    Complex.mul_re, Complex.mul_im, hre, him]
  congr 1 <;> ring

private theorem measurePreserving_rotateProd (θ : ℝ) : MeasurePreserving (rotateProd θ) :=
  volume_preserving_equiv_real_prod.comp
    ((rotation (Circle.exp θ)).measurePreserving.comp volume_preserving_equiv_real_prod.symm)

private theorem fourier_slice (φ : SchwartzMap (ℝ × ℝ) ℂ) (θ k : ℝ) :
    fourier1 (fun p => radon (φ : ℝ × ℝ → ℂ) (p, θ)) k =
      fourier2 (φ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ) := by
  let phase : ℝ → ℂ := fun p => Complex.exp (↑(-(2 * Real.pi * p * k)) * Complex.I)
  let F : ℝ × ℝ → ℂ := fun x => phase x.1 * φ (rotateProd θ x)
  let v : ℝ × ℝ := (k * Real.cos θ, k * Real.sin θ)
  let G : ℝ × ℝ → ℂ := fun x =>
    Complex.exp (-(2 * Real.pi * (x.1 * v.1 + x.2 * v.2)) * Complex.I) * φ x
  have hφ : Integrable (fun x => φ (rotateProd θ x)) := by
    apply ((measurePreserving_rotateProd θ).integrable_comp_emb
      (rotateProd θ).measurableEmbedding).2
    let ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ equivRealProdCLM φ
    exact (volume_preserving_equiv_real_prod.integrable_comp_emb
      measurableEquivRealProd.measurableEmbedding).1 ψ.integrable
  have hF : Integrable F :=
    hφ.bdd_mul (c := 1) ((show Continuous (fun x : ℝ × ℝ => phase x.1) by
      dsimp [phase]
      fun_prop).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
  calc
    _ = ∫ p : ℝ, ∫ t : ℝ, F (p, t) := by
      simp only [fourier1, radon, F, rotateProd_apply, integral_const_mul, phase,
        ofReal_neg, ofReal_mul, ofReal_ofNat]
    _ = ∫ x : ℝ × ℝ, F x := (integral_prod F hF).symm
    _ = ∫ x : ℝ × ℝ, G (rotateProd θ x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have h : (rotateProd θ x).1 * v.1 + (rotateProd θ x).2 * v.2 = x.1 * k := by
        rw [rotateProd_apply]
        calc
          _ = x.1 * k * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
          _ = x.1 * k := by rw [Real.sin_sq_add_cos_sq, mul_one]
      have h' := congrArg Complex.ofReal h
      push_cast at h'
      simp only [F, G, phase, h', ofReal_neg, ofReal_mul, ofReal_ofNat, mul_assoc]
    _ = fourier2 φ (k * Real.cos θ, k * Real.sin θ) :=
      (measurePreserving_rotateProd θ).integral_comp' G

private theorem fourier2_eq_fourier (f : ℝ × ℝ → ℂ) (z : ℂ) :
    fourier2 f (measurableEquivRealProd z) = 𝓕 (f ∘ measurableEquivRealProd) z := by
  rw [fourier2, Real.fourier_eq', ← volume_preserving_equiv_real_prod.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    measurableEquivRealProd_apply, Function.comp_apply, smul_eq_mul, ofReal_mul,
    ofReal_sub, ofReal_neg, ofReal_ofNat]
  congr 3
  ring

private theorem fourier2_injective :
    Function.Injective (fun φ : SchwartzMap (ℝ × ℝ) ℂ => fourier2 φ) := by
  intro φ ψ h
  let e (f : SchwartzMap (ℝ × ℝ) ℂ) : SchwartzMap ℂ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ equivRealProdCLM f
  have hFourier : 𝓕 (e φ) = 𝓕 (e ψ) := by
    apply SchwartzMap.ext
    intro z
    simp only [SchwartzMap.fourier_coe]
    change 𝓕 ((φ : ℝ × ℝ → ℂ) ∘ measurableEquivRealProd) z =
      𝓕 ((ψ : ℝ × ℝ → ℂ) ∘ measurableEquivRealProd) z
    simpa only [← fourier2_eq_fourier] using congrFun h (measurableEquivRealProd z)
  have he : e φ = e ψ := (FourierTransform.fourierEquiv ℂ (SchwartzMap ℂ ℂ)).injective hFourier
  apply SchwartzMap.ext
  intro x
  exact DFunLike.congr_fun he (measurableEquivRealProd.symm x)

set_option linter.dupNamespace false in
/-- **Fourier slice theorem and injectivity of the Radon transform on Schwartz functions.**
Write $R$ for the Radon transform, $\hat g$ for the one-dimensional Fourier transform of
$g : \mathbb{R} \to \mathbb{C}$ and $\hat f$ for the two-dimensional Fourier transform of
$f : \mathbb{R}^2 \to \mathbb{C}$. For every Schwartz function
$\varphi : \mathbb{R}^2 \to \mathbb{C}$ and all $\theta, k \in \mathbb{R}$, the Fourier transform
of $p \mapsto R\varphi(p, \theta)$ at $k$ equals $\hat\varphi(k\cos\theta, k\sin\theta)$.
Moreover, there is a map $S$ sending functions $\mathbb{R}^2 \to \mathbb{C}$ to functions
$\mathbb{R}^2 \to \mathbb{C}$ such that $S(R\varphi) = \varphi$ for every Schwartz function
$\varphi$.

The second part says only that $R$ is injective on Schwartz functions; no formula, linearity or
continuity is asserted for the left inverse $S$.

Source: J. Radon (1917); R. N. Bracewell (Fourier slice theorem, 1956). Knill, *Some fundamental
theorems in mathematics*, §100. Via leanprover/lean-eval@38361be, problem
`radon_transform_inversion`. -/
public theorem radon_can_be_diagonalized_and_pseudo_inverted :
    (∀ φ : SchwartzMap (ℝ × ℝ) ℂ, ∀ θ k : ℝ,
        fourier1 (fun p => radon (φ : ℝ × ℝ → ℂ) (p, θ)) k =
          fourier2 (φ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ)) ∧
    (∃ Rinv : (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ),
        ∀ φ : SchwartzMap (ℝ × ℝ) ℂ,
          Rinv (radon (φ : ℝ × ℝ → ℂ)) = (φ : ℝ × ℝ → ℂ)) := by
  let R : SchwartzMap (ℝ × ℝ) ℂ → ℝ × ℝ → ℂ := fun φ => radon φ
  have hR : Function.Injective R := by
    intro φ ψ h
    apply fourier2_injective
    funext x
    change fourier2 φ x = fourier2 ψ x
    let z := measurableEquivRealProd.symm x
    have hx : (‖z‖ * Real.cos z.arg, ‖z‖ * Real.sin z.arg) = x := by
      simp [z, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
    rw [← hx, ← fourier_slice, ← fourier_slice, show radon φ = radon ψ from h]
  exact ⟨fourier_slice, fun g => (Function.invFun R g : SchwartzMap (ℝ × ℝ) ℂ),
    fun φ => congrArg (fun ψ : SchwartzMap (ℝ × ℝ) ℂ => (ψ : ℝ × ℝ → ℂ))
      (Function.leftInverse_invFun hR φ)⟩

end MathlibExt.Analysis.RadonTransformWanted.Analysis.RadonTransform
