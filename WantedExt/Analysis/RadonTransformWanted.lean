/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Radon transform: Fourier-slice diagonalization and pseudo-inversion

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.RadonTransform` — radon_transform_inversion (manifest `manifests/problems/radon_transform_inversion.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.RadonTransformWanted` namespace. Mathematical
statements are unchanged. Source: J. Radon (1917); R. N. Bracewell (Fourier slice theorem, 1956). Knill, *Some fundamental theorems in mathematics*, §100.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.RadonTransformWanted
namespace Analysis.RadonTransform

/-!
# The Radon transform: Fourier-slice diagonalization and pseudo-inversion

`radon_can_be_diagonalized_and_pseudo_inverted`: the Fourier slice theorem
(`fourier1` of `radon φ(·,θ)` equals a 2D-Fourier slice of `φ`), together with
the existence of a left inverse of the Radon transform on Schwartz functions.
The trusted helpers (`radon`, `fourier1`, `fourier2`) are non-holes. Mathlib
has the 1D/2D Fourier transforms and Schwartz space but no Radon transform,
Fourier slice theorem, or filtered back-projection.

Category-(b) candidate from §100 of the Knill survey.
-/

open MeasureTheory Real Complex

/-- **Radon transform on the plane.** For $f : \mathbb{R}^2 \to \mathbb{C}$ and
$p, \theta \in \mathbb{R}$, the Radon transform of $f$ at $(p, \theta)$ is the integral of $f$
along the line $x \cos\theta + y \sin\theta = p$ with respect to arc length,

$$Rf(p, \theta) = \int_{\mathbb{R}} f(p\cos\theta - t\sin\theta, p\sin\theta + t\cos\theta)\,dt,$$

where the integral is taken to be $0$ when the integrand is not integrable. -/
noncomputable def radon (f : ℝ × ℝ → ℂ) (pθ : ℝ × ℝ) : ℂ :=
  ∫ t : ℝ, f (pθ.1 * Real.cos pθ.2 - t * Real.sin pθ.2,
              pθ.1 * Real.sin pθ.2 + t * Real.cos pθ.2)

/-- **One-dimensional Fourier transform.** For $g : \mathbb{R} \to \mathbb{C}$ and
$k \in \mathbb{R}$, the Fourier transform of $g$ at $k$ is

$$\hat g(k) = \int_{\mathbb{R}} e^{-2\pi i p k} \, g(p) \, dp,$$

where the integral is taken to be $0$ when the integrand is not integrable. -/
noncomputable def fourier1 (g : ℝ → ℂ) (k : ℝ) : ℂ :=
  ∫ p : ℝ, Complex.exp (-(2 * Real.pi * p * k) * Complex.I) * g p

/-- **Two-dimensional Fourier transform.** For $f : \mathbb{R}^2 \to \mathbb{C}$ and
$k = (k_1, k_2) \in \mathbb{R}^2$, the Fourier transform of $f$ at $k$ is

$$\hat f(k) = \int_{\mathbb{R}^2} e^{-2\pi i (x_1 k_1 + x_2 k_2)} \, f(x) \, dx,$$

where $dx$ is Lebesgue measure on $\mathbb{R}^2$ and the integral is taken to be $0$ when the
integrand is not integrable. -/
noncomputable def fourier2 (f : ℝ × ℝ → ℂ) (k : ℝ × ℝ) : ℂ :=
  ∫ x : ℝ × ℝ,
    Complex.exp (-(2 * Real.pi * (x.1 * k.1 + x.2 * k.2)) * Complex.I) * f x

/- **Radon's theorem (diagonalization + pseudo-inversion).** The Fourier slice
theorem diagonalizes the Radon transform, and the transform admits a left
inverse on the Schwartz space. -/
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

Source: J. Radon (1917); R. N. Bracewell (Fourier slice theorem, 1956). Knill, *Some fundamental theorems in mathematics*, §100. Via leanprover/lean-eval@38361be, problem `radon_transform_inversion`. -/
public theorem_wanted radon_can_be_diagonalized_and_pseudo_inverted :
    (∀ φ : SchwartzMap (ℝ × ℝ) ℂ, ∀ θ k : ℝ,
        fourier1 (fun p => radon (φ : ℝ × ℝ → ℂ) (p, θ)) k =
          fourier2 (φ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ)) ∧
    (∃ Rinv : (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ),
        ∀ φ : SchwartzMap (ℝ × ℝ) ℂ,
          Rinv (radon (φ : ℝ × ℝ → ℂ)) = (φ : ℝ × ℝ → ℂ))

end Analysis.RadonTransform

end MathlibExt.Analysis.RadonTransformWanted
