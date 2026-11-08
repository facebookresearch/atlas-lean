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

/-- The **Radon transform** of `f : ℝ × ℝ → ℂ` at `(p, θ)`: the integral of `f`
along the line `x cos θ + y sin θ = p`. -/
noncomputable def radon (f : ℝ × ℝ → ℂ) (pθ : ℝ × ℝ) : ℂ :=
  ∫ t : ℝ, f (pθ.1 * Real.cos pθ.2 - t * Real.sin pθ.2,
              pθ.1 * Real.sin pθ.2 + t * Real.cos pθ.2)

/-- 1D Fourier transform (mathlib's `2π i` convention). -/
noncomputable def fourier1 (g : ℝ → ℂ) (k : ℝ) : ℂ :=
  ∫ p : ℝ, Complex.exp (-(2 * Real.pi * p * k) * Complex.I) * g p

/-- 2D Fourier transform of `f : ℝ × ℝ → ℂ` at `(k₁, k₂)`. -/
noncomputable def fourier2 (f : ℝ × ℝ → ℂ) (k : ℝ × ℝ) : ℂ :=
  ∫ x : ℝ × ℝ,
    Complex.exp (-(2 * Real.pi * (x.1 * k.1 + x.2 * k.2)) * Complex.I) * f x

/- **Radon's theorem (diagonalization + pseudo-inversion).** The Fourier slice
theorem diagonalizes the Radon transform, and the transform admits a left
inverse on the Schwartz space. -/
/-- Source: J. Radon (1917); R. N. Bracewell (Fourier slice theorem, 1956). Knill, *Some fundamental theorems in mathematics*, §100. Via leanprover/lean-eval@38361be, problem `radon_transform_inversion`. -/
public theorem_wanted radon_can_be_diagonalized_and_pseudo_inverted :
    (∀ φ : SchwartzMap (ℝ × ℝ) ℂ, ∀ θ k : ℝ,
        fourier1 (fun p => radon (φ : ℝ × ℝ → ℂ) (p, θ)) k =
          fourier2 (φ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ)) ∧
    (∃ Rinv : (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ),
        ∀ φ : SchwartzMap (ℝ × ℝ) ℂ,
          Rinv (radon (φ : ℝ × ℝ → ℂ)) = (φ : ℝ × ℝ → ℂ))

end Analysis.RadonTransform

end MathlibExt.Analysis.RadonTransformWanted
