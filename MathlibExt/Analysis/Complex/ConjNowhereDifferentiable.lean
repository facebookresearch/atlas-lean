/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_57.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029). The theorem statement and its description
are adapted from MA-ProofBench, by L. Pu et al. (arXiv:2606.13782).

Copyright (c) 2026 OpenBMB
Licensed under the MIT License.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Complex.Conformal

/-!
# Complex conjugation is nowhere complex-differentiable

The real derivative of conjugation is conjugation itself. It fixes `1` and sends `I` to `-I`,
violating the Cauchy–Riemann equation.
-/

public section

open Complex
open scoped ComplexConjugate

namespace MathlibExt.Analysis.Complex.ConjNowhereDifferentiableWanted

/-- **Complex conjugation is nowhere complex-differentiable.** Let $f : \mathbb{C} \to \mathbb{C}$
be the function $f(z) = \bar z$. Then $f$ is not complex-differentiable at any point
$z \in \mathbb{C}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_57.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem not_differentiableAt_conj (f : ℂ → ℂ) (hf : ∀ z : ℂ, f z = conj z) :
    ∀ z : ℂ, ¬ DifferentiableAt ℂ f z := by
  rw [funext hf]
  intro z h
  have hCR := (differentiableAt_complex_iff_differentiableAt_real.mp h).2
  have hderiv : fderiv ℝ conj z = (conjCLE : ℂ →L[ℝ] ℂ) := conjCLE.fderiv
  simp [hderiv, smul_eq_mul, CharZero.neg_eq_self_iff] at hCR

end MathlibExt.Analysis.Complex.ConjNowhereDifferentiableWanted
